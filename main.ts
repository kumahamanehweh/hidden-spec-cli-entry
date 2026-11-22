// mend: one patch tool for every AI edit format (SPEC.md version 1).
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A, JSON edits), applies its edits to the tree in the working directory
// with three tiers of line matching, and writes every change or none.
// Node 22, standard library only; run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below).

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const KNOWN_FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** An exit-2 answer: the whole run stops with one line on stdout. */
class PatchError {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit failed; the run reports it and keeps going with the next edit. */
class EditFailure {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const isBlank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at `\n`, one trailing `\r` removed, no empty piece after a final `\n`. */
function splitPatchLines(text: string): string[] {
  if (text === '') return [];
  const out = text.split('\n');
  if (text.endsWith('\n')) out.pop();
  return out.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** SPEC.md section 3: a path is safe when it is not empty, does not start with `/`, holds no `\`, and none of its `/`-separated segments is empty, `.` or `..`. */
function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** One line of an edit's old or new side; `ctx` marks a context line (present in both sides). */
interface SideLine {
  text: string;
  ctx: boolean;
}

/** A file's text as lines: its line break, its lines, and whether it ends with that break. */
interface FileText {
  eol: string;
  rows: string[];
  trailing: boolean;
}

function readFileText(text: string): FileText {
  if (text === '') return { eol: '\n', rows: [], trailing: false };
  const firstNl = text.indexOf('\n');
  const eol = firstNl > 0 && text[firstNl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(eol);
  let trailing = false;
  if (text.endsWith(eol)) {
    parts.pop();
    trailing = true;
  }
  return { eol, rows: parts, trailing };
}

function writeFileText(f: FileText): string {
  if (f.rows.length === 0) return '';
  return f.rows.join(f.eol) + (f.trailing ? f.eol : '');
}

/** Leading spaces and tabs of a line. */
function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

/** A line compared at one matching tier: tier 1 drops trailing spaces/tabs, tier 2 both ends. */
function tiered(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** All positions where `want` occurs in `rows` at the first tier with any occurrence, or null. */
function locateAll(rows: string[], want: string[], strict: boolean): { tier: number; at: number[] } | null {
  const top = strict ? 1 : 3;
  for (let tier = 0; tier < top; tier++) {
    const w = want.map((l) => tiered(l, tier));
    const at: number[] = [];
    for (let i = 0; i + want.length <= rows.length; i++) {
      let ok = true;
      for (let j = 0; j < want.length; j++) {
        if (tiered(rows[i + j]!, tier) !== w[j]) {
          ok = false;
          break;
        }
      }
      if (ok) at.push(i);
    }
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** Single-line match at the first tier with a line at or after `from`, or -1. */
function locateLine(rows: string[], want: string, from: number, strict: boolean): { tier: number; at: number } | null {
  const top = strict ? 1 : 3;
  for (let tier = 0; tier < top; tier++) {
    const w = tiered(want, tier);
    for (let i = from; i < rows.length; i++) {
      if (tiered(rows[i]!, tier) === w) return { tier, at: i };
    }
  }
  return null;
}

/**
 * The lines that replace `old` at position `at` in the file. A context line is
 * written as the file's own matched line; at tier 2 every other new line is
 * re-indented from the old side's first line to the file's first matched line.
 */
function replacementLines(rows: string[], at: number, old: SideLine[], next: SideLine[], tier: number): string[] {
  // Map each context line of `next` to its index in `old` (context lines run in the same order in both).
  const oldIndex = new Map<number, number>();
  {
    const seen: number[] = [];
    for (let k = 0; k < old.length; k++) if (old[k]!.ctx) seen.push(k);
    let ci = 0;
    for (let k = 0; k < next.length; k++) {
      if (next[k]!.ctx) {
        oldIndex.set(k, seen[ci]!);
        ci += 1;
      }
    }
  }
  const fileLead = leadingWs(rows[at] ?? '');
  const oldLead = old.length > 0 ? leadingWs(old[0]!.text) : '';
  const out: string[] = [];
  for (let k = 0; k < next.length; k++) {
    const line = next[k]!;
    if (line.ctx) {
      out.push(rows[at + oldIndex.get(k)!]!);
      continue;
    }
    if (tier === 2 && line.text !== '' && line.text.trim() !== '' && line.text.startsWith(oldLead)) {
      out.push(fileLead + line.text.slice(oldLead.length));
    } else {
      out.push(line.text);
    }
  }
  return out;
}

/** A move an edit made, for the `R` output line that replaces its `D` and `A` lines. */
interface Move {
  from: string;
  to: string;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly seen = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Move[] = [];
  original(p: string): string | null {
    if (!this.seen.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.seen.set(p, v);
    }
    return this.seen.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  /** The current text of a file that must exist, or an EditFailure naming why not. */
  need(p: string): string {
    if (!isSafePath(p)) throw new EditFailure('unsafe', p);
    const t = this.get(p);
    if (t === null) throw new EditFailure('missing', p);
    return t;
  }
  noteMove(from: string, to: string): void {
    this.moves.push({ from, to });
  }
}

type Edit = (tree: Tree) => void;

/** SPEC.md section 4: the first of these that holds, else null. */
function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!isSafePath(p)) throw new EditFailure('unsafe', p);
      if (tree.get(p) !== null) throw new EditFailure('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = tree.need(p);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const flat = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = flat(before);
      const old = flat(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new EditFailure('no-match', p);
      if (count > 1) throw new EditFailure('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + flat(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const lineNo = o.insert_line;
    const add = splitPatchLines(o.new_str);
    return (tree) => {
      const before = tree.need(p);
      const f = readFileText(before);
      if (lineNo < 0 || lineNo > f.rows.length) throw new EditFailure('no-match', p);
      f.rows.splice(lineNo, 0, ...add);
      tree.now.set(p, writeFileText(f));
    };
  }
  return null;
}

/** All edits of a JSON patch: one array, or one edit object a line. */
function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new PatchError('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new PatchError(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new PatchError(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new PatchError(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new PatchError(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- Unified diffs (SPEC.md section 6) ---- */

interface Hunk {
  start: number;
  old: SideLine[];
  next: SideLine[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noEolCtxPlus: boolean;
  /** A `\` line follows the hunk's last `+` line. */
  noEolPlus: boolean;
}

interface DiffSection {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}

/** A `--- ` or `+++ ` path: text after four characters, up to the first tab, trimmed; `/dev/null` means no file; a leading `a/` or `b/` is removed. */
function dashPath(l: string): string | null {
  const raw = l.slice(4).split('\t')[0]!.trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function parseUnified(lines: string[]): DiffSection[] {
  const sections: DiffSection[] = [];
  const n = lines.length;
  let i = 0;
  const hunkStart = (l: string): number | null => {
    const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
    return m === null ? null : parseInt(m[1]!, 10);
  };
  const gitPaths = (l: string): [string, string] | null => {
    const m = /^diff --git a\/(\S+) b\/(.+)$/.exec(l);
    return m === null ? null : [m[1]!, m[2]!.replace(/\s+$/, '')];
  };
  /** Read a hunk body starting at `at` (just past its header); returns the hunk and the next index. */
  const readHunk = (at: number, start: number): { hunk: Hunk; next: number } => {
    let j = at;
    const body: string[] = [];
    while (j < n) {
      const l = lines[j]!;
      if (l.startsWith('diff --git ')) break;
      if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
      if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
        body.push(l);
        j++;
      } else break;
    }
    while (body.length > 0 && body[body.length - 1] === '') body.pop();
    let lastCp = -1;
    let lastPlus = -1;
    for (let k = 0; k < body.length; k++) {
      const b = body[k]!;
      if (b.startsWith(' ') || b === '' || b.startsWith('+')) lastCp = k;
      if (b.startsWith('+')) lastPlus = k;
    }
    const follows = (k: number): boolean => k >= 0 && body[k + 1] !== undefined && body[k + 1]!.startsWith('\\');
    const old: SideLine[] = [];
    const next: SideLine[] = [];
    for (const b of body) {
      if (b.startsWith('\\')) continue;
      if (b.startsWith(' ')) {
        const t = b.slice(1);
        old.push({ text: t, ctx: true });
        next.push({ text: t, ctx: true });
      } else if (b === '') {
        old.push({ text: '', ctx: true });
        next.push({ text: '', ctx: true });
      } else if (b.startsWith('-')) old.push({ text: b.slice(1), ctx: false });
      else if (b.startsWith('+')) next.push({ text: b.slice(1), ctx: false });
    }
    return { hunk: { start, old, next, noEolCtxPlus: follows(lastCp), noEolPlus: follows(lastPlus) }, next: j };
  };

  type State = 'top' | 'head' | 'after';
  let state: State = 'top';
  let cur: DiffSection | null = null;
  let pairOld: string | null = null;
  let pairNew: string | null = null;
  let hasPair = false;
  let renOld: string | null = null;
  let renNew: string | null = null;
  let gitOld: string | null = null;
  let gitNew: string | null = null;
  const finishSection = (): void => {
    if (cur === null) return;
    cur.oldPath = pairOld ?? renOld ?? gitOld;
    cur.newPath = pairNew ?? renNew ?? gitNew;
    sections.push(cur);
    cur = null;
    pairOld = pairNew = renOld = renNew = gitOld = gitNew = null;
    hasPair = false;
  };
  const beginSection = (): void => {
    cur = { oldPath: null, newPath: null, create: false, remove: false, hunks: [] };
    state = 'head';
  };

  while (i < n) {
    const line = lines[i]!;
    if (state === 'top') {
      if (line.startsWith('diff --git ')) {
        const g = gitPaths(line);
        if (g === null) throw new PatchError(`error: parse ${i + 1}`);
        gitOld = g[0];
        gitNew = g[1];
        beginSection();
        i++;
      } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        pairOld = dashPath(line);
        pairNew = dashPath(lines[i + 1]!);
        hasPair = true;
        beginSection();
        i += 2;
      } else if (line.startsWith('@@')) {
        throw new PatchError(`error: parse ${i + 1}`);
      } else {
        i++;
      }
      continue;
    }
    if (state === 'head') {
      if (line.startsWith('@@')) {
        const s = hunkStart(line);
        if (s === null) throw new PatchError(`error: parse ${i + 1}`);
        const r = readHunk(i + 1, s);
        cur!.hunks.push(r.hunk);
        i = r.next;
        state = 'after';
      } else if (line.startsWith('diff --git ')) {
        finishSection();
        state = 'top';
      } else if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          if (!hasPair) {
            pairOld = dashPath(line);
            pairNew = dashPath(lines[i + 1]!);
            hasPair = true;
            i += 2;
          } else {
            finishSection();
            state = 'top';
          }
        } else {
          throw new PatchError(`error: parse ${i + 2}`);
        }
      } else if (line.startsWith('rename from ')) {
        renOld = line.slice(12).trim();
        i++;
      } else if (line.startsWith('rename to ')) {
        renNew = line.slice(10).trim();
        i++;
      } else if (line.startsWith('new file mode')) {
        cur!.create = true;
        i++;
      } else if (line.startsWith('deleted file mode')) {
        cur!.remove = true;
        i++;
      } else {
        i++;
      }
      continue;
    }
    // state === 'after'
    if (line.startsWith('@@')) {
      const s = hunkStart(line);
      if (s === null) throw new PatchError(`error: parse ${i + 1}`);
      const r = readHunk(i + 1, s);
      cur!.hunks.push(r.hunk);
      i = r.next;
    } else if (line.startsWith('diff --git ')) {
      finishSection();
      state = 'top';
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      finishSection();
      state = 'top';
    } else {
      i++;
    }
  }
  finishSection();
  return sections;
}

/** Apply one section's hunks to a file's lines, in order, tracking the length drift `d`. */
function applyHunks(f: FileText, hunks: Hunk[], strict: boolean, failPath: string): void {
  let d = 0;
  for (const h of hunks) {
    if (h.old.length === 0) {
      let at = h.start + d;
      if (at < 0) at = 0;
      if (at > f.rows.length) at = f.rows.length;
      const atEnd = at === f.rows.length;
      const ins = h.next.map((l) => l.text);
      f.rows.splice(at, 0, ...ins);
      d += h.next.length;
      if (atEnd) f.trailing = !h.noEolCtxPlus;
      continue;
    }
    const oTexts = h.old.map((l) => l.text);
    const found = locateAll(f.rows, oTexts, strict);
    if (found === null) throw new EditFailure('no-match', failPath);
    const target = h.start - 1 + d;
    let best = found.at[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of found.at) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const touchesEnd = best + h.old.length === f.rows.length;
    const rep = replacementLines(f.rows, best, h.old, h.next, found.tier);
    f.rows.splice(best, h.old.length, ...rep);
    d += h.next.length - h.old.length;
    if (touchesEnd) f.trailing = !h.noEolCtxPlus;
  }
}

function unifiedEdits(sections: DiffSection[], strict: boolean): Edit[] {
  return sections.map((sec) => (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if (oldP !== null && !isSafePath(oldP)) throw new EditFailure('unsafe', oldP);
    if (newP !== null && !isSafePath(newP)) throw new EditFailure('unsafe', newP);
    const isCreate = oldP === null || sec.create;
    const isDelete = newP === null || sec.remove;
    if (isCreate) {
      if (newP === null) return;
      if (tree.get(newP) !== null) throw new EditFailure('exists', newP);
      const plus: string[] = [];
      let noEol = false;
      for (const h of sec.hunks) {
        let hasPlus = false;
        for (const l of h.next) {
          if (!l.ctx) {
            plus.push(l.text);
            hasPlus = true;
          }
        }
        if (hasPlus) noEol = h.noEolPlus;
      }
      tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
      return;
    }
    if (isDelete) {
      if (oldP === null) return;
      if (tree.get(oldP) === null) throw new EditFailure('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP !== newP) {
      const before = tree.get(oldP!);
      if (before === null) throw new EditFailure('missing', oldP!);
      if (tree.get(newP!) !== null) throw new EditFailure('exists', newP!);
      const f = readFileText(before);
      applyHunks(f, sec.hunks, strict, oldP!);
      tree.now.set(oldP!, null);
      tree.now.set(newP!, writeFileText(f));
      tree.noteMove(oldP!, newP!);
      return;
    }
    const before = tree.get(oldP!);
    if (before === null) throw new EditFailure('missing', oldP!);
    const f = readFileText(before);
    applyHunks(f, sec.hunks, strict, oldP!);
    tree.now.set(oldP!, writeFileText(f));
  });
}

/* ---- SEARCH/REPLACE blocks (SPEC.md section 7) ---- */

interface SearchBlock {
  path: string;
  old: string[];
  next: string[];
}

function parseSearchReplace(lines: string[]): SearchBlock[] {
  const blocks: SearchBlock[] = [];
  const n = lines.length;
  let prevEnd = -1;
  let prevPath: string | null = null;
  const isSearch = (l: string): boolean => l.trimEnd() === '<<<<<<< SEARCH';
  const isSep = (l: string): boolean => l.trimEnd() === '=======';
  const isEnd = (l: string): boolean => l.trimEnd() === '>>>>>>> REPLACE';
  for (let s = 0; s < n; s++) {
    if (!isSearch(lines[s]!)) continue;
    // The path: the nearest line before SEARCH, after the previous block's end,
    // that is not blank and does not start with three backticks once trimmed.
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new PatchError(`error: parse ${s + 1}`);
      path = prevPath;
    }
    let k = s + 1;
    let sep = -1;
    while (k < n) {
      if (isSep(lines[k]!)) {
        sep = k;
        break;
      }
      if (isSearch(lines[k]!) || isEnd(lines[k]!)) throw new PatchError(`error: parse ${s + 1}`);
      k++;
    }
    if (sep < 0) throw new PatchError(`error: parse ${s + 1}`);
    let r = sep + 1;
    let end = -1;
    while (r < n) {
      if (isEnd(lines[r]!)) {
        end = r;
        break;
      }
      if (isSearch(lines[r]!)) throw new PatchError(`error: parse ${s + 1}`);
      r++;
    }
    if (end < 0) throw new PatchError(`error: parse ${s + 1}`);
    blocks.push({ path, old: lines.slice(s + 1, sep), next: lines.slice(sep + 1, end) });
    prevEnd = end;
    prevPath = path;
    s = end;
  }
  return blocks;
}

function searchReplaceEdits(blocks: SearchBlock[], strict: boolean): Edit[] {
  return blocks.map((b) => (tree) => {
    if (!isSafePath(b.path)) throw new EditFailure('unsafe', b.path);
    if (b.old.length === 0) {
      if (tree.get(b.path) !== null) throw new EditFailure('exists', b.path);
      tree.now.set(b.path, b.next.length === 0 ? '' : b.next.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new EditFailure('missing', b.path);
    const f = readFileText(before);
    const found = locateAll(f.rows, b.old, strict);
    if (found === null) throw new EditFailure('no-match', b.path);
    if (found.at.length > 1) throw new EditFailure('ambiguous', b.path);
    const at = found.at[0]!;
    const oldSide: SideLine[] = b.old.map((t) => ({ text: t, ctx: false }));
    const newSide: SideLine[] = b.next.map((t) => ({ text: t, ctx: false }));
    const rep = replacementLines(f.rows, at, oldSide, newSide, found.tier);
    f.rows.splice(at, b.old.length, ...rep);
    tree.now.set(b.path, writeFileText(f));
  });
}

/* ---- V4A patches (SPEC.md section 8) ---- */

interface V4aChunk {
  anchor: string | null;
  old: SideLine[];
  next: SideLine[];
  eof: boolean;
}

interface V4aSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: V4aChunk[];
}

function parseV4a(lines: string[]): V4aSection[] {
  const n = lines.length;
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new PatchError('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new PatchError(`error: parse ${first + 1}`);
  let last = n - 1;
  while (last >= 0 && isBlank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new PatchError(`error: parse ${n + 1}`);
  const sections: V4aSection[] = [];
  const isStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (isBlank(line)) {
      i++;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice(14).trim();
      let j = i + 1;
      while (j < last && !isStart(lines[j]!)) j++;
      const raw = lines.slice(i + 1, j);
      while (raw.length > 0 && isBlank(raw[raw.length - 1]!)) raw.pop();
      const ls: string[] = [];
      for (let k = 0; k < raw.length; k++) {
        const l = raw[k]!;
        if (l.startsWith('+')) ls.push(l.slice(1));
        else if (l === '') ls.push('');
        else throw new PatchError(`error: parse ${i + 1 + k + 1}`);
      }
      sections.push({ kind: 'add', path, moveTo: null, lines: ls, chunks: [] });
      i = j;
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice(17).trim();
      let j = i + 1;
      while (j < last && !isStart(lines[j]!)) {
        if (!isBlank(lines[j]!)) throw new PatchError(`error: parse ${j + 1}`);
        j++;
      }
      sections.push({ kind: 'delete', path, moveTo: null, lines: [], chunks: [] });
      i = j;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice(17).trim();
      let j = i + 1;
      let moveTo: string | null = null;
      if (j < last && lines[j]!.startsWith('*** Move to: ')) {
        moveTo = lines[j]!.slice(13).trim();
        j++;
      }
      // The section's lines run to the next section start or End Patch; trailing blank lines are not part of it.
      let end = j;
      while (end < last && !isStart(lines[end]!)) end++;
      const raw = lines.slice(j, end);
      while (raw.length > 0 && isBlank(raw[raw.length - 1]!)) raw.pop();
      const chunks: V4aChunk[] = [];
      let cur: V4aChunk | null = null;
      let open = false;
      const startChunk = (anchor: string | null): void => {
        cur = { anchor, old: [], next: [], eof: false };
        chunks.push(cur);
        open = true;
      };
      for (let k = 0; k < raw.length; k++) {
        const l = raw[k]!;
        const no = j + k + 1;
        if (l === '*** End of File') {
          if (!open || cur === null) throw new PatchError(`error: parse ${no}`);
          cur.eof = true;
          open = false;
          cur = null;
        } else if (l.startsWith('@@')) {
          const a = l.slice(2).trim();
          startChunk(a === '' ? null : a);
        } else if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l === '') {
          if (!open) {
            if (chunks.length > 0) throw new PatchError(`error: parse ${no}`);
            startChunk(null);
          }
          const c = cur!;
          if (l.startsWith(' ')) {
            const t = l.slice(1);
            c.old.push({ text: t, ctx: true });
            c.next.push({ text: t, ctx: true });
          } else if (l === '') {
            c.old.push({ text: '', ctx: true });
            c.next.push({ text: '', ctx: true });
          } else if (l.startsWith('-')) c.old.push({ text: l.slice(1), ctx: false });
          else c.next.push({ text: l.slice(1), ctx: false });
        } else {
          throw new PatchError(`error: parse ${no}`);
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new PatchError(`error: parse ${i + 1}`);
      sections.push({ kind: 'update', path, moveTo, lines: [], chunks });
      i = end;
      continue;
    }
    throw new PatchError(`error: parse ${i + 1}`);
  }
  return sections;
}

/** Apply one Update section's chunks, tracking the cursor that starts at line 0. */
function applyV4aChunks(f: FileText, chunks: V4aChunk[], strict: boolean, failPath: string): void {
  let cursor = 0;
  for (const c of chunks) {
    if (c.anchor !== null) {
      const found = locateLine(f.rows, c.anchor, cursor, strict);
      if (found === null) throw new EditFailure('no-match', failPath);
      cursor = found.at + 1;
    }
    const oTexts = c.old.map((l) => l.text);
    if (c.old.length === 0) {
      const at = c.eof ? f.rows.length : cursor;
      const ins = c.next.map((l) => l.text);
      f.rows.splice(at, 0, ...ins);
      cursor = at + ins.length;
      continue;
    }
    let chosen: { tier: number; at: number } | null = null;
    const top = strict ? 1 : 3;
    for (let tier = 0; tier < top && chosen === null; tier++) {
      const w = oTexts.map((l) => tiered(l, tier));
      for (let p = cursor; p + oTexts.length <= f.rows.length; p++) {
        if (c.eof && p + oTexts.length !== f.rows.length) continue;
        let ok = true;
        for (let k = 0; k < oTexts.length; k++) {
          if (tiered(f.rows[p + k]!, tier) !== w[k]) {
            ok = false;
            break;
          }
        }
        if (ok) {
          chosen = { tier, at: p };
          break;
        }
      }
    }
    if (chosen === null) throw new EditFailure('no-match', failPath);
    const rep = replacementLines(f.rows, chosen.at, c.old, c.next, chosen.tier);
    f.rows.splice(chosen.at, c.old.length, ...rep);
    cursor = chosen.at + rep.length;
  }
}

function v4aEdits(sections: V4aSection[], strict: boolean): Edit[] {
  return sections.map((sec) => (tree) => {
    if (!isSafePath(sec.path)) throw new EditFailure('unsafe', sec.path);
    if (sec.kind === 'add') {
      if (tree.get(sec.path) !== null) throw new EditFailure('exists', sec.path);
      tree.now.set(sec.path, sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (tree.get(sec.path) === null) throw new EditFailure('missing', sec.path);
      tree.now.set(sec.path, null);
      return;
    }
    const before = tree.get(sec.path);
    if (before === null) throw new EditFailure('missing', sec.path);
    if (sec.moveTo !== null) {
      if (!isSafePath(sec.moveTo)) throw new EditFailure('unsafe', sec.moveTo);
      if (tree.get(sec.moveTo) !== null) throw new EditFailure('exists', sec.moveTo);
    }
    const f = readFileText(before);
    applyV4aChunks(f, sec.chunks, strict, sec.path);
    const out = writeFileText(f);
    if (sec.moveTo !== null) {
      tree.now.set(sec.path, null);
      tree.now.set(sec.moveTo, out);
      tree.noteMove(sec.path, sec.moveTo);
    } else {
      tree.now.set(sec.path, out);
    }
  });
}

/* ---- The command line (SPEC.md sections 1, 2 and 10) ---- */

function run(argv: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let checkOnly = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of argv) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && KNOWN_FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !checkOnly) checkOnly = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = splitPatchLines(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(parseUnified(lines), strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(parseSearchReplace(lines), strict);
    else edits = v4aEdits(parseV4a(lines), strict);
    if (edits.length === 0) throw new PatchError('error: parse 1');
  } catch (e) {
    if (e instanceof PatchError) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: EditFailure[] = [];
  for (const edit of edits) {
    const savedNow = new Map(tree.now);
    const savedMoves = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFailure)) throw e;
      tree.now.clear();
      for (const [k, v] of savedNow) tree.now.set(k, v);
      tree.moves.length = savedMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  // The change rows: a move's `R` line replaces its `D` and `A` pair and sorts by the new path.
  interface Row {
    key: string;
    line: string;
  }
  const rows: Row[] = [];
  const movedFrom = new Set<string>();
  const movedTo = new Set<string>();
  for (const m of tree.moves) {
    const wasOld = tree.original(m.from);
    const nowOld = tree.get(m.from);
    const wasNew = tree.original(m.to);
    const nowNew = tree.get(m.to);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: m.to, line: `R ${m.from} -> ${m.to}` });
      movedFrom.add(m.from);
      movedTo.add(m.to);
    }
  }
  for (const p of tree.now.keys()) {
    if (movedFrom.has(p) || movedTo.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`];
  if (!checkOnly) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
