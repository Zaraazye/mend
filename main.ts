// main.ts is mend, the CLI SPEC.md specifies. The kit starter did sections 1 to 4, 9 and 10
// (command line, output and exit codes, safe paths, format detection, JSON edits and the
// all-or-nothing write). This file adds sections 5 to 8: matching lines at three tiers,
// unified diffs, SEARCH/REPLACE blocks and V4A patches, plus the R (move) output line that
// sections 6 and 8 need. Node 22, the standard library alone; run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands
// over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---------- Section 3: a file as lines, its break and its final break ----------

interface FileView {
  lines: string[];
  br: string;
  final: boolean;
}

function splitText(text: string): FileView {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { lines: parts, br, final: fin };
}

function joinText(v: FileView): string {
  if (v.lines.length === 0) return '';
  return v.lines.join(v.br) + (v.final ? v.br : '');
}

function leadingWS(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

// ---------- Section 5: matching lines at three tiers ----------

/** The comparison key of one line at a tier: 0 exact, 1 trailing ws stripped, 2 both ends stripped. */
function tierKey(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** All 0-based positions where O occurs in fileLines at tier, at or after `from`. */
function occurrencesAt(fileLines: string[], O: string[], tier: number, from = 0): number[] {
  const occ: number[] = [];
  const n = O.length;
  if (n === 0) return occ;
  const keys = O.map((l) => tierKey(l, tier));
  for (let i = from; i + n <= fileLines.length; i++) {
    let ok = true;
    for (let j = 0; j < n; j++) {
      if (tierKey(fileLines[i + j]!, tier) !== keys[j]) {
        ok = false;
        break;
      }
    }
    if (ok) occ.push(i);
  }
  return occ;
}

/** The first tier (0, then 1, then 2; only 0 when strict) at which O occurs, with its positions. */
function findTier(fileLines: string[], O: string[], strict: boolean, from = 0): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(fileLines, O, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/**
 * Replace fileLines[pos .. pos+O.length-1] by N. ctx[j] is the O index of N[j] when N[j] is a
 * context line (written as the file's own matched line), else -1. At tier 2 every other N line
 * is re-indented from O's first line's leading whitespace to the file's.
 */
function applyMatch(fileLines: string[], pos: number, O: string[], N: string[], ctx: number[], tier: number): string[] {
  const out: string[] = [];
  let f = '';
  let p = '';
  if (tier === 2 && O.length > 0) {
    f = leadingWS(fileLines[pos]!);
    p = leadingWS(O[0]!);
  }
  for (let j = 0; j < N.length; j++) {
    if (ctx[j]! >= 0) {
      out.push(fileLines[pos + ctx[j]!]!);
    } else {
      let line = N[j]!;
      if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(p)) {
        line = f + line.slice(p.length);
      }
      out.push(line);
    }
  }
  return [...fileLines.slice(0, pos), ...out, ...fileLines.slice(pos + O.length)];
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<{ old: string; nw: string }> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  /** Record a move: old path deleted, new path written, remembered for the R output line. */
  move(oldP: string, newP: string, content: string): void {
    this.now.set(oldP, null);
    this.now.set(newP, content);
    this.moves.push({ old: oldP, nw: newP });
  }
}

type Edit = (tree: Tree) => void;

/** Check every named path for safety first; throw Fail('unsafe', path) for the first bad one. */
function checkSafe(paths: string[]): void {
  for (const p of paths) {
    if (!safe(p)) throw new Fail('unsafe', p);
  }
}

/** Replace the lines of a file's current text with `replacement` lines, keeping its break and final flag. */
function replaceFileText(tree: Tree, p: string, view: FileView): void {
  tree.now.set(p, joinText(view));
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
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
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const fin = before !== '' && before.endsWith(br);
      if (fin) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (fin ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------- Section 6: unified diffs ----------

interface Hunk {
  a: number;
  body: string[];
}

/** O, N and the context map of one hunk body, plus whether a \ line follows its last context/+ line. */
function hunkParts(body: string[]): { o: string[]; n: string[]; ctx: number[]; noBreak: boolean } {
  const o: string[] = [];
  const n: string[] = [];
  const ctx: number[] = [];
  let lastNew = -1;
  for (let k = 0; k < body.length; k++) {
    const b = body[k]!;
    if (b.startsWith(' ') || b.startsWith('+')) lastNew = k;
  }
  const noBreak = lastNew >= 0 && lastNew + 1 < body.length && body[lastNew + 1]!.startsWith('\\');
  let oi = 0;
  let ni = 0;
  for (const b of body) {
    if (b.startsWith('\\')) continue;
    if (b.startsWith(' ')) {
      const t = b.slice(1);
      o.push(t);
      n.push(t);
      ctx[ni] = oi;
      oi += 1;
      ni += 1;
    } else if (b.startsWith('-')) {
      o.push(b.slice(1));
      oi += 1;
    } else if (b.startsWith('+')) {
      n.push(b.slice(1));
      ctx[ni] = -1;
      ni += 1;
    } else if (b === '') {
      o.push('');
      n.push('');
      ctx[ni] = oi;
      oi += 1;
      ni += 1;
    }
  }
  return { o, n, ctx, noBreak };
}

function cleanUnifiedPath(raw: string): string {
  const p = raw.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) return p.slice(2);
  return p;
}

/** The path after `--- ` or `+++ ` (text up to the first tab, surrounding spaces removed). */
function headerPath(line: string): string {
  const rest = line.slice(4);
  const tab = rest.indexOf('\t');
  return cleanUnifiedPath(tab >= 0 ? rest.slice(0, tab) : rest);
}

interface UniSection {
  oldPath: string | null;
  newPath: string | null;
  pairOld: string | null;
  pairNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  isNew: boolean;
  isDeleted: boolean;
  hunks: Hunk[];
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let i = 0;
  const gitRe = /^diff --git a\/(\S+) b\/(\S+)$/;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = gitRe.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const sec: UniSection = { oldPath: null, newPath: null, pairOld: null, pairNew: null, renameFrom: null, renameTo: null, isNew: false, isDeleted: false, hunks: [] };
      const gitOld = m[1]!;
      const gitNew = m[2]!;
      sections.push(sec);
      i += 1;
      i = parseUniHeader(lines, i, sec);
      // precedence: ---/+++ pair first, then rename from/to, then the diff --git paths
      sec.oldPath = sec.pairOld ?? sec.renameFrom ?? gitOld;
      sec.newPath = sec.pairNew ?? sec.renameTo ?? gitNew;
      i = parseUniHunks(lines, i, sec);
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const sec: UniSection = { oldPath: null, newPath: null, pairOld: null, pairNew: null, renameFrom: null, renameTo: null, isNew: false, isDeleted: false, hunks: [] };
      sections.push(sec);
      i = parseUniHeader(lines, i, sec);
      sec.oldPath = sec.pairOld ?? sec.renameFrom;
      sec.newPath = sec.pairNew ?? sec.renameTo;
      i = parseUniHunks(lines, i, sec);
    } else if (line.startsWith('@@')) {
      throw new Exit2(`error: parse ${i + 1}`);
    } else {
      i += 1;
    }
  }
  return sections;
}

/** Parse a section header (up to the first hunk or the next section); returns the next index. */
function parseUniHeader(lines: string[], i: number, sec: UniSection): number {
  let sawPair = false;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('@@')) break;
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (!sawPair) {
        sec.pairOld = headerPath(line);
        sec.pairNew = headerPath(lines[i + 1]!);
        sawPair = true;
        i += 2;
        continue;
      }
      break;
    }
    if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
    if (line.startsWith('rename from ')) sec.renameFrom = cleanUnifiedPath(line.slice('rename from '.length));
    else if (line.startsWith('rename to ')) sec.renameTo = cleanUnifiedPath(line.slice('rename to '.length));
    else if (line === 'new file mode' || line.startsWith('new file mode ')) sec.isNew = true;
    else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) sec.isDeleted = true;
    i += 1;
  }
  return i;
}

/** Parse a section's hunks; returns the next index (next section or end of patch). */
function parseUniHunks(lines: string[], i: number, sec: UniSection): number {
  const hunkRe = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (line.startsWith('@@')) {
      const m = hunkRe.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: parseInt(m[1]!, 10), body: [] };
      sec.hunks.push(hunk);
      i += 1;
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\') || b === '') {
          hunk.body.push(b);
          i += 1;
        } else break;
      }
      while (hunk.body.length > 0 && hunk.body[hunk.body.length - 1] === '') hunk.body.pop();
    } else {
      i += 1;
    }
  }
  return i;
}

/** Apply one hunk to a file view; returns the new view and the new offset d. */
function applyUniHunk(view: FileView, hunk: Hunk, d: number, strict: boolean, path: string): { view: FileView; d: number } {
  const { o, n, ctx, noBreak } = hunkParts(hunk.body);
  if (o.length === 0) {
    const pos = Math.max(0, Math.min(hunk.a + d, view.lines.length));
    const lines = [...view.lines.slice(0, pos), ...n, ...view.lines.slice(pos)];
    const atEnd = pos === view.lines.length;
    return { view: { lines, br: view.br, final: atEnd ? !noBreak : view.final }, d: d + (n.length - o.length) };
  }
  const found = findTier(view.lines, o, strict);
  if (found === null) throw new Fail('no-match', path);
  const target = hunk.a - 1 + d;
  let best = found.occ[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.occ) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const lines = applyMatch(view.lines, best, o, n, ctx, found.tier);
  const runsToEnd = best + o.length === view.lines.length;
  return { view: { lines, br: view.br, final: runsToEnd ? !noBreak : view.final }, d: d + (n.length - o.length) };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseUnified(lines);
  return sections.map((sec) => {
    return (tree: Tree) => {
      const oldP = sec.oldPath;
      const newP = sec.newPath;
      const oldIsNull = oldP === '/dev/null';
      const newIsNull = newP === '/dev/null';
      const isCreate = oldIsNull || sec.isNew;
      const isDelete = !isCreate && (newIsNull || sec.isDeleted);
      const paths: string[] = [];
      if (oldP !== null && !oldIsNull) paths.push(oldP);
      if (newP !== null && !newIsNull) paths.push(newP);
      checkSafe(paths);
      if (isCreate) {
        const target = newP!;
        if (tree.get(target) !== null) throw new Fail('exists', target);
        const created: string[] = [];
        for (const h of sec.hunks) {
          for (const b of h.body) {
            if (b.startsWith('+')) created.push(b.slice(1));
          }
        }
        // a created file ends with a line break unless a \ line follows its last + line
        let noBreak = false;
        outer: for (let hi = sec.hunks.length - 1; hi >= 0; hi--) {
          const body = sec.hunks[hi]!.body;
          for (let k = body.length - 1; k >= 0; k--) {
            if (body[k]!.startsWith('+')) {
              noBreak = k + 1 < body.length && body[k + 1]!.startsWith('\\');
              break outer;
            }
          }
        }
        tree.now.set(target, created.length === 0 ? '' : created.join('\n') + (noBreak ? '' : '\n'));
        return;
      }
      if (isDelete) {
        const target = oldP!;
        if (tree.get(target) === null) throw new Fail('missing', target);
        tree.now.set(target, null);
        return;
      }
      const isMove = oldP !== null && newP !== null && oldP !== newP;
      if (isMove) {
        const from = oldP!;
        const to = newP!;
        const cur = tree.get(from);
        if (cur === null) throw new Fail('missing', from);
        if (tree.get(to) !== null) throw new Fail('exists', to);
        let view = splitText(cur);
        let d = 0;
        for (const h of sec.hunks) {
          const r = applyUniHunk(view, h, d, strict, from);
          view = r.view;
          d = r.d;
        }
        tree.move(from, to, joinText(view));
        return;
      }
      const target = (oldP ?? newP)!;
      const cur = tree.get(target);
      if (cur === null) throw new Fail('missing', target);
      let view = splitText(cur);
      let d = 0;
      for (const h of sec.hunks) {
        const r = applyUniHunk(view, h, d, strict, target);
        view = r.view;
        d = r.d;
      }
      replaceFileText(tree, target, view);
    };
  });
}

// ---------- Section 7: SEARCH/REPLACE blocks ----------

interface SrBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
  searchLine: number;
}

function parseSearchReplace(lines: string[]): SrBlock[] {
  const blocks: SrBlock[] = [];
  let i = 0;
  let prevEnd = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let k = searchIdx - 1; k >= prevEnd; k--) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (blocks.length === 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = blocks[blocks.length - 1]!.path;
    }
    let sep = -1;
    for (let k = searchIdx + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '=======') {
        sep = k;
        break;
      }
    }
    let end = -1;
    if (sep >= 0) {
      for (let k = sep + 1; k < lines.length; k++) {
        if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
          end = k;
          break;
        }
      }
    }
    if (sep < 0 || end < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    blocks.push({
      path,
      oldLines: lines.slice(searchIdx + 1, sep),
      newLines: lines.slice(sep + 1, end),
      searchLine: searchIdx + 1,
    });
    prevEnd = end + 1;
    i = end + 1;
  }
  return blocks;
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const blocks = parseSearchReplace(lines);
  return blocks.map((b) => {
    return (tree: Tree) => {
      checkSafe([b.path]);
      if (b.oldLines.length === 0) {
        if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
        tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
        return;
      }
      const cur = tree.get(b.path);
      if (cur === null) throw new Fail('missing', b.path);
      const view = splitText(cur);
      const found = findTier(view.lines, b.oldLines, strict);
      if (found === null) throw new Fail('no-match', b.path);
      if (found.occ.length !== 1) throw new Fail('ambiguous', b.path);
      const ctx = b.newLines.map(() => -1);
      const lines = applyMatch(view.lines, found.occ[0]!, b.oldLines, b.newLines, ctx, found.tier);
      replaceFileText(tree, b.path, { lines, br: view.br, final: view.final });
    };
  });
}

// ---------- Section 8: V4A patches ----------

interface V4Chunk {
  anchor: string | null;
  body: string[];
  eof: boolean;
}

interface V4Section {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: V4Chunk[];
  headerLine: number;
}

function parseV4a(lines: string[]): V4Section[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4Section[] = [];
  let i = first + 1;
  const startRe = /^\*\*\* (Add File|Delete File|Update File): /;
  while (i < last) {
    if (blank(lines[i]!)) {
      i += 1;
      continue;
    }
    const m = startRe.exec(lines[i]!);
    if (!m) throw new Exit2(`error: parse ${i + 1}`);
    const kind = m[1] === 'Add File' ? 'add' : m[1] === 'Delete File' ? 'delete' : 'update';
    const path = lines[i]!.slice(m[0].length).trim();
    const headerLine = i + 1;
    i += 1;
    const bodyStart = i;
    while (i < last && !startRe.test(lines[i]!)) i += 1;
    let body = lines.slice(bodyStart, i);
    while (body.length > 0 && blank(body[body.length - 1]!)) body.pop();
    const sec: V4Section = { kind, path, moveTo: null, lines: [], chunks: [], headerLine };
    if (kind === 'add') {
      for (let k = 0; k < body.length; k++) {
        const b = body[k]!;
        if (b.startsWith('+')) sec.lines.push(b.slice(1));
        else if (b === '') sec.lines.push('');
        else throw new Exit2(`error: parse ${bodyStart + k + 1}`);
      }
    } else if (kind === 'delete') {
      for (let k = 0; k < body.length; k++) {
        if (!blank(body[k]!)) throw new Exit2(`error: parse ${bodyStart + k + 1}`);
      }
    } else {
      let rest = body;
      let restStart = bodyStart;
      if (rest.length > 0 && rest[0]!.startsWith('*** Move to: ')) {
        sec.moveTo = rest[0]!.slice('*** Move to: '.length).trim();
        rest = rest.slice(1);
        restStart += 1;
      }
      const chunks: V4Chunk[] = [];
      let cur: V4Chunk | null = null;
      for (let k = 0; k < rest.length; k++) {
        const b = rest[k]!;
        if (b.startsWith('@@')) {
          if (cur !== null) chunks.push(cur);
          const anchor = b.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, body: [], eof: false };
        } else if (b.trim() === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${restStart + k + 1}`);
          cur.eof = true;
          chunks.push(cur);
          cur = null;
        } else if (b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b === '') {
          if (cur === null) {
            if (chunks.length > 0) throw new Exit2(`error: parse ${restStart + k + 1}`);
            cur = { anchor: null, body: [], eof: false };
          }
          cur.body.push(b);
        } else {
          throw new Exit2(`error: parse ${restStart + k + 1}`);
        }
      }
      if (cur !== null) chunks.push(cur);
      sec.chunks = chunks;
      if (chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${headerLine}`);
    }
    sections.push(sec);
  }
  return sections;
}

/** O, N and context map of one V4A chunk body. */
function chunkParts(body: string[]): { o: string[]; n: string[]; ctx: number[] } {
  const o: string[] = [];
  const n: string[] = [];
  const ctx: number[] = [];
  let oi = 0;
  let ni = 0;
  for (const b of body) {
    if (b.startsWith(' ')) {
      const t = b.slice(1);
      o.push(t);
      n.push(t);
      ctx[ni] = oi;
      oi += 1;
      ni += 1;
    } else if (b.startsWith('-')) {
      o.push(b.slice(1));
      oi += 1;
    } else if (b.startsWith('+')) {
      n.push(b.slice(1));
      ctx[ni] = -1;
      ni += 1;
    } else if (b === '') {
      o.push('');
      n.push('');
      ctx[ni] = oi;
      oi += 1;
      ni += 1;
    }
  }
  return { o, n, ctx };
}

/** First tier (0/1/2) where a single line occurs at or after `from`; the first such position. */
function anchorAt(fileLines: string[], anchor: string, strict: boolean, from: number): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const key = tierKey(anchor, t);
    for (let p = from; p < fileLines.length; p++) {
      if (tierKey(fileLines[p]!, t) === key) return p;
    }
  }
  return null;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseV4a(lines);
  return sections.map((sec) => {
    return (tree: Tree) => {
      const paths: string[] = [sec.path];
      if (sec.moveTo !== null) paths.push(sec.moveTo);
      checkSafe(paths);
      if (sec.kind === 'add') {
        if (tree.get(sec.path) !== null) throw new Fail('exists', sec.path);
        tree.now.set(sec.path, sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n');
        return;
      }
      if (sec.kind === 'delete') {
        if (tree.get(sec.path) === null) throw new Fail('missing', sec.path);
        tree.now.set(sec.path, null);
        return;
      }
      const cur = tree.get(sec.path);
      if (cur === null) throw new Fail('missing', sec.path);
      if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
      let view = splitText(cur);
      let cursor = 0;
      for (const chunk of sec.chunks) {
        if (chunk.anchor !== null) {
          const at = anchorAt(view.lines, chunk.anchor, strict, cursor);
          if (at === null) throw new Fail('no-match', sec.path);
          cursor = at + 1;
        }
        const { o, n, ctx } = chunkParts(chunk.body);
        if (o.length === 0) {
          const pos = chunk.eof ? view.lines.length : cursor;
          const lines = [...view.lines.slice(0, pos), ...n, ...view.lines.slice(pos)];
          view = { lines, br: view.br, final: view.final };
          cursor = pos + n.length;
          continue;
        }
        let found: { tier: number; pos: number } | null = null;
        const tiers = strict ? [0] : [0, 1, 2];
        for (const t of tiers) {
          const occ = occurrencesAt(view.lines, o, t, cursor).filter((p) => !chunk.eof || p + o.length === view.lines.length);
          if (occ.length > 0) {
            found = { tier: t, pos: occ[0]! };
            break;
          }
        }
        if (found === null) throw new Fail('no-match', sec.path);
        const lines = applyMatch(view.lines, found.pos, o, n, ctx, found.tier);
        view = { lines, br: view.br, final: view.final };
        cursor = found.pos + n.length;
      }
      if (sec.moveTo !== null) {
        tree.move(sec.path, sec.moveTo, joinText(view));
      } else {
        replaceFileText(tree, sec.path, view);
      }
    };
  });
}

// ---------- Section 1, 2, 10: run the CLI ----------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
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
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = 0;
      tree.moves.push(...beforeMoves);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row {
    key: string;
    line: string;
  }
  const rows: Row[] = [];
  const rNew = new Set<string>();
  const rOld = new Set<string>();
  for (const m of tree.moves) {
    if (tree.original(m.old) !== null && tree.get(m.old) === null && tree.original(m.nw) === null && tree.get(m.nw) !== null) {
      rows.push({ key: m.nw, line: `R ${m.old} -> ${m.nw}` });
      rNew.add(m.nw);
      rOld.add(m.old);
    }
  }
  for (const p of [...tree.now.keys()]) {
    if (rNew.has(p) || rOld.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  if (!check) {
    for (const p of [...tree.now.keys()]) {
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
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
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
