// Collect everything the book needs from the compiled Lean library.
//
// Inputs (under LEAN_ROOT, default: the parent of book/):
//   .lake/build/lib/lean/**/*.ilean   declaration ranges and every identifier
//                                     reference, as computed by Lean itself
//   RotationBST/**/*.lean             the sources the ranges point into
// and the output of book/lean/Export.lean (signatures, docstrings, axioms,
// test vectors), which this script runs through `lake env lean`.
//
// Output: book/build/lean-data.json and book/build/vectors.json.
//
// The library must have been built (`lake build`) from the current sources.
// The script checks this: every declaration's name must appear at its recorded
// position, otherwise the .ilean files are stale and extraction fails.

import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const bookDir = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const leanRoot = resolve(process.env.LEAN_ROOT ?? join(bookDir, '..'));
const buildDir = join(bookDir, 'build');
const ileanRoot = join(leanRoot, '.lake', 'build', 'lib', 'lean');
const LIBRARY = 'RotationBST';

if (!existsSync(join(ileanRoot, LIBRARY))) {
  console.error(`No compiled library under ${ileanRoot}. Run \`lake build\` in ${leanRoot} first,`
    + ' or point LEAN_ROOT at a built checkout.');
  process.exit(1);
}
mkdirSync(buildDir, { recursive: true });

// Only modules reachable from the library root count; the build directory may
// still hold artifacts of deleted modules.
const ileanOf = (module) => join(ileanRoot, module.replaceAll('.', '/') + '.ilean');
const ileans = [];
{
  const seen = new Set();
  const pending = [LIBRARY];
  while (pending.length) {
    const module = pending.pop();
    if (seen.has(module)) continue;
    seen.add(module);
    const file = ileanOf(module);
    if (!existsSync(file)) {
      console.error(`Missing compiled module ${module}. Run \`lake build\` first.`);
      process.exit(1);
    }
    ileans.push(file);
    for (const [dep] of JSON.parse(readFileSync(file, 'utf8')).directImports ?? []) {
      if (dep === LIBRARY || dep.startsWith(LIBRARY + '.')) pending.push(dep);
    }
  }
}

const modules = {};
const names = new Set();
const problems = [];

for (const file of ileans) {
  const ilean = JSON.parse(readFileSync(file, 'utf8'));
  const module = ilean.module;
  const path = module.replaceAll('.', '/') + '.lean';
  const sourcePath = join(leanRoot, path);
  if (!existsSync(sourcePath)) {
    problems.push(`${module}: compiled, but ${path} no longer exists`);
    continue;
  }
  const source = readFileSync(sourcePath, 'utf8');
  const lines = source.split('\n');

  // decls: name -> [line, col, endLine, endCol, selLine, selCol, selEndLine, selEndCol],
  // zero-based lines and UTF-16 columns (LSP conventions).
  const decls = {};
  for (const [name, r] of Object.entries(ilean.decls ?? {})) {
    if (name.includes('._') || name.includes('.match_') || name.includes('.proof_')) continue;
    const selected = (lines[r[4]] ?? '').slice(r[5], r[7]);
    const tail = name.split('.').slice(-selected.split('.').length).join('.');
    const anonymous = selected === 'instance' || selected === 'example';
    if (!anonymous && selected.replace(/[«»]/g, '') !== tail.replace(/[«»]/g, '')) {
      problems.push(`${module}: ${name} is recorded at line ${r[4] + 1}, which reads ${JSON.stringify(selected)}`);
    }
    decls[name] = r;
    names.add(name);
  }

  // refs: [line, col, endLine, endCol, constant]; plus local definition sites
  // (constructors, structure fields) as defs.
  const refs = [];
  const defs = [];
  for (const [key, info] of Object.entries(ilean.references ?? {})) {
    const ident = JSON.parse(key);
    if (!ident.c) continue;
    const constant = ident.c.n;
    names.add(constant);
    for (const u of info.usages ?? []) refs.push([u[0], u[1], u[2], u[3], constant]);
    if (info.definition) {
      const d = info.definition;
      defs.push([d[0], d[1], d[2], d[3], constant]);
    }
  }
  refs.sort((a, b) => a[0] - b[0] || a[1] - b[1] || (b[2] - b[0]) - (a[2] - a[0]) || b[3] - a[3]);

  // `#check_bst_abstract NS allowing [M₁, …]`: the statement reading base.
  const audits = [];
  const auditRe = /#check_bst_abstract\s+([\w.]+)(?:\s+allowing\s*\[([^\]]*)\])?/g;
  for (const m of source.matchAll(auditRe)) {
    audits.push({
      namespace: m[1],
      allowed: (m[2] ?? '').split(',').map((s) => s.trim()).filter(Boolean),
    });
  }

  modules[module] = { path, source, decls, refs, defs, audits };
}

if (problems.length) {
  console.error('The compiled Lean data does not match the sources. Rebuild with `lake build`.');
  for (const p of problems.slice(0, 20)) console.error('  ' + p);
  process.exit(1);
}

const namesFile = join(buildDir, 'names.txt');
const constsFile = join(buildDir, 'consts.json');
const vectorsFile = join(buildDir, 'vectors.json');
writeFileSync(namesFile, [...names].sort().join('\n') + '\n');

const lake = process.env.LAKE ?? 'lake';
console.log(`Exporting ${names.size} constants from ${Object.keys(modules).length} modules…`);
execFileSync(lake, ['env', 'lean', join(bookDir, 'lean', 'Export.lean')], {
  cwd: leanRoot,
  stdio: 'inherit',
  env: { ...process.env, BOOK_NAMES: namesFile, BOOK_OUT: constsFile, BOOK_VECTORS: vectorsFile },
});

const exported = JSON.parse(readFileSync(constsFile, 'utf8'));
const consts = {};
for (const c of exported.consts) consts[c.name] = c;

// Some declarations (for example certain Prop-valued definitions) have no
// entry in their module's .ilean `decls`. Fall back to Lean's own ranges.
for (const c of exported.consts) {
  const m = modules[c.module];
  if (!m || !c.range || m.decls[c.name] || c.kind === 'constructor' || c.kind === 'field') continue;
  if (c.name.includes('._') || c.name.includes('.match_') || c.name.includes('.proof_')) continue;
  m.decls[c.name] = c.range;
}
for (const c of exported.consts) delete c.range;

let commit = null;
try {
  commit = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: leanRoot, encoding: 'utf8' }).trim();
} catch { /* not a git checkout */ }
let dirty = false;
try {
  dirty = execFileSync('git', ['status', '--porcelain', '--', LIBRARY], { cwd: leanRoot, encoding: 'utf8' }).trim() !== '';
} catch { /* ignore */ }
const toolchain = readFileSync(join(leanRoot, 'lean-toolchain'), 'utf8').trim();

writeFileSync(join(buildDir, 'lean-data.json'), JSON.stringify({
  generated: new Date().toISOString(),
  leanRoot: relative(bookDir, leanRoot) || '.',
  commit, dirty, toolchain,
  modules, consts, missing: exported.missing,
}));
console.log(`Wrote build/lean-data.json (${Object.keys(consts).length} constants`
  + `${exported.missing.length ? `, ${exported.missing.length} unresolved` : ''}).`);
