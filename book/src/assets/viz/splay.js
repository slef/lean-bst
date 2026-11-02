// Step through Splay.run: first `locate`, then one `splayAt` equation at a time.
// If the page shows the Lean definition of `splayAt`, the equation being applied
// is highlighted in it. With {"potential": true} the panel also tracks the
// potential and checks the access lemma on the actual run.

import * as T from './tree.js';
import { TreeView } from './render.js';
import { button, fmt, frame, label, mono, number, row, select } from './ui.js';

const EQUATIONS = {
  1: '[]', 2: '[.left b]', 3: '[.right a]',
  4: '.left b :: .left c :: cs', 5: '.right a :: .right b :: cs',
  6: '.right a :: .left b :: cs', 7: '.left b :: .right a :: cs',
};

function keysOf(t, lo) {
  const n = T.size(t);
  return n === 0 ? 'empty' : n === 1 ? `key ${lo}` : `keys ${lo}–${lo + n - 1}`;
}

/** All intermediate states of `run t x`. */
function trace(t, x) {
  const c = T.locate(t, x);
  if (c.focus === null) return null;
  const states = [{ tree: t, l: c.focus[0], r: c.focus[1], context: c.context, rotations: 0, equation: null }];
  let { context } = c;
  let [l, r] = c.focus;
  let rotations = 0;
  for (;;) {
    const s = T.splayStep(l, r, context);
    if ('result' in s) {
      rotations += s.equation === 1 ? 0 : 1;
      states.push({ tree: s.result, l: s.result[0], r: s.result[1], context: [], rotations, equation: s.equation, kind: s.case, final: true });
      break;
    }
    rotations += 2;
    ({ l, r, context } = s);
    states.push({ tree: T.plug(context, T.node(l, r)), l, r, context, rotations, equation: s.equation, kind: s.case });
  }
  return { states, cost: c.context.length, locate: c };
}

export default function mount(root, cfg) {
  let n = cfg.n ?? 11;
  let shape = cfg.shape ?? 'random';
  let seed = cfg.seed ?? 5;
  let tree = cfg.tree ? T.fromLean(cfg.tree) : T.makeTree(shape, n, seed);
  let x = cfg.x ?? Math.max(0, T.size(tree) - 2);
  let run = null;
  let pos = 0;
  let playing = null;
  const w = () => 1; // unit weights

  const ui = frame(root, {
    title: cfg.title ?? 'Splaying, one equation at a time',
    help: 'Click a node to choose the requested rank, then step. Each step applies one equation of splayAt to the search context.',
  });
  const view = new TreeView(ui.stage, {
    onNode: (k) => { stop(); if (run && pos === run.states.length - 1) tree = run.states[pos].tree; x = k; xInput.value = k; prepare(); },
  });

  const xInput = number(x, { min: 0, max: 63, label: 'requested rank', onChange: (v) => { stop(); x = Math.min(v, T.size(tree) - 1); xInput.value = x; prepare(); } });
  const back = button('◀', () => { stop(); if (pos > 0) { pos--; draw(); } }, { title: 'Previous step' });
  const fwd = button('Step ▶', () => { stop(); if (run && pos < run.states.length - 1) { pos++; draw(); } });
  const play = button('Play', () => {
    if (playing) { stop(); return; }
    if (run && pos === run.states.length - 1) pos = 0;
    play.textContent = 'Pause';
    const tick = () => {
      if (!run || pos >= run.states.length - 1) { stop(); return; }
      pos++; draw();
      playing = setTimeout(tick, 900);
    };
    draw();
    playing = setTimeout(tick, 600);
  });
  const again = button('Keep result', () => { stop(); if (run) { tree = run.states[run.states.length - 1].tree; prepare(); } }, { title: 'Make the splayed tree the starting tree for the next request' });
  function stop() { clearTimeout(playing); playing = null; play.textContent = 'Play'; }

  ui.controls.append(
    label('x', xInput), back, fwd, play, again,
  );
  if (!cfg.tree) {
    ui.controls.append(
      label('shape', select([['random', 'random'], ['balanced', 'balanced'], ['left-path', 'left path'], ['right-path', 'right path'], ['zigzag', 'zigzag']], shape, (v) => { shape = v; regenerate(); })),
      label('n', number(n, { min: 1, max: 40, label: 'number of keys', onChange: (v) => { n = v; regenerate(); } })),
      button('New', () => { seed++; regenerate(); }),
    );
  }
  function regenerate() { stop(); tree = T.makeTree(shape, n, seed); x = Math.min(x, n - 1); xInput.value = x; prepare(); }

  function prepare() {
    run = trace(tree, x);
    pos = 0;
    draw();
  }

  // Highlight an equation of splayAt in the Lean listing on this page.
  function highlightEquation(eq) {
    const fig = document.getElementById('decl-RotationBST.Splay.splayAt');
    if (!fig) return;
    const lines = [...fig.querySelectorAll('.line')];
    const eqLines = lines.filter((l) => l.textContent.trimStart().startsWith('|'));
    lines.forEach((l) => l.classList.remove('hl'));
    if (eq) eqLines[eq - 1]?.classList.add('hl');
  }

  function draw() {
    if (!run) return;
    const s = run.states[pos];
    const classes = new Map([[x, 'target']]);
    // Ancestors of x in the current whole tree.
    const path = T.pathTo(s.tree, x) ?? [];
    let t = s.tree; let lo = 0;
    const edgeClasses = new Map();
    for (const d of path) {
      const k = lo + T.size(t[0]);
      classes.set(k, 'path');
      if (d === 'L') t = t[0]; else { lo = k + 1; t = t[1]; }
      edgeClasses.set(lo + T.size(t[0]), 'path');
    }
    view.update(s.tree, { classes, edgeClasses });
    highlightEquation(s.equation);
    back.disabled = pos === 0;
    fwd.disabled = pos === run.states.length - 1;

    ui.state.replaceChildren();
    const c = run.locate;
    // Frames of the remaining context, nearest ancestor first, with the keys
    // their stored subtree holds.
    const frames = [];
    {
      let off = 0;
      const offsets = [];
      for (let i = s.context.length - 1; i >= 0; i--) {
        offsets[i] = off;
        if (s.context[i].side === 'right') off += T.size(s.context[i].tree) + 1;
      }
      // offsets[i] = number of keys before the subtree that frame i's parent roots,
      // counted from the frames above it.
      for (let i = 0; i < s.context.length; i++) {
        const f = s.context[i];
        const parentLo = offsets[i];
        const innerSize = T.size(T.plug(s.context.slice(0, i), T.node(s.l, s.r)));
        const lo = f.side === 'left' ? parentLo + innerSize + 1 : parentLo;
        frames.push(`.${f.side} ⟨${keysOf(f.tree, lo)}⟩`);
      }
    }
    if (pos === 0) {
      ui.state.append(row('locate t x', `focus is the node with key ${x}; context has ${c.context.length} frame${c.context.length === 1 ? '' : 's'}, nearest ancestor first`));
    } else {
      ui.state.append(row(`equation ${s.equation}`, `${mono(EQUATIONS[s.equation])} — ${s.kind}${s.equation === 1 ? ' (nothing left to do)' : ''}`));
    }
    ui.state.append(row('context', s.context.length ? mono(`[${frames.join(', ')}]`) : mono('[]')));
    ui.state.append(row('rotations so far', `${s.rotations} <span class="vnote">of (run t x).2 = context.length = ${run.cost}</span>`));
    if (s.final) ui.state.append(row('result', `${mono(`(run t ${x}).1`)} has key ${x} at the root: its left subtree has size ${T.size(s.tree[0])}`));

    if (cfg.potential) {
      const W = T.mass(w, tree);
      const phi0 = T.potential(w, tree);
      const phi = T.potential(w, s.tree);
      const amort = s.rotations + phi - phi0;
      const bound = 3 * (Math.log2(W) - Math.log2(w(x))) + 1;
      const sub = T.mass(w, c.focus, T.offset(c.context));
      const boundSub = 3 * (Math.log2(W) - Math.log2(sub)) + 1;
      ui.state.append(row('potential Φ', `${fmt(phi0)} → ${fmt(phi)} <span class="vnote">(sum of log₂ of subtree sizes; unit weights)</span>`));
      ui.state.append(row('rotations + ΔΦ', fmt(amort)));
      if (s.final) {
        ui.state.append(row('access_lemma', `${fmt(amort)} ≤ 3(log₂ ${W} − log₂ 1) + 1 = ${fmt(bound)} ${amort <= bound + 1e-9 ? '<span class="vok">✓</span>' : '<span class="vno">✗</span>'}`));
        ui.state.append(row('access_lemma_subtree', `${fmt(amort)} ≤ 3(log₂ ${W} − log₂ ${sub}) + 1 = ${fmt(boundSub)} ${amort <= boundSub + 1e-9 ? '<span class="vok">✓</span>' : '<span class="vno">✗</span>'}`));
      }
    }
  }
  prepare();
}
