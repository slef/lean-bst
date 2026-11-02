// Small DOM helpers shared by the figures.

export function h(tag, attrs = {}, ...children) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs ?? {})) {
    if (v === undefined || v === null || v === false) continue;
    if (k.startsWith('on')) e.addEventListener(k.slice(2).toLowerCase(), v);
    else if (k === 'class') e.className = v;
    else if (k === 'html') e.innerHTML = v;
    else e.setAttribute(k, v === true ? '' : v);
  }
  for (const c of children.flat()) if (c !== null && c !== undefined && c !== false) e.append(c);
  return e;
}

export const button = (label, onClick, attrs = {}) => h('button', { type: 'button', class: 'vbtn', onClick, ...attrs }, label);

export function select(options, value, onChange, attrs = {}) {
  const s = h('select', { class: 'vsel', ...attrs });
  for (const [v, label] of options) s.append(h('option', { value: v, selected: String(v) === String(value) }, label));
  s.addEventListener('change', () => onChange(s.value));
  return s;
}

export function number(value, { min = 0, max = 99, step = 1, onChange, label }) {
  const i = h('input', { type: 'number', class: 'vnum', min, max, step, value, 'aria-label': label });
  i.addEventListener('change', () => {
    const v = Math.max(min, Math.min(max, Number(i.value) || min));
    i.value = v;
    onChange(v);
  });
  return i;
}

export const label = (text, control) => h('label', { class: 'vlabel' }, h('span', {}, text), control);

/** The standard frame: title bar with controls, stage, state panel, help line. */
export function frame(root, { title, help }) {
  root.replaceChildren();
  const controls = h('div', { class: 'viz-controls' });
  const bar = h('div', { class: 'viz-bar' }, h('span', { class: 'viz-title' }, title), controls);
  const stage = h('div', { class: 'viz-stage' });
  const state = h('div', { class: 'viz-state' });
  const helpEl = help ? h('div', { class: 'viz-help' }, help) : null;
  root.append(bar, stage, state);
  if (helpEl) root.append(helpEl);
  return { controls, stage, state, help: helpEl };
}

/** A key/value row in the state panel; values are HTML (already escaped by callers). */
export const row = (k, v, cls = '') => h('div', { class: `vrow ${cls}` }, h('span', { class: 'vk' }, k), h('span', { class: 'vv', html: v }));

export const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
export const mono = (s) => `<code>${esc(s)}</code>`;
export const fmt = (x, d = 2) => (Number.isInteger(x) ? String(x) : x.toFixed(d));
