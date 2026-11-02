// Mount every interactive figure on the page.
const modules = {
  shape: () => import('./shape.js'),
  rotate: () => import('./rotate.js'),
  splay: () => import('./splay.js'),
  pointer: () => import('./pointer.js'),
  experiment: () => import('./experiment.js'),
  workingset: () => import('./workingset.js'),
  updates: () => import('./updates.js'),
};

for (const root of document.querySelectorAll('.viz[data-viz]')) {
  const load = modules[root.dataset.viz];
  if (!load) { root.textContent = `Unknown figure: ${root.dataset.viz}`; continue; }
  const cfg = JSON.parse(root.dataset.config || '{}');
  load().then((m) => m.default(root, cfg)).catch((e) => {
    root.textContent = `This figure failed to load: ${e.message}`;
    console.error(e);
  });
}
