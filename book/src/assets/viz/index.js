// Mount every interactive figure on the page. `@viz kind {…}` loads ./kind.js,
// whose default export receives the container element and the JSON options.

for (const root of document.querySelectorAll('.viz[data-viz]')) {
  const kind = root.dataset.viz;
  if (!/^[a-z][a-z0-9-]*$/.test(kind)) { root.textContent = `Unknown figure: ${kind}`; continue; }
  const cfg = JSON.parse(root.dataset.config || '{}');
  import(`./${kind}.js`).then((m) => m.default(root, cfg)).catch((e) => {
    root.textContent = `This figure failed to load: ${e.message}`;
    console.error(e);
  });
}
