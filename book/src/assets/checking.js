// Checking a result: select main results, then light up the definitions a
// reader needs to check them. The selection is shared by every page through
// localStorage; the reading paths come from assets/claims.json (see build.mjs).
(() => {
  const KEY = 'bst-checking';
  const FOCUS = 'bst-checking-focus';
  const here = decodeURIComponent(location.pathname.split('/').pop() || 'index.html');
  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  let data = null;
  let selected = new Set();
  try { selected = new Set(JSON.parse(localStorage.getItem(KEY) || '[]')); } catch { /* ignore */ }

  const params = new URLSearchParams(location.search);
  if (params.get('select')) selected.add(params.get('select'));

  function save() {
    localStorage.setItem(KEY, JSON.stringify([...selected]));
    apply();
  }

  // name -> [claim ids], for the selected claims.
  function neededNames() {
    const out = new Map();
    for (const c of data.claims) {
      if (!selected.has(c.id)) continue;
      for (const n of c.needs) {
        if (!out.has(n)) out.set(n, []);
        out.get(n).push(c.id);
      }
    }
    return out;
  }
  const claimTitle = (id) => data.claims.find((c) => c.id === id)?.title ?? id;
  const split = (href) => {
    const i = href.indexOf('#');
    return i < 0 ? [href, ''] : [href.slice(0, i), decodeURIComponent(href.slice(i + 1))];
  };

  // The shown definitions to read, in book order.
  function path(needed) {
    return [...needed.keys()].map((n) => ({ n, d: data.decls[n] }))
      .filter((e) => e.d?.href)
      .sort((a, b) => a.d.ch - b.d.ch || a.d.o - b.d.o);
  }

  function apply() {
    if (!data) return;
    for (const id of [...selected]) if (!data.claims.some((c) => c.id === id)) selected.delete(id);
    const needed = neededNames();
    const active = selected.size > 0;
    document.body.classList.toggle('checking', active);
    document.body.classList.toggle('check-focus', active && localStorage.getItem(FOCUS) === '1');
    document.querySelectorAll('.claim-toggle').forEach((box) => { box.checked = selected.has(box.dataset.claim); });
    document.querySelectorAll('.headline, .claim-row').forEach((el) => el.classList.toggle('selected', selected.has(el.dataset.claim ?? el.id.replace(/^claim-/, ''))));

    // Declarations on this page.
    document.querySelectorAll('figure.decl.needed, figure.decl.claim-root').forEach((f) => {
      f.classList.remove('needed', 'claim-root');
      f.querySelector('.needed-chip')?.remove();
    });
    const sections = new Set();
    const steps = path(needed);
    for (const { n, d } of steps) {
      const [file, id] = split(d.href);
      if (file !== here) continue;
      const fig = document.getElementById(id)?.closest('figure.decl');
      if (!fig) continue;
      fig.classList.add('needed');
      const chip = document.createElement('span');
      chip.className = 'needed-chip';
      chip.textContent = 'needed';
      chip.title = 'Needed to check: ' + needed.get(n).map((c) => claimTitle(c).replace(/<[^>]+>/g, '')).join('; ');
      fig.querySelector('figcaption')?.prepend(chip);
      if (d.sec) sections.add(d.sec.id);
    }
    for (const c of data.claims) {
      if (!selected.has(c.id)) continue;
      for (const t of c.theorems) {
        if (!t.href) continue;
        const [file, id] = split(t.href);
        if (file === here) document.getElementById(id)?.closest('figure.decl')?.classList.add('claim-root');
      }
    }

    // Sidebar: chapters and, for this chapter, sections that hold something to read.
    const perChapter = new Map();
    for (const { d } of steps) perChapter.set(d.ch, (perChapter.get(d.ch) ?? 0) + 1);
    for (const c of data.claims) if (selected.has(c.id)) perChapter.set(`root${c.chapter}`, true);
    document.querySelectorAll('.toc > li > a').forEach((a) => {
      a.querySelector('.check-count')?.remove();
      a.parentElement.classList.remove('needed');
      const index = data.chapters.findIndex((ch) => ch.href === a.getAttribute('href'));
      const count = perChapter.get(index);
      const root = perChapter.get(`root${index}`);
      if (!count && !root) return;
      a.parentElement.classList.add('needed');
      const badge = document.createElement('span');
      badge.className = 'check-count';
      badge.textContent = count ? String(count) : '★';
      badge.title = count ? `${count} definition${count === 1 ? '' : 's'} to read here` : 'States a selected result';
      a.append(badge);
    });
    document.querySelectorAll('.toc-sections a').forEach((a) => {
      a.classList.toggle('needed', sections.has(decodeURIComponent(a.getAttribute('href').slice(1))));
    });

    renderBar(needed, steps);
    renderReadingList(needed, steps);
  }

  // A small bar at the bottom of every page while results are selected.
  let bar = null;
  function renderBar(needed, steps) {
    if (!selected.size) { bar?.remove(); bar = null; return; }
    if (!bar) {
      bar = document.createElement('div');
      bar.className = 'check-bar';
      bar.setAttribute('role', 'region');
      bar.setAttribute('aria-label', 'Checking a result');
      document.body.append(bar);
      bar.addEventListener('click', onBarClick);
      bar.addEventListener('change', (e) => {
        if (e.target.matches('.check-focus-toggle')) {
          localStorage.setItem(FOCUS, e.target.checked ? '1' : '0');
          apply();
        }
      });
    }
    const titles = [...selected].map(claimTitle);
    const onPage = steps.filter(({ d }) => split(d.href)[0] === here).length;
    const internal = [...needed.keys()].filter((n) => !data.decls[n]?.href).length;
    const label = titles.length === 1 ? titles[0] : `${titles.length} results`;
    bar.innerHTML = `<span class="cb-what">Checking <strong>${label}</strong></span>`
      + `<span class="cb-count">${steps.length} to read${internal ? ` (+${internal} internal)` : ''} · ${onPage} on this page</span>`
      + `<span class="cb-nav"><button type="button" class="cb-prev" title="Previous definition to read">‹</button>`
      + `<button type="button" class="cb-next" title="Next definition to read">›</button></span>`
      + `<label class="cb-focus"><input type="checkbox" class="check-focus-toggle"${localStorage.getItem(FOCUS) === '1' ? ' checked' : ''}> dim the rest</label>`
      + `<a class="cb-list" href="checking.html#reading-list">reading list</a>`
      + `<button type="button" class="cb-clear" title="Stop checking">✕</button>`;
    bar.querySelector('.cb-prev').disabled = bar.querySelector('.cb-next').disabled = steps.length === 0;
  }

  function onBarClick(e) {
    if (e.target.closest('.cb-clear')) { selected.clear(); save(); return; }
    const dir = e.target.closest('.cb-next') ? 1 : e.target.closest('.cb-prev') ? -1 : 0;
    if (!dir) return;
    const steps = path(neededNames());
    if (!steps.length) return;
    const pageIndex = data.chapters.findIndex((ch) => ch.href === here);
    // Position: the first step at or after the top of the viewport on this page.
    const located = steps.map((s, i) => {
      const [file, id] = split(s.d.href);
      if (file !== here) return null;
      const el = document.getElementById(id);
      return el ? { i, top: el.closest('figure.decl')?.getBoundingClientRect().top ?? 0 } : null;
    }).filter(Boolean);
    let target;
    if (dir > 0) {
      const after = located.find((l) => l.top > 90);
      target = after ? after.i : steps.findIndex((s) => s.d.ch > pageIndex);
      if (target < 0) target = 0;
    } else {
      const before = located.filter((l) => l.top < 60).pop();
      if (before) target = before.i;
      else {
        const earlier = steps.map((s, i) => [s, i]).filter(([s]) => s.d.ch < pageIndex).pop();
        target = earlier ? earlier[1] : steps.length - 1;
      }
    }
    const [file, id] = split(steps[target].d.href);
    if (file === here) {
      const fig = document.getElementById(id);
      history.replaceState(null, '', '#' + encodeURIComponent(id).replace(/%2E/g, '.'));
      fig?.scrollIntoView({ block: 'start', behavior: 'smooth' });
      window.dispatchEvent(new HashChangeEvent('hashchange'));
    } else {
      location.href = steps[target].d.href;
    }
  }

  // The checking page lists everything to read, grouped by chapter and section.
  function renderReadingList(needed, steps) {
    const box = document.getElementById('reading-list');
    if (!box) return;
    if (!selected.size) {
      box.innerHTML = '<p class="reading-empty">Select one or more results above to see what to read.</p>';
      return;
    }
    const chosen = data.claims.filter((c) => selected.has(c.id));
    const multi = chosen.length > 1;
    const tag = (n) => multi ? `<span class="rl-for">${needed.get(n).map((id) => esc(id)).join(' · ')}</span>` : '';
    let html = `<h2 class="rl-heading">What to read</h2>`;
    html += `<p class="rl-summary">${chosen.length === 1 ? 'This result rests' : 'These results rest'} on <strong>${needed.size}</strong> library definitions. `
      + `Proofs are not on the list: Lean checks them, and <a href="audit.html">Appendix A</a> lists the axioms they use.</p>`;
    html += '<h3>The statements</h3><ul class="rl-theorems">';
    for (const c of chosen) {
      html += `<li><a href="${esc(c.href)}">${c.title}</a>: ${c.theorems.map((t) => t.href ? `<a href="${esc(t.href)}"><code>${esc(t.s)}</code></a>` : `<code>${esc(t.s)}</code>`).join(', ')}</li>`;
    }
    html += '</ul>';
    html += '<h3>Definitions, in reading order</h3>';
    let lastCh = null;
    let lastSec = null;
    for (const { n, d } of steps) {
      if (d.ch !== lastCh) {
        if (lastCh !== null) html += '</ul>';
        const ch = data.chapters[d.ch];
        html += `<h4 class="rl-chapter"><a href="${esc(ch.href)}">${ch.number ? `Chapter ${esc(ch.number)} · ` : ''}${esc(ch.title)}</a></h4><ul class="rl-decls">`;
        lastCh = d.ch;
        lastSec = null;
      }
      const sec = d.sec ? d.sec.id : null;
      if (sec !== lastSec && d.sec) {
        html += `<li class="rl-section"><a href="${esc(data.chapters[d.ch].href)}#${esc(d.sec.id)}">${d.sec.number ? esc(d.sec.number) + ' ' : ''}${esc(d.sec.title)}</a></li>`;
      }
      lastSec = sec;
      html += `<li><a href="${esc(d.href)}"><code>${esc(n)}</code></a> <span class="kind-pill">${esc(d.k)}</span>${tag(n)}</li>`;
    }
    if (lastCh !== null) html += '</ul>';
    const internal = [...needed.keys()].filter((n) => !data.decls[n]?.href);
    if (internal.length) {
      html += `<h3>Definitions in internal modules</h3><p>These are not quoted in the book, because they live outside the reading interface. Read them in the library source:</p><ul class="rl-decls">`;
      for (const n of internal) {
        const d = data.decls[n];
        html += `<li>${d.src ? `<a href="${esc(d.src)}"><code>${esc(n)}</code></a>` : `<code>${esc(n)}</code>`} <span class="kind-pill">${esc(d.k)}</span> <span class="rl-module">${esc(d.m ?? '')}</span>${tag(n)}</li>`;
      }
      html += '</ul>';
    }
    const skips = chosen.flatMap((c) => c.skips.map((s) => ({ ...s, claim: c })));
    if (skips.length) {
      html += '<h3>What you may skip</h3><ul class="rl-skips">';
      for (const s of skips) html += `<li><code>${esc(s.s)}</code>${multi ? ` <span class="rl-for">${esc(s.claim.id)}</span>` : ''}: ${s.reason}</li>`;
      html += '</ul>';
    }
    const ext = new Map();
    for (const c of chosen) for (const e of c.external) ext.set(e.s, e.href);
    if (ext.size) {
      html += `<h3>From Lean and Mathlib</h3><p class="rl-ext">The statements also use these standard notions: ${[...ext].sort().map(([s, href]) => href ? `<a href="${esc(href)}"><code>${esc(s)}</code></a>` : `<code>${esc(s)}</code>`).join(', ')}.</p>`;
    }
    box.innerHTML = html;
  }

  document.addEventListener('change', (e) => {
    const box = e.target.closest('.claim-toggle');
    if (!box) return;
    if (box.checked) selected.add(box.dataset.claim); else selected.delete(box.dataset.claim);
    save();
  });
  document.addEventListener('click', (e) => {
    if (e.target.closest('.claims-clear')) { selected.clear(); save(); }
    if (e.target.closest('.claims-key')) { for (const c of data?.claims ?? []) if (c.key) selected.add(c.id); save(); }
  });
  window.addEventListener('storage', (e) => {
    if (e.key !== KEY) return;
    try { selected = new Set(JSON.parse(e.newValue || '[]')); } catch { selected = new Set(); }
    apply();
  });

  fetch('assets/claims.json').then((r) => r.json()).then((d) => {
    data = d;
    if (params.get('select')) {
      save();
      document.getElementById('reading-list')?.scrollIntoView();
    } else apply();
  }).catch(() => { /* the page still works without highlighting */ });
})();
