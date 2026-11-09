// Page behaviour: hover cards for Lean identifiers and citations, theme, menu,
// copy, proofs.
(() => {
  const data = JSON.parse(document.getElementById('lean-hover')?.textContent || '[]');
  const refs = JSON.parse(document.getElementById('bib-hover')?.textContent || '[]');
  const card = document.querySelector('.hover-card');
  const home = card?.parentNode;
  const TARGET = 'a.ref[data-c], a.cite[data-b]';
  let showTimer = null;
  let hideTimer = null;
  let current = null;

  const esc = (s) => s.replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

  function fill(entry) {
    let html = `<pre>${esc(entry.s)}</pre>`;
    if (entry.d) html += `<div class="hc-doc">${entry.d}</div>`;
    html += `<div class="hc-foot"><span class="hc-kind">${esc(entry.k)}</span>`;
    if (entry.m) html += `<span>${esc(entry.m)}</span>`;
    if (entry.b) html += `<span>→ ${esc(entry.b)}</span>`;
    html += '</div>';
    card.innerHTML = html;
  }

  function place(el) {
    const r = el.getBoundingClientRect();
    card.hidden = false;
    card.style.left = '0px';
    card.style.top = '0px';
    const w = card.offsetWidth;
    const h = card.offsetHeight;
    let left = Math.min(r.left, window.innerWidth - w - 12);
    left = Math.max(12, left);
    let top = r.bottom + 6;
    if (top + h > window.innerHeight - 8 && r.top - h - 6 > 8) top = r.top - h - 6;
    card.style.left = `${left}px`;
    card.style.top = `${top}px`;
  }

  // A citation card holds the full reference and its links. It is moved
  // just after the citation, so that Tab reaches its links next.
  function fillCite(html, el) {
    card.innerHTML = `<div class="hc-ref">${html}</div>`
      + `<div class="hc-foot"><span class="hc-kind">reference</span><a href="${el.getAttribute('href')}">→ bibliography</a></div>`;
    el.after(card);
  }

  function show(el) {
    if (!card) return;
    const isCite = el.matches('a.cite');
    const entry = isCite ? refs[Number(el.dataset.b)] : data[Number(el.dataset.c)];
    if (!entry) return;
    clearTimeout(hideTimer);
    if (current) current.classList.remove('hovered');
    current = el;
    el.classList.add('hovered');
    card.classList.toggle('cite-card', isCite);
    if (isCite) fillCite(entry, el);
    else {
      if (card.parentNode !== home) home.appendChild(card);
      fill(entry);
    }
    place(el);
  }
  function hideNow() {
    card.hidden = true;
    if (current) current.classList.remove('hovered');
    current = null;
  }
  function hide() {
    hideTimer = setTimeout(hideNow, 180);
  }

  document.addEventListener('mouseover', (e) => {
    const el = e.target.closest(TARGET);
    if (el) {
      clearTimeout(showTimer);
      showTimer = setTimeout(() => show(el), current ? 0 : 220);
    } else if (e.target.closest('.hover-card')) {
      clearTimeout(hideTimer);
    }
  });
  document.addEventListener('mouseout', (e) => {
    if (e.target.closest(TARGET) || e.target.closest('.hover-card')) {
      clearTimeout(showTimer);
      if (!card.contains(document.activeElement)) hide();
    }
  });
  document.addEventListener('focusin', (e) => {
    const el = e.target.closest(TARGET);
    if (el) show(el);
    else if (e.target.closest('.hover-card')) clearTimeout(hideTimer);
  });
  document.addEventListener('focusout', (e) => {
    if (!e.target.closest(TARGET) && !e.target.closest('.hover-card')) return;
    // Moving focus from a citation into its card keeps the card open.
    if (e.relatedTarget && (card.contains(e.relatedTarget) || e.relatedTarget === current)) return;
    hide();
  });
  window.addEventListener('scroll', () => {
    if (!card || card.hidden) return;
    // A card opened from the keyboard follows its citation; others close.
    if (current && (current === document.activeElement || card.contains(document.activeElement))) place(current);
    else hideNow();
  }, { passive: true });
  document.addEventListener('keydown', (e) => {
    if (e.key !== 'Escape' || !card || card.hidden) return;
    const back = card.contains(document.activeElement) ? current : null;
    hideNow();
    back?.focus({ preventScroll: true });
    if (back) { clearTimeout(showTimer); hideNow(); }
  });

  // Touch: first tap shows the card, second tap follows the link.
  document.addEventListener('touchstart', (e) => {
    const el = e.target.closest(TARGET);
    if (el && current !== el) { e.preventDefault(); show(el); }
  }, { passive: false });

  // Same-page links to a declaration: flash it.
  function flash() {
    const id = decodeURIComponent(location.hash.slice(1));
    if (!id) return;
    const el = document.getElementById(id);
    const fig = el?.closest('figure.decl');
    if (fig) {
      fig.classList.remove('flash');
      void fig.offsetWidth;
      fig.classList.add('flash');
      setTimeout(() => fig.classList.remove('flash'), 1600);
    }
  }
  window.addEventListener('hashchange', flash);
  flash();

  // Theme.
  document.querySelector('.topbar .theme')?.addEventListener('click', () => {
    const next = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
    document.documentElement.dataset.theme = next;
    localStorage.setItem('theme', next);
    window.dispatchEvent(new Event('themechange'));
  });
  document.querySelector('.topbar .menu')?.addEventListener('click', () => document.body.classList.toggle('menu-open'));

  // Copy Lean source and proof toggles.
  document.addEventListener('click', (e) => {
    const copy = e.target.closest('figure.decl .copy');
    if (copy) {
      const fig = copy.closest('figure.decl');
      const lines = [...fig.querySelectorAll('pre.lean .line')].map((line) => {
        const clone = line.cloneNode(true);
        clone.querySelectorAll('.proof-elided').forEach((n) => n.remove());
        return clone.textContent;
      });
      navigator.clipboard?.writeText(lines.join('\n')).then(() => {
        copy.textContent = 'copied';
        setTimeout(() => { copy.textContent = 'copy'; }, 1200);
      });
      return;
    }
    const toggle = e.target.closest('figure.decl .proof-toggle');
    if (toggle) {
      const fig = toggle.closest('figure.decl');
      const open = fig.classList.toggle('proof-open');
      toggle.textContent = open ? 'hide proof' : 'show proof';
      toggle.setAttribute('aria-expanded', String(open));
    }
  });

  // Declaration index filter.
  const filter = document.querySelector('.index-filter input');
  if (filter) {
    filter.addEventListener('input', () => {
      const q = filter.value.trim().toLowerCase();
      document.querySelectorAll('table.decl-index tbody tr').forEach((tr) => {
        tr.hidden = q !== '' && !tr.dataset.search.includes(q);
      });
    });
  }
})();
