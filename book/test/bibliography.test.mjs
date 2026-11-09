// The citation syntax and the bibliography renderer (scripts/bibliography.mjs),
// and the checked-in data in src/bibliography.json.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import MarkdownIt from 'markdown-it';
import {
  citedKeys, citePlugin, familyName, formatReference, loadBibliography, parseCiteGroup, parseSourceLine, renderCitation, sortEntries,
} from '../scripts/bibliography.mjs';

const here = dirname(fileURLToPath(import.meta.url));

const ENTRIES = [
  { key: 'sleator1985', type: 'article', authors: ['Daniel D. Sleator', 'Robert E. Tarjan'], title: 'Self-adjusting binary search trees', venue: 'Journal of the ACM', volume: '32', number: '3', pages: '652–686', year: 1985, doi: '10.1145/3828.3835' },
  { key: 'iacono2001', type: 'inproceedings', authors: ['John Iacono'], title: 'Alternatives to splay trees with O(log n) worst-case access times', venue: 'Proceedings of the 12th ACM-SIAM Symposium on Discrete Algorithms (SODA)', pages: '516–522', year: 2001 },
  { key: 'demaine2009geometry', type: 'inproceedings', authors: ['Erik D. Demaine', 'Dion Harmon', 'John Iacono', 'Daniel M. Kane', 'Mihai Pătraşcu'], title: 'The geometry of binary search trees', venue: 'SODA', year: 2009, doi: '10.1137/1.9781611973068.55' },
  { key: 'demaine2009other', type: 'preprint', authors: ['Erik D. Demaine', 'Someone Else', 'A Third'], title: 'Another <paper> & more', year: 2009, arxiv: '0901.00001' },
  { key: 'vanemdeboas1977', type: 'article', authors: ['van Emde Boas, Peter'], title: 'Preserving order in a forest in less than logarithmic time and linear space', venue: 'Information Processing Letters', year: 1977,
    versions: [{ label: 'Conference version', type: 'inproceedings', venue: 'FOCS', year: 1975, doi: '10.1109/SFCS.1975.26' }] },
];
const bib = loadBibliography(ENTRIES);
const link = (entry) => ({ href: `bibliography.html#ref-${entry.key}`, attrs: ` data-b="${entry.key}"` });

function render(src) {
  const md = new MarkdownIt({ typographer: true });
  const errors = [];
  const cited = [];
  md.use(citePlugin, { bib, link, onError: (m) => errors.push(m), onCite: (k) => cited.push(k) });
  return { html: md.renderInline(src), errors, cited };
}

test('the test data is valid', () => {
  assert.deepEqual(bib.errors, []);
});

test('labels: one, two, or more authors, and suffixes for clashes', () => {
  assert.equal(bib.byKey.get('sleator1985').label, 'Sleator and Tarjan 1985');
  assert.equal(bib.byKey.get('iacono2001').label, 'Iacono 2001');
  assert.equal(bib.byKey.get('demaine2009geometry').label, 'Demaine et al. 2009b');
  assert.equal(bib.byKey.get('demaine2009other').label, 'Demaine et al. 2009a');
  assert.equal(bib.byKey.get('vanemdeboas1977').label, 'van Emde Boas 1977');
});

test('family names', () => {
  assert.equal(familyName('Mihai Pătraşcu'), 'Pătraşcu');
  assert.equal(familyName('van Emde Boas, Peter'), 'van Emde Boas');
  assert.deepEqual(sortEntries(ENTRIES).map((e) => e.key), ['demaine2009other', 'demaine2009geometry', 'iacono2001', 'sleator1985', 'vanemdeboas1977']);
});

test('validation catches malformed entries', () => {
  const { errors } = loadBibliography([
    { key: 'Bad-Key', type: 'article', authors: ['A B'], title: 'T', venue: 'V', year: 2000 },
    { key: 'ok2000', type: 'article', authors: ['A B'], title: 'T', venue: 'V', year: 2000, doi: 'doi:10.1/x' },
    { key: 'ok2000', type: 'article', authors: [], title: 'T', venue: 'V', year: 2001, colour: 'red' },
    { key: 'pre2010', type: 'preprint', authors: ['A B'], title: 'T', year: 2010 },
  ]);
  assert.ok(errors.some((e) => e.includes('Bad-Key') && e.includes('key must be')));
  assert.ok(errors.some((e) => e.includes('malformed doi')));
  assert.ok(errors.some((e) => e.includes('duplicate key')));
  assert.ok(errors.some((e) => e.includes('unknown field colour')));
  assert.ok(errors.some((e) => e.includes('authors must be')));
  assert.ok(errors.some((e) => e.includes("key's year")));
  assert.ok(errors.some((e) => e.includes('preprint needs')));
});

test('parsing citation groups', () => {
  assert.equal(parseCiteGroup('some text'), null);
  assert.deepEqual(parseCiteGroup('@a2000; -@b2001, Theorem 3').items, [
    { key: 'a2000', suppressAuthor: false, locator: undefined },
    { key: 'b2001', suppressAuthor: true, locator: 'Theorem 3' },
  ]);
  assert.deepEqual(parseCiteGroup('@a2000; nonsense').errors, ['malformed citation item "nonsense"']);
  assert.deepEqual(parseSourceLine('@sleator1985; @iacono2001'), ['sleator1985', 'iacono2001']);
  assert.deepEqual(parseSourceLine('[@sleator1985]'), ['sleator1985']);
  assert.equal(parseSourceLine('Sleator and Tarjan (1985)'), null);
  assert.equal(parseSourceLine('@sleator1985, Theorem 1'), null);
});

test('parenthetical, narrative, year-only and located citations', () => {
  let r = render('Splaying [@sleator1985] is fast.');
  assert.equal(r.html, 'Splaying (<a class="cite" href="bibliography.html#ref-sleator1985" data-b="sleator1985">Sleator and Tarjan 1985</a>) is fast.');
  r = render('[@sleator1985; @iacono2001, Section 2]');
  assert.equal(r.html, '(<a class="cite" href="bibliography.html#ref-sleator1985" data-b="sleator1985">Sleator and Tarjan 1985</a>; '
    + '<a class="cite" href="bibliography.html#ref-iacono2001" data-b="iacono2001">Iacono 2001</a>, Section 2)');
  assert.deepEqual(r.cited, ['sleator1985', 'iacono2001']);
  r = render('As @iacono2001 showed.');
  assert.equal(r.html, 'As <a class="cite" href="bibliography.html#ref-iacono2001" data-b="iacono2001">Iacono (2001)</a> showed.');
  r = render('Iacono [-@iacono2001]');
  assert.equal(r.html, 'Iacono (<a class="cite" href="bibliography.html#ref-iacono2001" data-b="iacono2001">2001</a>)');
  r = render('@demaine2009geometry');
  assert.match(r.html, />Demaine et al\. \(2009b\)</);
});

test('what is not a citation', () => {
  for (const src of ['mail claude@slef.org', '`[@sleator1985]` in code', '@decl Foo', 'a [link](x.html)', '@[simp] lemma', 'see [Chapter 3](a.html)']) {
    const r = render(src);
    assert.ok(!r.html.includes('class="cite"'), src);
    assert.deepEqual(r.errors, [], src);
  }
});

test('unknown keys and malformed groups are errors', () => {
  let r = render('[@nobody1999]');
  assert.deepEqual(r.errors, ['unknown citation key nobody1999']);
  assert.equal(r.html, '[@nobody1999]');
  r = render('As @nobody1999 said');
  assert.deepEqual(r.errors, ['unknown citation key nobody1999']);
  r = render('[@sleator1985; oops]');
  assert.deepEqual(r.errors, ['malformed citation item "oops"']);
});

test('source lines render without parentheses', () => {
  assert.equal(renderCitation(bib, ['sleator1985', 'iacono2001'], 'source', link),
    '<a class="cite" href="bibliography.html#ref-sleator1985" data-b="sleator1985">Sleator and Tarjan 1985</a>; '
    + '<a class="cite" href="bibliography.html#ref-iacono2001" data-b="iacono2001">Iacono 2001</a>');
});

test('formatted references', () => {
  assert.equal(formatReference(bib.byKey.get('sleator1985')),
    '<span class="bib-authors">Daniel D. Sleator and Robert E. Tarjan</span>. <span class="bib-title">Self-adjusting binary search trees</span>. '
    + '<em>Journal of the ACM</em> 32(3):652–686, 1985. <span class="bib-links"><a class="bib-link" href="https://doi.org/10.1145/3828.3835">doi:10.1145/3828.3835</a></span>');
  const pre = formatReference(bib.byKey.get('demaine2009other'));
  assert.match(pre, /Erik D\. Demaine, Someone Else and A Third/);
  assert.match(pre, /Another &lt;paper&gt; &amp; more/);
  assert.match(pre, /Preprint, 2009\./);
  assert.match(pre, /href="https:\/\/arxiv\.org\/abs\/0901\.00001">arXiv:0901\.00001</);
  const veb = formatReference(bib.byKey.get('vanemdeboas1977'));
  assert.match(veb, /Peter van Emde Boas<\/span>/);
  assert.match(veb, /<span class="bib-version">Conference version: In <em>FOCS<\/em>, 1975\. <span class="bib-links"><a class="bib-link" href="https:\/\/doi\.org\/10\.1109\/SFCS\.1975\.26">/);
  assert.match(formatReference(bib.byKey.get('iacono2001')), /In <em>Proceedings of the 12th ACM-SIAM Symposium on Discrete Algorithms \(SODA\)<\/em>, pages 516–522, 2001\.$/);
});

test('cited keys of an unrendered page', () => {
  const src = [
    '# Draft',
    'Text [@a2000; @b2001] and @c2002, but not `@d2003` or me@e2004.',
    '```headline x',
    'title: T',
    'source: @f2005; @g2006',
    '',
    'Body citing [-@h2007].',
    '```',
    '```lean',
    '-- @i2008 in code',
    '```',
  ].join('\n');
  assert.deepEqual(citedKeys(src), ['a2000', 'b2001', 'c2002', 'f2005', 'g2006', 'h2007']);
});

test('the bibliography data is well formed', () => {
  const data = JSON.parse(readFileSync(join(here, '..', 'src', 'bibliography.json'), 'utf8'));
  const loaded = loadBibliography(data.entries);
  assert.deepEqual(loaded.errors, []);
  assert.ok(loaded.order.length > 50);
  // ACM's 10.5555 identifiers are not registered DOIs and cannot be checked.
  for (const e of loaded.order) {
    for (const v of [e, ...(e.versions ?? [])]) assert.ok(!v.doi?.startsWith('10.5555/'), `${e.key}: unregistered DOI ${v.doi}`);
  }
});
