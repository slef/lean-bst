# Binary Search Trees in Lean: the book

An interactive online textbook documenting the `RotationBST` library. Each definition and theorem statement of the library's reading interface is shown as compiled, with hoverable and hyperlinked identifiers, axiom badges, and the statement boundary checked by `#check_bst_abstract`. Explanations are interleaved, and the interactive figures run JavaScript transcriptions of the Lean algorithms, tested against Lean.

## Build

```sh
lake build                       # in the repository root: the book reads the .ilean files
cd book
npm ci
npm run extract                  # Lean → build/lean-data.json, build/vectors.json
npm run build                    # → dist/
npm test                         # JavaScript ports against values computed by Lean
npm run lint                     # coherence of the sources (numbers, citations, roadmap, figures, coverage)
npm run check:pages              # every built page in headless Chromium
npm run check                    # build, lint, test and check:pages together: run before every commit
npm run verify:bib               # changed bibliography entries against Crossref, DataCite and arXiv
npm run serve                    # http://localhost:8000
```

`npm run extract` reads the compiled library of the checkout in `LEAN_ROOT` (default: the parent directory) and runs `lean/Export.lean` through `lake env lean`. It fails if the `.ilean` files are stale with respect to the sources. `BOOK_DIST` changes the output directory of `build` and `serve`. CI (`.github/workflows/book.yml`) builds the library and the book, runs the lint, the tests and the page check, and publishes `dist/` to GitHub Pages. What each check covers, and the process for every kind of change, is in [docs/maintaining-the-book.md](../docs/maintaining-the-book.md).

## Layout

| Path | Contents |
|---|---|
| `src/book.json` | Title, repository URL, KaTeX macros, and the order of the pages: front matter, parts (each with an introduction page, its chapters, a chapter possibly with sections on pages of their own, and an optional unnumbered `notes` page that ends the part), appendices. Numbers and appendix letters are assigned by the build. |
| `src/bibliography.json` | The bibliography: every work the book cites (see [Citations](#citations)) |
| `src/chapters/<part>/*.md` | One file per page, named by its slug (Markdown with the directives below) |
| `src/assets/` | Stylesheet, page scripts (`book.js`; `checking.js` for reading paths), and the figures in `viz/` |
| `lean/Export.lean` | Exports signatures, docstrings, axioms, declaration ranges, dependencies and test vectors |
| `scripts/extract.mjs` | Collects `.ilean` reference data and the export into `build/lean-data.json` |
| `scripts/build.mjs`, `scripts/lean-html.mjs` | Static site generator and Lean highlighter |
| `scripts/bibliography.mjs` | Citation syntax, labels and formatted references (tested by `test/bibliography.test.mjs`) |
| `test/*.test.mjs` | Check the JavaScript ports in `src/assets/viz/` against vectors computed by Lean, and the citation parser and renderer |

## Writing

Chapters are Markdown with KaTeX math (`$…$`, `$$…$$`) and these additions:

- `@decl Name …` on its own line shows the compiled source of one or more declarations. Its first occurrence is the declaration's home, which every other link to the declaration targets. Use `@stmt Name` to collapse a tactic proof behind a toggle.
- `[[Name]]` or `[[Name|text]]` is an inline hoverable reference (write `[[Name\|text]]` inside a table cell).
- `@viz kind {json}` mounts the figure implemented by `src/assets/viz/<kind>.js`, whose default export receives the container and the options; the build fails if the module does not exist. Figures are built on shared helpers (`tree.js` for the ports of the tree algorithms, `render.js` for drawing trees, `ui.js` for controls), and the options of each figure are read at the top of its module.
- Cross-references whose link text is `Chapter N`, `Section N.M`, `Part I` or `Appendix X`, such as `[Chapter 3](accesses.html)` or `[Section 4.2](keys.html#the-textbook-invariant)`, are renumbered from their target when the book is built, so the number written in the source does not matter. A link to a page that is a section of a chapter reads `Section N.k`, whichever word the source used. Other link texts are left alone. Outside links, for instance in code blocks, write `{{ref:slug}}` for the label of a page (`Chapter 24`, `Section 23.2`) and `{{num:slug}}` for its number.
- A chapter with sections on their own pages is a short overview; its own headings are not numbered.
- `::: check`, `::: caveat`, `::: note Title`, `::: exercise Title`, `::: details Title` are callouts.
- `@audit` and `@index` generate the appendix tables.
- Citations are written `[@key]`, `[@a; @b]`, `[@key, Theorem 3]`, `[-@key]` (the year only, after the authors are named) or `@key` in running text; see [Citations](#citations).
- A fenced block ```` ```headline id ```` states a chapter's main result, as a box at the top of the chapter. Header lines come first: `title:`, optional `source:` (the papers, as citation keys: `source: @sleator1985; @iacono2001`), `key: yes` for results announced in a formalized paper's abstract or introduction, `theorems:` (the Lean theorems that together establish the result; each must also be shown with `@decl` or `@stmt` somewhere), and any number of `skip: Name | reason`. Then a blank line and the statement in English. Display math needs blank lines around it.
- `@claims` lists the main results, on the checking page.

Each main result has a *reading path*: the library definitions its statements mention, then, recursively, the definitions those mention in their types and bodies. Proofs are never followed. `lean/Export.lean` exports these dependencies (`deps` in `build/lean-data.json`), mapping constructors, recursors and projections back to their types. A `skip` cuts the path at a constant, or at a structure field written `Structure.field`, that a reader can safely ignore, for example a correctness obligation of a structure whose existence a listed theorem proves. Every skip needs a stated reason, which the reading list shows, and the build fails on skips that cut nothing. The paths are written to `dist/assets/claims.json`; `src/assets/checking.js` uses them to highlight what to read across pages.

Names may be fully qualified or any unambiguous suffix. Library names must come from `*.Abstract` modules, the reading interface: the build fails if a chapter quotes or links an internal declaration (write it as plain code instead). The build also fails on unknown names, unknown figures, KaTeX errors, broken internal links and cross-references it cannot number, and it lists the reading-interface declarations that no chapter shows.

## Citations

Every work the book cites has one entry in `src/bibliography.json`, an object whose `entries` array holds records like this one:

```json
{
  "key": "sleator1985",
  "type": "article",
  "authors": ["Daniel D. Sleator", "Robert E. Tarjan"],
  "title": "Self-adjusting binary search trees",
  "venue": "Journal of the ACM",
  "volume": "32", "number": "3", "pages": "652–686",
  "year": 1985,
  "doi": "10.1145/3828.3835",
  "url": "https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf",
  "versions": [
    { "label": "Preliminary version, “Self-adjusting binary trees”", "type": "inproceedings",
      "venue": "Proceedings of the 15th Annual ACM Symposium on Theory of Computing (STOC)",
      "pages": "235–245", "year": 1983, "doi": "10.1145/800061.808752" }
  ]
}
```

- `key`: lowercase letters, the year, then optional lowercase letters to tell works apart (`demaine2009`, `cole2000proof`).
- `type`: `article`, `inproceedings`, `incollection`, `book`, `phdthesis`, `mastersthesis`, `techreport`, `preprint` or `misc`. An article prints as *venue* volume(number):pages; a paper in proceedings as "In *venue*, pages …".
- `authors`: full names, `"Given Family"`, or `"Family, Given"` when the family name has several words (`"van Emde Boas, Peter"`). The family name is the last word otherwise.
- `title`, `year`, and `venue` (the journal, the proceedings, the institution of a thesis or report; not needed for a `preprint`); optional `volume`, `number`, `pages`, `publisher`, `note`.
- Links: `doi` (without `https://doi.org/`), `arxiv` (the bare identifier) and `url`, in that order of preference. Every DOI and arXiv identifier must be checked against doi.org, Crossref, DBLP or arxiv.org before it is added; when no link can be verified, leave it out.
- `versions`: other versions of the same work, such as a conference version or a preliminary paper with another title. Each has a `label`, a `type`, a `venue`, a `year` and optional pages and links. The entry itself is the version to cite, usually the journal version, and its `year` is the year in the label.

Labels are computed: "Wilber 1989" for one author, "Sleator and Tarjan 1985" for two, "Demaine et al. 2009" for more. Two entries whose labels would coincide get the suffixes a, b, … in bibliography order.

In a chapter:

| Source | Renders as |
|---|---|
| `[@sleator1985]` | (Sleator and Tarjan 1985) |
| `[@sleator1985; @iacono2001]` | (Sleator and Tarjan 1985; Iacono 2001) |
| `[@sleator1985, Theorem 5]` | (Sleator and Tarjan 1985, Theorem 5) |
| `Sleator and Tarjan [-@sleator1985]` | Sleator and Tarjan (1985) |
| `@sleator1985 conjectured` | Sleator and Tarjan (1985) conjectured |
| `source: @sleator1985; @iacono2001` (headline) | Sleator and Tarjan 1985; Iacono 2001 |

Each citation links to the entry on the Bibliography page (`@bibliography`, Appendix C), and hovering or focusing it shows the full reference with its DOI and preprint links; Tab moves into the card. The Bibliography lists the works cited by the pages in `book.json`, sorted by author, with links back to the first citation on each page. The build fails on an unknown key, on a malformed citation, on a headline `source:` that is not a list of keys, and on an entry that no page cites. Pages under `src/chapters` that `book.json` does not list yet, such as drafts waiting to be merged, are checked too: their keys must exist, and they count as citing the entries they use, but they are not rendered.

Each part ends with a page of bibliographic notes (`notes` in `book.json`, file `<part>/notes.md`): who proved what, and when, with pointers to the chapters, and the related results that the book does not cover.

