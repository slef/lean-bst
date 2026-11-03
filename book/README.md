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
npm run serve                    # http://localhost:8000
```

`npm run extract` reads the compiled library of the checkout in `LEAN_ROOT` (default: the parent directory) and runs `lean/Export.lean` through `lake env lean`. It fails if the `.ilean` files are stale with respect to the sources. `BOOK_DIST` changes the output directory of `build` and `serve`. CI (`.github/workflows/book.yml`) builds the library and the book and publishes `dist/` to GitHub Pages.

## Layout

| Path | Contents |
|---|---|
| `src/book.json` | Title, repository URL, chapter order (with parts, numbers and appendix letters), KaTeX macros |
| `src/chapters/*.md` | Chapters (Markdown with the directives below) |
| `src/assets/` | Stylesheet, page scripts (`book.js`; `checking.js` for reading paths), and the figures in `viz/` |
| `lean/Export.lean` | Exports signatures, docstrings, axioms, declaration ranges, dependencies and test vectors |
| `scripts/extract.mjs` | Collects `.ilean` reference data and the export into `build/lean-data.json` |
| `scripts/build.mjs`, `scripts/lean-html.mjs` | Static site generator and Lean highlighter |
| `test/*.test.mjs` | Check the JavaScript ports in `src/assets/viz/` against vectors computed by Lean |

## Writing

Chapters are Markdown with KaTeX math (`$…$`, `$$…$$`) and these additions:

- `@decl Name …` on its own line shows the compiled source of one or more declarations. Its first occurrence is the declaration's home, which every other link to the declaration targets. Use `@stmt Name` to collapse a tactic proof behind a toggle.
- `[[Name]]` or `[[Name|text]]` is an inline hoverable reference (write `[[Name\|text]]` inside a table cell).
- `@viz kind {json}` mounts the figure implemented by `src/assets/viz/<kind>.js`, whose default export receives the container and the options; the build fails if the module does not exist. Figures are built on shared helpers (`tree.js` for the ports of the tree algorithms, `render.js` for drawing trees, `ui.js` for controls), and the options of each figure are read at the top of its module.
- Cross-references whose link text is `Chapter N`, `Section N.M` or `Appendix X`, such as `[Chapter 3](accesses.html)` or `[Section 4.2](keys.html#the-textbook-invariant)`, are renumbered from their target when the book is built, so the number written in the source does not matter. Other link texts are left alone.
- `::: check`, `::: caveat`, `::: note Title`, `::: exercise Title`, `::: details Title` are callouts.
- `@audit` and `@index` generate the appendix tables.
- A fenced block ```` ```headline id ```` states a chapter's main result, as a box at the top of the chapter. Header lines come first: `title:`, optional `source:` (the paper), `key: yes` for results announced in a formalized paper's abstract or introduction, `theorems:` (the Lean theorems that together establish the result; each must also be shown with `@decl` or `@stmt` somewhere), and any number of `skip: Name | reason`. Then a blank line and the statement in English. Display math needs blank lines around it.
- `@claims` lists the main results, on the checking page.

Each main result has a *reading path*: the library definitions its statements mention, then, recursively, the definitions those mention in their types and bodies. Proofs are never followed. `lean/Export.lean` exports these dependencies (`deps` in `build/lean-data.json`), mapping constructors, recursors and projections back to their types. A `skip` cuts the path at a constant, or at a structure field written `Structure.field`, that a reader can safely ignore, for example a correctness obligation of a structure whose existence a listed theorem proves. Every skip needs a stated reason, which the reading list shows, and the build fails on skips that cut nothing. The paths are written to `dist/assets/claims.json`; `src/assets/checking.js` uses them to highlight what to read across pages.

Names may be fully qualified or any unambiguous suffix. Library names must come from `*.Abstract` modules, the reading interface: the build fails if a chapter quotes or links an internal declaration (write it as plain code instead). The build also fails on unknown names, unknown figures, KaTeX errors, broken internal links and cross-references it cannot number, and it lists the reading-interface declarations that no chapter shows.
