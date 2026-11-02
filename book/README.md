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
| `src/book.json` | Title, repository URL, chapter order, KaTeX macros |
| `src/chapters/*.md` | Chapters (Markdown with the directives below) |
| `src/assets/` | Stylesheet, page script, and the figures in `viz/` |
| `lean/Export.lean` | Exports signatures, docstrings, axioms, declaration ranges and test vectors |
| `scripts/extract.mjs` | Collects `.ilean` reference data and the export into `build/lean-data.json` |
| `scripts/build.mjs`, `scripts/lean-html.mjs` | Static site generator and Lean highlighter |
| `test/port.test.mjs` | Checks `src/assets/viz/tree.js` against Lean |

## Writing

Chapters are Markdown with KaTeX math (`$…$`, `$$…$$`) and these additions:

- `@decl Name …` on its own line shows the compiled source of one or more declarations. Its first occurrence is the declaration's home, which every other link to the declaration targets. Use `@stmt Name` to collapse a tactic proof behind a toggle.
- `[[Name]]` or `[[Name|text]]` is an inline hoverable reference.
- `@viz kind {json}` mounts a figure: `shape`, `rotate`, `splay`, `pointer`, `workingset`, `experiment` or `updates`. The options are read at the top of each module in `src/assets/viz/`.
- `::: check`, `::: caveat`, `::: note Title`, `::: exercise Title`, `::: details Title` are callouts.
- `@audit` and `@index` generate the appendix tables.

Names may be fully qualified or any unambiguous suffix. The build fails on unknown names, KaTeX errors and broken internal links, and it lists the reading-interface declarations that no chapter shows.
