# Maintaining the book

The book (`book/`, published at https://slef.github.io/lean-bst/) grows by
many small changes, made by people and by agents. This document is the process
that keeps it coherent: the rules every change follows, the checks to run, and
the checklists for the common kinds of change. `book/README.md` documents the
authoring syntax; this document is about keeping the whole consistent.

## Principles

- **The book is a textbook.** It collects what is known about binary search
  trees. Where several classical results are instances of one theory, present
  the theory once and the results as instances. Original papers appear as
  sources, not as the structure of the text.
- **A result is formalized only if a Lean declaration shown in the book
  proves it.** Everything else is stated in a `::: todo` box ("Not yet
  formalized") that links to its entry in `ROADMAP.md`. In a figure it is a
  dashed (`todo`) node or edge. In a table its status says "not yet formalized".
- **Never overclaim.** Statements match the Lean statements, including
  hypotheses, constants and startup terms. Results from the literature are
  attributed to their authors. Papers by the repository owner are described
  like all others.
- **Unformalized results go to the roadmap, not into proofs.** Book authors add
  a `ROADMAP.md` entry (source, target Lean statement, where it goes, what to
  change in the book). The prover picks entries up from there.
- **Numbers are never written by hand.** Chapter, section, part and appendix
  numbers are assigned by the build. Refer to them with links (`[Chapter 3](accesses.html)`,
  `[Part II](part-bounds.html)`), or `{{ref:slug}}` / `{{num:slug}}` in code and
  table cells. A section of a *paper* stays plain text and says whose it is
  ("Section 4 of the paper", or next to a citation).
- **Every citation uses the bibliography.** `[@key]`, `@key` or `source: @key`,
  with entries in `book/src/bibliography.json`. A DOI, arXiv id or URL is
  added only after it has been checked.
- **Plain style.** Short sentences, one idea each, no hype. Say what a
  definition does before how.

## Checks

Run all of them before every commit that touches the book:

```sh
cd book
npm run check          # build, lint, unit tests, pages in a browser
npm run verify:bib     # only if bibliography.json changed (needs network)
```

| Check | Command | What it catches |
|---|---|---|
| Build | `npm run build` | Unknown or internal Lean names; `@decl` without source; bad headline blocks (sources, theorems, skips); KaTeX errors; links to missing pages or anchors; cross-references that cannot be numbered; unknown, malformed or uncited bibliography keys; unknown figures; bad figure JSON. Warns about reading-interface declarations that no chapter shows. |
| Lint | `npm run lint` | Chapter, part, appendix or book-section numbers written in plain text; citations written by hand; an author named right before `[@key]` (the name would appear twice); a key cited twice in one sentence; a key whose year differs from its entry's year; articles without pages; links to missing `ROADMAP.md` entries; `todo` boxes without a roadmap link; roadmap entries naming book files that do not exist; roadmap targets that now exist in Lean (the entry may be done); library names in roadmap target statements that do not exist; figure nodes and edges naming theorems that their page never links (the figure link would be dead), or pages and anchors that do not exist; `todo` figure items without a roadmap option; table rows whose status cell says "not formalized" but that link a Lean declaration; phrases that record a gap ("not stated as one Lean theorem", "has no Lean definition", …), unless the paragraph is marked `<!-- known gap -->`; roadmap entries whose lettered items do not start at (a); part introductions and the preface map that miss a chapter; "has N parts" in the preface; files under `chapters/` that `book.json` does not list. `--verbose` also lists chapters that a part's notes do not mention. |
| Unit tests | `npm test` | The ports of the tree algorithms used by figures, and the bibliography parser and renderer. |
| Pages | `npm run check:pages` | In headless Chromium, every page: JavaScript errors, failed requests, figures that draw nothing, KaTeX errors, citations without reference data. Skips with a message when no Chromium is found (set `CHROME_PATH`); CI runs it with `--require`. |
| Bibliography | `npm run verify:bib` | For entries changed since `HEAD` (or `-- --all`, or `-- key …`): each DOI resolves on Crossref or DataCite, each arXiv id on arxiv.org, to a work with the same title and first author; every other URL answers. |
| CI | push to `main` | Workflows "Lean" (library and snippets), "Documentation" (the LaTeX description), and "Book" (build, lint, tests, pages, then deployment). |

The lint, the build and the page check are cheap: run them after every edit,
not only before committing. Fix warnings too, so that new ones stand out.

## Workflow

1. Work on a branch in its own worktree (`git worktree add ../lean-bst-<topic> -b <topic> main`).
   Link `book/build/` from a checkout where `npm run extract` has run, or run it.
2. Make the change, following the checklist for its kind below.
3. Run `npm run check` (and `npm run verify:bib` if references changed).
4. For a substantial content change, have it reviewed by someone who did not
   write it (a person or a separate agent), with the review brief below.
5. Commit as the repository owner's identity, then merge into `main` only when
   asked. After pushing, wait for the three workflows and look at the live page.

## Checklists

### A new chapter or section

- Add it to `book/src/book.json`: a chapter, or a `children` entry of one.
- Write the page under `book/src/chapters/<part>/<slug>.md`. Each headline
  result goes in a `headline` block with `source:` keys and `theorems:`.
- Mention it in the part introduction (`part-*.md`, its table or list) and in
  the preface's "Map of the book" if it is a chapter. The lint warns otherwise.
- Add its history to the part's `notes.md`, with citations.
- If it introduces a bound, an algorithm meeting a bound, or a model: add it
  to the map of the bounds (`assets/viz/boundsmap.js`, and the tables in
  `bounds/part-bounds.md`) or the map of the models (`assets/viz/modelsmap.js`,
  and the tables in `models/part-models.md`). Every theorem a figure names must
  be linked as `[[Name]]` on the same page.
- If it states results that are not formalized: `::: todo` boxes, a roadmap
  entry for each, and dashed figure items.
- If it needs a new Lean directory, record it in `docs/organization.md`.

### A roadmap entry that has been formalized

The lint warns when a target name of an entry exists in the library. Then:

- Replace the `::: todo` box with `@decl` blocks and a `headline` block.
- In the figures, remove `todo: true` and add `thms`, linked on the page.
- Update the status columns: `classical/part-classical.md`, the algorithm
  tables of `bounds/part-bounds.md`, and the "What is not formalized" sections.
- Delete the entry from `ROADMAP.md` and fix links to it (the lint finds them).

### A result that is not formalized

- A `::: todo` box with the statement and a link to its roadmap entry.
- A `ROADMAP.md` entry: **Source**, **Statement** (a Lean target in the
  library's conventions), **Where**, **Book**. Hard results go under
  "Stretch goals".
- If it belongs in a figure, a dashed node or edge, and its text says it is not
  formalized.

### A new reference

- Add the entry to `book/src/bibliography.json` (schema in `book/README.md`),
  with a DOI or arXiv id only if it resolves to the same work. Take every
  field (authors, venue, volume, pages, year) from Crossref, DataCite, arXiv or
  the publisher's page, never from memory. The key's year is the entry's year,
  which is the year of the version cited; earlier versions go in `versions`,
  and prose that dates a result by its first version says so ("at FOCS 2004").
- Run `npm run verify:bib`. Leave out any link that cannot be verified.
- Cite it at least once; the build fails on uncited entries.

### Reordering or renaming

- Move entries in `book.json`; links and numbers follow automatically.
- Look for prose that depends on order or counts: "the next chapter", "the
  first three chapters", "the last five", "has five parts" (only the last is
  checked automatically).
- A renamed slug breaks links to it: the build reports each one.

### After a change to the Lean library

- The build fails on any shown declaration that disappeared or moved out of an
  `Abstract.lean` file; follow the rename.
- Its coverage warning lists reading-interface declarations no chapter shows:
  each should be shown, or be deliberately internal.

## What no script checks

Some coherence needs a reader. For every substantial change, and periodically
for the whole book:

- Mathematical and historical claims against the sources: constants,
  hypotheses, attributions, years.
- Overclaiming: "formalized", "proves" and "the library shows" only next to a
  shown declaration; status columns that match the `todo` boxes.
- That a verb in a headline ("computes a tree", "builds", "runs in time") is
  backed by a theorem about the function's actual output: a function that
  returns a cost does not compute a tree.
- Units: heights count nodes, depths count edges; "from the empty tree"
  restrictions on amortized bounds.
- That `[@key]` cites the paper the sentence means, and that what the
  sentence says the paper did is what the paper did (read its abstract).
- That one concept has one definition everywhere it appears: the chapter,
  the part introduction's table, the figure's label, the roadmap.
- That a status ("formalized", "partly formalized") in a table matches what
  the shown declarations prove, not what nearby lemmas prove.
- Order-dependent prose ("next", "previous", "the first three").
- Duplicated or contradictory statements between chapters.
- `ROADMAP.md` target statements: correct mathematics, names that exist.

### Review brief

When asking a separate agent for a review, give it the repository path and the
commits to read, say that it must not edit anything, and ask for findings
ranked as *error* (false or overclaimed), *inconsistency* or *minor*, each with
`file:line`, a quote, the evidence, and a suggested fix. Point it to this
document and to `book/README.md` for the conventions. List the topics above.
Ask it to end with the systematic problems it saw, so that new checks can be
added to `book/scripts/lint.mjs`.

## Improving the checks

When a review finds a mistake that a pattern could have caught, add the
pattern to `book/scripts/lint.mjs`, and a line to the table above. Keep the
lint free of false positives: a check that is often wrong gets ignored.
