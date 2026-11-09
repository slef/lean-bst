# lean-bst

A Lean 4 library on binary search trees and a literate textbook built from it (`book/`).

- Library layout and where new results go: `docs/organization.md`.
- Results the book states but the library does not prove yet: `ROADMAP.md`. Book authors add entries there; they do not prove them.
- Any change to the book follows `docs/maintaining-the-book.md`. Before committing, run `cd book && npm run check`, and also `npm run verify:bib` when `book/src/bibliography.json` changed. Authoring syntax: `book/README.md`.
