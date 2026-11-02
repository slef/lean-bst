# What Lean checks

A formal library rests on a short chain of trust. This appendix spells out each link, what checks it, and what is left to the reader. The tables at the end are generated from the compiled library each time the book is built.

## The chain of trust

**1. The proofs.** Every theorem in the library is checked by Lean's kernel. The library builds with `lake build --wfail`, so warnings, including the one Lean emits for `sorry`, fail the build.

**2. The axioms.** The test target `RotationBSTTests` audits the kernel axioms of *every* declaration owned by the library, including generated helpers. It fails if anything depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, which are Lean's standard axioms and the usual foundation for classical mathematics. `sorryAx` is not among them. The badges in this book repeat that computation (`collectAxioms`) for each declaration shown.

**3. The statement boundary.** Each `Abstract.lean` file ends with `#check_bst_abstract`. It traverses the *statements* of the file's theorems, and the statements and bodies of the definitions they mention, transitively. It fails if any library declaration it reaches comes from a module outside an explicit allow-list. Proof bodies are not traversed, so proofs may use any internal lemma. It also rejects `opaque`, `partial` and `unsafe` definitions anywhere in the reading base, which could otherwise hide an unchecked behaviour behind a name. This book shows each theorem's allow-list as its "statement reads only" line.

**4. The definitions and statements.** This is the part no tool can check: whether `Access`, `workingSetSum` or `HasStaticFingerBound` mean what the literature means. The preceding chapters exist for this step. Each definition in every allow-list is shown and explained, with the subtle points collected in "Reading the Lean" boxes and the deviations from the paper in caveats.

## What this book's build checks

- Every Lean name mentioned in the text resolves to a constant that Lean exported. Renamed or deleted declarations fail the build.
- Declaration positions come from the compiler's `.ilean` files, and each is checked against the current source: the declared name must appear where the compiler recorded it. A stale build fails.
- Code blocks are cut from the compiled sources by those positions, so they cannot drift from the library.
- The figures run JavaScript transcriptions of `Splay.locate`, `Splay.splayAt`, `Splay.run`, the four update operations, `StaticTree.depth`, `workingSetNumber` and `workingSetSum`. The test suite compares them with the Lean functions evaluated by Lean, on every shape with at most six nodes and on larger random inputs.
- Coverage: the build lists every declaration of the reading interface that the book does not show.

## Deliberate non-claims

These limits are stated in the library's README and in the chapters, and are collected here for reference.

- No algorithm is proved dynamically optimal ([Chapter 6](online.html#dynamic-optimality)). The pointer-machine transfer theorems are conditional.
- The unified theorem is the 1985 fixed-finger version, not Iacono's dynamic unified bound ([Chapter 9](analysis.html#the-unified-theorem-theorem-5)).
- Updates take ranks as input. Computing the rank of a new comparison key, and a pointer machine with node allocation, are not formalized ([Chapter 10](beyond.html#updates)).
- The long-splay theorem bounds restructuring only, not search cost ([Chapter 10](beyond.html#long-splays)).
- Costs count abstract BST operations. The evaluation time of the Lean functions (which recompute subtree sizes) is not modelled, and the causal pointer transformer's planning is uncharged ([Chapter 6](online.html#running-an-online-algorithm-on-the-pointer-machine)).
- Constants are explicit but generous. For instance, the scanning bound is $14n$, not the sharper $5.5n$ of Kakimura and Terai.

## Theorems of the reading interface

@audit
