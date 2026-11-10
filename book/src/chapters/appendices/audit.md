# What Lean checks

A formal library rests on a short chain of trust. This appendix spells out each link, what checks it, and what is left to the reader. The tables at the end are generated from the compiled library each time the book is built.

## The chain of trust

**1. The proofs.** Every theorem in the library is checked by Lean's kernel. The library builds with `lake build --wfail`, so warnings, including the one Lean emits for `sorry`, fail the build.

**2. The axioms.** The test target `RotationBSTTests` audits the kernel axioms of *every* declaration owned by the library, including generated helpers. It fails if anything depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, which are Lean's standard axioms and the usual foundation for classical mathematics. `sorryAx` is not among them. The badges in this book repeat that computation (`collectAxioms`) for each declaration shown.

**3. The statement boundary.** The library separates what a reader must trust from proof engineering. Files named `Abstract.lean` are the reading interface: definitions, and theorem statements whose proofs are one-line delegations to a single `AbstractBridge.lean` import. Everything else (`Defs.lean`, `Results.lean`, proof files) is internal. Each `Abstract.lean` file that states theorems ends with `#check_bst_abstract`, wrapped in `#guard_msgs` with the number of root declarations it audits, so adding or removing a statement without updating the pin also fails the build. It traverses the *statements* of the file's theorems, and the statements and bodies of the definitions they mention, transitively. It fails if any library declaration it reaches comes from a module outside an explicit allow-list. Proof bodies are not traversed, so proofs may use any internal lemma. It also rejects `opaque`, `partial` and `unsafe` definitions anywhere in the reading base, which could otherwise hide an unchecked behaviour behind a name. This book shows each theorem's allow-list as its "statement reads only" line. Every surface allow-list names only `Abstract` modules, so every definition a surface statement reaches is quoted somewhere in this book; the build fails if a chapter quotes or links a declaration from outside the reading interface.

**4. The definitions and statements.** This is the part no tool can check: whether `Access`, `workingSetSum` or `HasStaticFingerBound` mean what the literature means. The preceding chapters exist for this step. Each definition in every allow-list is shown and explained, with the subtle points collected in "Reading the Lean" boxes and the deviations from the paper in caveats.

## What this book's build checks

- Every Lean name mentioned in the text resolves to a constant that Lean exported. Renamed or deleted declarations fail the build.
- Declaration positions come from the compiler's `.ilean` files, and each is checked against the current source: the declared name must appear where the compiler recorded it. A stale build fails.
- Code blocks are cut from the compiled sources by those positions, so they cannot drift from the library.
- The figures run JavaScript transcriptions of the executable Lean definitions: `Splay.locate`, `Splay.splayAt`, `Splay.run`, the four update operations, `moveToRoot`, `Tree.depth`, `workingSetNumber` and `workingSetSum`; the GreedyASS sweep and the arboral-satisfaction test; Wilber's interleave quantity, Tango's preference counts and preferred paths; and the 2–3–4 split-tree views. The test suite compares them with the Lean functions evaluated by Lean, on every shape with at most six nodes and on larger pseudo-random inputs.
- Coverage: the build lists every declaration of the reading interface that the book does not show.

## Deliberate non-claims

These limits are stated in the library's README and in the chapters, and are collected here for reference.

- No algorithm is proved dynamically optimal ([Chapter 5](online.html#dynamic-optimality)), neither splaying nor GreedyASS. The theorem about GreedyASS is that each row is the unique minimum *local* completion ([Chapter 16](greedy.html)), not that the whole execution is near-optimal. The pointer-machine transfer theorems are conditional.
- The unified theorem is the 1985 fixed-finger version, not Iacono's unified bound. The dynamic finger bound is proved for GreedyASS, not for splay trees ([Chapter 10](bounds.html#what-is-not-formalized)).
- Of Wilber's two lower bounds, only the first, the interleave bound, is formalized ([Chapter 11](wilber.html)).
- Tango's auxiliary trees are splay trees rather than the red-black trees of the original paper, so its bound is amortized over the sequence ([Chapter 19](tango.html)).
- The constants of the geometric simulation (6018, 192593, …) and of the geometric equivalences are explicit but not sharp ([Chapter 17](simulation.html)).
- Updates take ranks as input. Computing the rank of a new comparison key, and a pointer machine with node allocation, are not formalized ([Chapter 15](beyond.html#updates)).
- The long-splay theorem bounds restructuring only, not search cost ([Chapter 15](beyond.html#long-splays)).
- Costs count abstract BST operations. The evaluation time of the Lean functions (which recompute subtree sizes) is not modelled, and the causal pointer transformer's planning is uncharged ([Section 6.6](pointer.html#running-an-online-algorithm-on-the-pointer-machine)). The same holds for the planning of the geometric simulation and of Tango.
- The GreedyASS finger bounds cover Theorems 3.1, 4.1, 4.2 and Corollary 1 of Iacono and Langerman. Theorem 4.3 is formalized as an abstract BST-operation statement in [Chapter 38](combined-finger.html). The BST and pointer-machine forms state that *some* online algorithm meets the bound; that it is the simulation of GreedyASS is visible in the proof, not in the statement ([Chapter 23](greedy-finger.html)).
- Of the lazy-finger paper, the nine numbered results are formalized, but not the unnumbered periodic-rebuilding analysis or the concluding conjecture. The conditional-entropy obstruction is stated for every BST execution in the pointer model; the lazy-finger form follows by combining it with the simulation of [Chapter 15](lazy-finger-hierarchy.html), a step done in the text, not in Lean ([Chapter 16](conditional-entropy.html)).
- The optimizer's cubic work bound is stated in an annotated cost model whose charges are written by hand next to the code, not measured ([Chapter 29](optimal-lazy-finger.html)). The query bound of the multiple-tree structure excludes preprocessing, which reads the whole sequence ([Chapter 30](multiple-trees.html)).
- ComboBST ([Chapter 23](combination.html)) and the deamortization ([Chapter 37](deamortization.html)) are formalized for abstract BST operations. Not formalized: the storage and private-computation clauses (the paper's Theorems 3 and 5 of *Combining binary search trees* and Theorem 7 of *De-amortizing binary search trees*), the $O(k)$ overhead for families of $k$ structures, and the concrete applications other than Splay, GreedyASS and Tango (Cole's dynamic finger, key-independent optimality, multi-splay trees). The combined policies are chosen with classical choice, and their planning is not charged.
- The general combination theorem assumes that its two input workers are well-behaved ([Chapter 33](combining.html)); this is an operational hypothesis, proved in the library for the GreedyASS and Tango workers of [Chapter 38](combined-finger.html), not for arbitrary algorithms.
- The classical trees of [Part III](part-classical.html) are formalized in part. Rank-balanced trees have their heights and WAVL/AVL insertion, but no deletion and no red-black insertion ([Chapter 19](rank-balanced.html#what-is-not-formalized)). Weight-balanced trees have their height bound, rebuilding and scapegoat trees, but not BB[α] rebalancing ([Chapter 20](weight-balanced.html)). Random trees have expected depths, but not treap updates by rotations ([Chapter 21](random-trees.html)). Knuth's algorithm counts examined roots, and rebuilding counts rotations; neither is a running time in a machine model ([Chapter 18](static-trees.html#knuth-s-algorithm)).
- Constants are explicit but generous. For instance, the scanning bound is $14n$, not the sharper $5.5n$ of Kakimura and Terai [-@kakimura2026].

## Theorems of the reading interface

@audit
