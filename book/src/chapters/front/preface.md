# Binary Search Trees in Lean

<p class="lead">This book is a guided reading of <a href="https://github.com/slef/lean-bst">lean-bst</a>, a Lean 4 library of checked knowledge about binary search trees. It formalizes the standard models of BST computation and the equivalences between them, the classical bounds on request sequences together with Wilber's lower bound, and the main algorithms with their guarantees: splay trees with the theorems of Sleator and Tarjan's 1985 paper, the geometric GreedyASS with its online simulation by a BST and its weighted dynamic finger bound, the $O(\log\log n)$-competitive Tango trees, static trees searched with a lazy finger: their characterization, their place among the other bounds, and an algorithm that computes the best one; and two general transformations, one that combines two BST algorithms into one as good as the better of them on every window, and one that removes amortization, giving $O(\log n)$ worst-case time per access. Together they give one BST with the weighted dynamic finger bound, $O(\log\log n)$-competitiveness and $O(\log n)$ worst-case time at once.</p>

You know what a binary search tree is, and what a rotation does. The question this book helps you answer is narrower: *do the Lean definitions say what you think they say, and do the theorems say what the paper says?* A machine-checked proof guarantees that the statement follows from the definitions. It cannot tell you whether those are the right definitions and the right statement. Only a reader can check that, and the reading is easier with explanations next to the code.

So each definition and theorem statement in the library's public interface appears below as it was compiled. The prose between them explains what each piece models, why it is phrased the way it is, and where the formal choices differ from textbook conventions. Proofs are not explained: Lean has checked them, and you can open any of them from its code block.

If you only want to check one result, you do not need to read the book in order. Every chapter or section that proves something opens with a box that states its main result in English and in Lean. [Checking a result](checking.html) lists all of them, marks the *key results* that the formalized papers announce, and computes, for any selection of results, the few definitions you must read to trust them. The book then highlights those definitions wherever they are explained.

## How to read the Lean blocks

Here is a block, taken from the [first chapter](shapes.html):

@decl RotationBST.Tree.size

- **Hover** over any identifier, such as `Tree` or `Nat`, to see its signature and docstring, printed by Lean. The data comes from the compiler's own reference tables (the `.ilean` files), so the link points to the constant Lean actually resolved, not to a guess based on the name.
- **Click** an identifier to jump to where this book explains it. For library internals not covered here, the link opens the source on GitHub. For Lean, Std and Mathlib names, it opens the Mathlib documentation.
- The **badge** lists the kernel axioms the declaration depends on, as computed by `collectAxioms`. "No axioms" means fully constructive. Most analytic results use Lean's three standard axioms: `propext`, `Classical.choice` and `Quot.sound`. A `sorryAx` dependency, meaning an unfinished proof, would show up in red; none does.
- Theorems from the library's reading interface carry a **"statement reads only"** line, explained below.
- **show proof** expands a collapsed proof, when there is one. In the reading interface most theorems end with `:= Bridge.foo …`: the statement is spelled out in the readable file and the proof lives elsewhere.

The library and this book are built from the same sources. The build fails if a name mentioned here no longer exists, or if the compiled reference data is out of date with respect to the sources.

## The reading interface

The library is laid out as a textbook rather than by source paper: `Models/` holds the BST models and their equivalences, `Bounds/` the sequence bounds and their relations, `Classical/` the classical search trees, `Algorithms/` one directory per adaptive algorithm with its definition followed by its bounds, and `Structures/` the supporting data structures. The parts of this book follow the same order, with one exception: the tools for replaying and mirroring pointer computations live mostly under `Models/`, but they serve only the transformations at the end of [Part IV](part-algorithms.html) and the structures of [Part V](part-structures.html), so they are explained in [Chapter 30](replay.html).

Within each directory the library follows the [abstractlean](https://github.com/slef/abstractlean) convention. Every topic has a short file called `Abstract.lean` containing only definitions and theorem statements; proofs are imported through a single `AbstractBridge.lean` module, and internal lemma contracts and definitions of a proof are named `Results.lean` and `Defs.lean`. Each statements file ends with a command like

```lean
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Online.Abstract, …]
```

This command fails to compile unless every library definition mentioned in a theorem statement, directly or transitively, comes from one of the listed modules. The proofs are exempt: they may use anything. So to trust a theorem you need to read its statement and the definitions in the listed modules, and nothing else from the library. This book shows that list under every theorem, linked to the chapters where those modules are explained. [Appendix A](audit.html) describes the checks in more detail and summarizes them for all theorems.

## Conventions at a glance

These conventions hold throughout the library. Each is justified where it first appears.

| | Convention |
|---|---|
| Keys | A tree on $n$ keys stores no keys at all. Its keys are the inorder ranks $0,\dots,n-1$ ([Chapter 1](shapes.html)); arbitrary ordered keys are recovered exactly in [Chapter 4](keys.html). |
| Access | Serving request $x$ means rotating until $x$ is at the root ([Chapter 3](accesses.html)). |
| Rotation cost $R$ | The number of rotations, at any depth. No pointer movement is charged. |
| Total cost $T$ | $T = m + R$ for $m$ requests ([Chapter 5](online.html)). Without the $+m$, a request for the current root would be free. |
| Pointer cost | One per cursor move or rotation, plus one per request ([Chapter 6](pointer.html)). Within constant factors this is the same as $T$. |
| Logarithms | Base 2. `Real.logb 2` on reals, with Mathlib's convention $\log 0 = 0$; `Nat.log2` (floor) on naturals. |
| Geometric cost | One per point of an arborally satisfied set; the request points are included ([Chapter 8](geometry.html)). Up to constant factors and an additive $O(n)$, this is the same as $T$ ([Chapter 9](equivalence.html)). |
| Startup | Bounds that hold for every initial tree include an explicit additive term for it, usually $D \cdot n(1+\lfloor\log_2 n\rfloor)$. |

## Interactive figures

The figures let you rotate, search and splay, run move-to-root and GreedyASS, and watch preferred paths change. They do not imitate the algorithms: they run JavaScript transcriptions of the executable Lean definitions, one equation at a time and with the same names. The book's test suite compares these transcriptions against values computed by the Lean functions themselves, on exhaustive small cases, such as all shapes with at most six nodes, and on larger pseudo-random ones. Here is one; click any node that is not the root.

@viz rotate {"n": 9, "shape": "random", "seed": 3}

## Map of the book

The book has five parts, and each opens with an introduction that surveys it.

**[Part I · Models](part-models.html)** fixes what a BST execution is and what it costs. The basic model has unlabelled [shapes](shapes.html), [rotations](rotations.html), and [root accesses](accesses.html) charged by the number of rotations. Labelled trees on arbitrary keys correspond to it exactly ([Chapter 4](keys.html)), and [online algorithms](online.html) and dynamic optimality are defined on top of it. A model with [insertions and deletions](dictionary.html) serves the dictionaries of [Part III](part-classical.html). The standard models of the literature follow: a [single-pointer machine](pointer.html), the [touched-region model](regions.html), and the [geometric view](geometry.html), in which an execution is a set of points in the plane. Two more models serve later results: a BST with [several fingers](fingers.html), and [static linked searches](linked-search.html) in an explicit pointer memory. [Chapter 11](equivalence.html) proves that the models agree, with explicit constants, and the introduction to the part draws them on one map.

**[Part II · Bounds](part-bounds.html)** studies request sequences without reference to an algorithm. [Chapter 12](bounds.html) defines the classical benchmarks (working set, static optimality, static and dynamic finger, the unified charge, a fixed comparison tree) and proves the implications between them. The next two chapters study the *lazy finger*, a static tree in which each search starts where the previous one ended: its [characterization](lazy-finger.html) by the weighted dynamic finger bound, and its [place](lazy-finger-hierarchy.html) between static trees and dynamic BSTs. The part ends with two limits: [Wilber's interleave bound](wilber.html), a lower bound on every execution, and a [conditional-entropy benchmark](conditional-entropy.html) that no BST can meet. The introduction to the part maps all the benchmarks, the relations between them, and the algorithms that meet them.

**[Part III · Classical search trees](part-classical.html)** collects the trees that do not adapt to the requests, which are the baseline for everything after: [static trees](static-trees.html), including entropy trees and Knuth's optimal trees, [rank-balanced trees](rank-balanced.html) (AVL, red-black, WAVL), [weight-balanced trees](weight-balanced.html) (BB[α], scapegoat) and [random trees](random-trees.html) (random BSTs, treaps). Most of it is formalized; the chapters state the rest, deletions among them, in boxes marked "Not yet formalized", and the library's roadmap lists them.

**[Part IV · Adaptive algorithms](part-algorithms.html)** defines each algorithm, then proves its bounds. An algorithm with several analyses is one chapter with one section per analysis. [Move-to-root](move-to-root.html) is the simplest rule. [Splay trees](splay-trees.html) get the theorems of Sleator and Tarjan's 1985 paper. [GreedyASS](greedy-ass.html), the greedy algorithm of the geometric view, becomes an online BST and is as good as the best static lazy-finger tree. [Tango trees](tango-trees.html) are $O(\log\log n)$-competitive. Two static structures follow: a dynamic program that computes the [optimal lazy-finger tree](optimal-lazy-finger.html), and [multiple trees](multiple-trees.html) that trade space for conditional-entropy query time. The part ends with two transformations and their combination. [Combining search trees](combination.html) makes one BST as good as the better of two on every window. [Deamortization](deamortization.html) gives any online BST algorithm $O(\log n)$ worst-case cost per access, and gives a deamortized splay tree. [The last chapter](combined-finger.html) applies both to GreedyASS and Tango: Theorem 4.3 of Iacono and Langerman.

**[Part V · Structures](part-structures.html)** contains the data structures used inside proofs and algorithms: [treaps](treaps.html), [split trees](split-trees.html), [prefix sums and weighted search trees](prefix-sums.html), the [simulation of several fingers](finger-simulation.html) by one, the [replay tools](replay.html) that treat pointer computations as data, [pop-tarts](poptarts.html) and [heavy paths](heavy-path-simulation.html), which hold the source tree of the deamortization at logarithmic depth, and the [tree buffers and snapshots](tree-state.html) with which the combination saves and restores its initial tree.

**Appendices.** [Appendix A](audit.html) describes what Lean checks and what it cannot, and lists every theorem of the reading interface with its axioms. [Appendix B](declarations.html) indexes every declaration shown. [Appendix C](bibliography.html) lists the works cited, with links to their published versions and preprints.

::: note Sources
The main sources are the splay tree paper [@sleator1985]; move-to-root [@allen1978]; Wilber's lower bounds [@wilber1989]; the greedy algorithm [@lucas1988; @munro2000]; Tango trees [@demaine2007]; the geometric view, GreedyASS and the online simulation [@demaine2009]; the comparison of BST models in Derryberry's thesis [@derryberry2009]; the lazy finger [@bose2016]; the weighted dynamic finger [@iacono2016]; the multi-finger simulation, ComboBST, tree buffers and snapshots [@demaine2013]; pop-tarts, heavy-path simulation and deamortization [@bose2012]; and the potential used in the scanning proof [@kakimura2026]. The [bibliography](bibliography.html) lists every work cited, and each part ends with bibliographic notes on who proved what, and when.
:::
