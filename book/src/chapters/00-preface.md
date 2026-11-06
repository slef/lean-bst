# Binary Search Trees in Lean

<p class="lead">This book is a guided reading of <a href="https://github.com/slef/lean-bst">lean-bst</a>, a Lean 4 library of checked knowledge about binary search trees. It formalizes the standard models of BST computation and the equivalences between them, the classical bounds on request sequences together with Wilber's lower bound, and the main algorithms with their guarantees: splay trees with the theorems of Sleator and Tarjan's 1985 paper, the geometric GreedyASS with its online simulation by a BST and its weighted dynamic finger bound, the $O(\log\log n)$-competitive Tango trees, static trees searched with a lazy finger: their characterization, their place among the other bounds, and an algorithm that computes the best one; and two general transformations, one that combines two BST algorithms into one as good as the better of them on every window, and one that removes amortization, giving $O(\log n)$ worst-case time per access. Together they give one BST with the weighted dynamic finger bound, $O(\log\log n)$-competitiveness and $O(\log n)$ worst-case time at once.</p>

You know what a binary search tree is, and what a rotation does. The question this book helps you answer is narrower: *do the Lean definitions say what you think they say, and do the theorems say what the paper says?* A machine-checked proof guarantees that the statement follows from the definitions. It cannot tell you whether those are the right definitions and the right statement. Only a reader can check that, and the reading is easier with explanations next to the code.

So each definition and theorem statement in the library's public interface appears below as it was compiled. The prose between them explains what each piece models, why it is phrased the way it is, and where the formal choices differ from textbook conventions. Proofs are not explained: Lean has checked them, and you can open any of them from its code block.

If you only want to check one result, you do not need to read the book in order. Every chapter that proves something opens with a box that states its main result in English and in Lean. [Checking a result](checking.html) lists all of them, marks the *key results* that the formalized papers announce, and computes, for any selection of results, the few definitions you must read to trust them. The book then highlights those definitions wherever they are explained.

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

The library is laid out as a textbook rather than by source paper: `Models/` holds the BST models and their equivalences, `Bounds/` the sequence bounds and their relations, `Algorithms/` one directory per algorithm with its definition followed by its bounds, and `Structures/` the supporting data structures. The four parts of this book follow the same order.

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

**Part I · Models** fixes what a BST execution is and what it costs. The basic model has unlabelled [shapes](shapes.html), [rotations](rotations.html), and [root accesses](accesses.html) charged by the number of rotations. Labelled trees on arbitrary keys correspond to it exactly ([Chapter 4](keys.html)). [Online algorithms](online.html) and dynamic optimality are defined on top of it. Three further models are standard in the literature: a [single-pointer machine](pointer.html), the [touched-region model](regions.html), in which a request pays for a rooted subtree that it rearranges, and the [geometric view](geometry.html), in which an execution is a set of points in the plane. [Chapter 9](equivalence.html) collects the theorems relating all of them, with explicit constants. Two more models serve later chapters: a BST with [several fingers](fingers.html), and [static linked searches](linked-search.html) in an explicit pointer memory. [Chapter 12](replay.html) adds the bookkeeping that the combination and deamortization chapters need: replayed instruction streams, detours, mirror images, depth invariants along a computation, and per-node fields.

**Part II · Bounds** studies request sequences without reference to an algorithm. [Chapter 10](bounds.html) defines the classical upper-bound benchmarks (working set, static optimality, static finger, the unified charge, a fixed comparison tree) and proves the implications between them. [Chapter 11](wilber.html) proves Wilber's interleave lower bound, which holds for every execution in the rotation, pointer and geometric models. The next three chapters study the *lazy finger*, a static tree in which each search starts where the previous one ended: its [characterization](lazy-finger.html) by the weighted dynamic finger bound, its [place](lazy-finger-hierarchy.html) between static trees and dynamic BSTs, and an [entropy obstruction](conditional-entropy.html) that no static search with a lazy finger can beat.

**Part III · Algorithms** defines each algorithm, then proves its bounds. [Move-to-root](move-to-root.html) is the simplest rule and the witness behind the existence results. Splaying takes three chapters: the [algorithm](splay.html), the [amortized analysis](analysis.html) with Theorems 1–5 of the paper, and [updates, long splays, the snapshot theorem and sequential access](beyond.html). [GreedyASS](greedy.html) is the greedy algorithm of the geometric view, and [Chapter 17](simulation.html) turns any online geometric algorithm into an online BST algorithm. Four chapters then prove that GreedyASS is as good as the [best static lazy-finger tree](greedy-finger.html), and so has the weighted dynamic finger property, through a [reference forest](reference-forest.html), a [colored potential](greedy-potential.html) and a [row-by-row amortized analysis](greedy-amortized.html). [Preferred paths](preferred-paths.html) and [Tango trees](tango.html) give an $O(\log\log n)$-competitive BST, and a bottom-up variant has a [linear startup term](tango-linear.html). Two static structures follow: a dynamic program that computes the [optimal lazy-finger tree](optimal-lazy-finger.html), and [multiple trees](multiple-trees.html) that trade space for conditional-entropy query time. The part ends with two transformations and their combination. [Combining search trees](combining.html) and the three chapters after it run two BST algorithms side by side, in alternating rounds of [interruptible workers](combo-workers.html), as [one online execution](combo-online.html); [Deamortization](deamortization.html) turns any online BST algorithm into one with $O(\log n)$ worst-case cost per access, and gives a deamortized splay tree. [The last chapter](combined-finger.html) combines GreedyASS with Tango and deamortizes the result: Theorem 4.3 of Iacono and Langerman.

**Part IV · Structures** contains the data structures used inside proofs and algorithms: [treaps](treaps.html), which convert geometric solutions into BST executions and, with random priorities, give a good lazy-finger tree; [split trees](split-trees.html), which implement the online simulation; [prefix sums and weighted search trees](prefix-sums.html), used by the optimizer and the multiple-tree structure; [BST deques, tendons](bst-deques.html) and [finger hands](finger-hands.html), which let one BST simulate several fingers; [pop-tarts](pop-tarts.html), [Chocolate pop-tarts](chocolate.html) and four chapters on [heavy paths](heavy-paths.html), which hold the source tree of the deamortization at logarithmic depth; and [tree buffers](tree-buffers.html) and [snapshots](snapshots.html), with which the combination saves and restores the tree of each algorithm.

**Appendices.** [Appendix A](audit.html) describes what Lean checks and what it cannot, and lists every theorem of the reading interface with its axioms. [Appendix B](declarations.html) indexes every declaration shown.

::: note Sources
D. D. Sleator and R. E. Tarjan, [*Self-Adjusting Binary Search Trees*](https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf), JACM 32(3), 1985. B. Allen and I. Munro, *Self-organizing binary search trees*, JACM 25(4), 1978. R. Wilber, *Lower bounds for accessing binary search trees with rotations*, SIAM J. Comput. 18(1), 1989. J. Lucas, *Canonical forms for competitive binary search tree algorithms*, Rutgers technical report, 1988, and I. Munro, *On the competitiveness of linear search*, ESA 2000, for the greedy algorithm. E. D. Demaine, D. Harmon, J. Iacono and M. Pătraşcu, *Dynamic optimality—almost*, FOCS 2004 / SIAM J. Comput. 2007, for Tango trees. E. D. Demaine, D. Harmon, J. Iacono, D. Kane and M. Pătraşcu, *The geometry of binary search trees*, SODA 2009, for the geometric view, GreedyASS and the online simulation. J. Derryberry, [*Adaptive Binary Search Trees*](https://www.cs.cmu.edu/~jonderry/thesis.pdf), PhD thesis, 2009, for the comparison of BST models. P. Bose, K. Douïeb, J. Iacono and S. Langerman, [*The Power and Limitations of Static Binary Search Trees with Lazy Finger*](https://arxiv.org/abs/1304.6897), ISAAC 2014 / Algorithmica 2016. J. Iacono and S. Langerman, [*Weighted Dynamic Finger in Binary Search Trees*](https://arxiv.org/abs/1810.01785), SODA 2016. E. D. Demaine, J. Iacono, S. Langerman and Ö. Özkan, [*Combining Binary Search Trees*](https://arxiv.org/abs/1304.7604), ICALP 2013, for the multi-finger simulation, ComboBST, tree buffers and snapshots. P. Bose, S. Collette, R. Fagerberg and S. Langerman, [*De-amortizing Binary Search Trees*](https://arxiv.org/abs/1111.1665), ICALP 2012, for pop-tarts, heavy-path simulation and deamortization. M. Kakimura and K. Terai, [*A Refined Analysis of the Sequential Access Theorem for Splay Trees*](https://arxiv.org/abs/2609.19746), 2026, for the potential used in the scanning proof.
:::
