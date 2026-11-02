# Binary Search Trees in Lean

<p class="lead">This book is a guided reading of <a href="https://github.com/slef/lean-bst">lean-bst</a>, a Lean 4 library that formalizes a rotation-based model of binary search trees, shows that it is equivalent to the usual formulations, and proves the main theorems of Sleator and Tarjan's 1985 paper on splay trees.</p>

You know what a binary search tree is, and what a rotation does. The question this book helps you answer is narrower: *do the Lean definitions say what you think they say, and do the theorems say what the paper says?* A machine-checked proof guarantees that the statement follows from the definitions. It cannot tell you whether those are the right definitions and the right statement. Only a reader can check that, and the reading is easier with explanations next to the code.

So each definition and theorem statement in the library's public interface appears below as it was compiled. The prose between them explains what each piece models, why it is phrased the way it is, and where the formal choices differ from textbook conventions. Proofs are not explained: Lean has checked them, and you can open any of them from its code block.

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

The library follows the [abstractlean](https://github.com/slef/abstractlean) convention. Every topic has a short file called `Abstract.lean` containing only definitions and theorem statements; proofs are imported from separate "bridge" modules. Each such file ends with a command like

```lean
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Online.Abstract, …]
```

This command fails to compile unless every library definition mentioned in a theorem statement, directly or transitively, comes from one of the listed modules. The proofs are exempt: they may use anything. So to trust a theorem you need to read its statement and the definitions in the listed modules, and nothing else from the library. This book shows that list under every theorem, linked to the chapters where those modules are explained. [Appendix A](audit.html) describes the checks in more detail and summarizes them for all theorems.

## Conventions at a glance

These conventions hold throughout the library. Each is justified where it first appears.

| | Convention |
|---|---|
| Keys | A tree on $n$ keys stores no keys at all. Its keys are the inorder ranks $0,\dots,n-1$ ([Chapter 1](shapes.html)); arbitrary ordered keys are recovered exactly in [Chapter 4](keys.html). |
| Access | Serving request $x$ means rotating until $x$ is at the root ([Chapter 3](accesses.html)). |
| Rotation cost $R$ | The number of rotations, at any depth. No pointer movement is charged. |
| Total cost $T$ | $T = m + R$ for $m$ requests ([Chapter 6](online.html)). Without the $+m$, a request for the current root would be free. |
| Pointer cost | One per cursor move or rotation, plus one per request ([Chapter 5](pointer.html)). Within constant factors this is the same as $T$. |
| Logarithms | Base 2. `Real.logb 2` on reals, with Mathlib's convention $\log 0 = 0$; `Nat.log2` (floor) on naturals. |
| Startup | Bounds that hold for every initial tree include an explicit additive term for it, usually $D \cdot n(1+\lfloor\log_2 n\rfloor)$. |

## Interactive figures

The figures let you rotate, search and splay. They do not imitate the algorithms: they run JavaScript transcriptions of the executable Lean definitions, one equation at a time and with the same names. The book's test suite compares these transcriptions against values computed by the Lean functions themselves, on all shapes with at most six nodes and on larger random cases. Here is one; click any node that is not the root.

@viz rotate {"n": 9, "shape": "random", "seed": 3}

## Map of the book

**Part I** sets up the rotation model: unlabelled shapes ([1](shapes.html)), rotations ([2](rotations.html)), and root accesses and executions ([3](accesses.html)).

**Part II** proves that nothing was lost. Shapes are in exact correspondence with labelled BSTs on any key set, through rotations, accesses and whole executions ([4](keys.html)). A conventional single-pointer machine is equivalent to the rotation model up to constant factors ([5](pointer.html)).

**Part III** defines online algorithms, their cost, and dynamic optimality ([6](online.html)), and then the classical adaptive bounds: working set, static optimality, static finger, and comparison with a fixed tree ([7](bounds.html)).

**Part IV** is about splay trees: the algorithm and its correctness ([8](splay.html)), the potential-function analysis and Theorems 1–5 of the paper ([9](analysis.html)), and updates, long splays, the snapshot theorem and sequential access ([10](beyond.html)).

::: note Sources
D. D. Sleator and R. E. Tarjan, [*Self-Adjusting Binary Search Trees*](https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf), JACM 32(3), 1985. J. Derryberry, [*Adaptive Binary Search Trees*](https://www.cs.cmu.edu/~jonderry/thesis.pdf), PhD thesis, 2009, for the comparison of BST models. M. Kakimura and K. Terai, [*A Refined Analysis of the Sequential Access Theorem for Splay Trees*](https://arxiv.org/abs/2609.19746), 2026, for the potential used in the scanning proof.
:::
