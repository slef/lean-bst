# Rotations

A rotation at a node swaps it with one of its children while keeping inorder fixed. With keys $x < y$, the right rotation at $y$ turns $((A\,x\,B)\,y\,C)$ into $(A\,x\,(B\,y\,C))$, and the left rotation at $x$ undoes it. Rotations are the only restructuring primitive in the model. Searching, splaying, insertion and deletion are all built from them, or charged in terms of them.

This chapter defines a single rotation, [[RotationBST.Rotate]], and a sequence of exactly $k$ rotations, [[RotationBST.Rotations]]. Every cost in the book is a count of such steps, so these two relations appear on the reading list of almost every result. The theorems here are sanity checks rather than results: rotations preserve the number of nodes, sequences compose with additive cost, and a sequence inside a subtree is a sequence in the whole tree.

## One rotation

Since keys are ranks and rotations preserve inorder, a rotation never changes any key. It only changes the shape. The library defines rotation as a *relation* between shapes:

@decl RotationBST.Rotate

`Rotate s t` holds when `t` is obtained from `s` by exactly one rotation somewhere in the tree. The four constructors split this into a rotation *at the root* and a rotation *inside a subtree*:

- `right` is the right rotation at the root. The left child of the root becomes the new root. Writing $a, b, c$ for the three subtrees, `node (node a b) c` becomes `node a (node b c)`, which is the picture above with the keys removed.
- `left` is its mirror image: the right child of the root becomes the new root.
- `inLeft` and `inRight` lift a rotation of a subtree to the whole tree. If `Rotate a b`, then rotating inside the left subtree turns `node a c` into `node b c`, and likewise on the right.

A rotation at depth $d$ is therefore a derivation with $d$ uses of `inLeft`/`inRight` wrapped around one `right` or `left`. The relation has no position argument; *where* the rotation happens is recorded in the shape of its proof. The figure computes this proof term for every rotation you perform.

@viz rotate {"n": 8, "shape": "balanced"}

::: check
- The names follow the direction of the rotation, not the child being promoted: `right` promotes a *left* child. [Chapter 5](pointer.html) names cursor moves after the promoted child instead (`rotateLeftChild` promotes a left child), so `right` and `rotateLeftChild` describe the same restructuring.
- No subtree is copied, dropped or reordered: in both base cases the subtrees $a, b, c$ appear in the same left-to-right order on both sides. This is exactly the statement that inorder is preserved, made precise in [[Representation.rotation_preserves_keys]].
- `Rotate` is a relation, not a function, so a shape may have many successors, one per non-root node. Every non-root node can be rotated over its parent, and these are the only moves.
:::

A rotation preserves size, and therefore the set of keys $\{0, \dots, n-1\}$.

**Theorem (rotations preserve size).** If $t$ is obtained from $s$ by one rotation, then $s$ and $t$ have the same number of nodes.

The library proves it as `Rotate.size_eq`, by induction on the rotation. Each base case is the equation $(|a| + 1 + |b|) + 1 + |c| = |a| + 1 + (|b| + 1 + |c|)$, discharged by `omega`. The relation is also symmetric, since `right` and `left` are mutually inverse; this is proved in the library as `Rotate.symm`.

## Counted sequences of rotations

Costs in the rotation model count rotations, so a sequence of rotations is recorded together with its exact length:

@decl RotationBST.Rotations

`Rotations s t k` says that `t` can be reached from `s` by exactly `k` rotations. `refl` is the empty sequence (cost $0$) and `step` adds one rotation at the front (cost $k+1$). This is the reflexive-transitive closure of `Rotate`, indexed by length. Because the count is exact, an upper bound on cost is always stated explicitly, as in `∃ k, k ≤ 2 * s.size ∧ Rotations s t k`. The relation itself never silently allows extra rotations.

Three closure properties are used throughout.

**Theorem (composition and lifting).** If $j$ rotations turn $s$ into $t$ and $k$ rotations turn $t$ into $u$, then $j + k$ rotations turn $s$ into $u$. If $k$ rotations turn $a$ into $b$, then $k$ rotations turn `node a c` into `node b c`, and `node c a` into `node c b`.

These are `Rotations.append`, `Rotations.inLeft` and `Rotations.inRight`.

**Theorem (sequences preserve size).** If $k$ rotations turn $s$ into $t$, then $s$ and $t$ have the same number of nodes.

This is `Rotations.size_eq`, an induction using `Rotate.size_eq`.

::: note Where these live
`Rotate` and `Rotations` are in `Models/Rotation/Abstract.lean`, the most basic reading module. The five lemmas above are proved in `Models/Rotation/Basic.lean` and `Models/Rotation/Rotations.lean`. They are not part of any theorem statement, so they are outside the reading interface and the book states them without quoting their Lean. They are the first sanity checks a reader would want, and the proofs use them constantly.
:::
