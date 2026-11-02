# Putting the keys back

Part I worked entirely with shapes, where a node's key is its inorder rank. This chapter proves that nothing was lost. A shape on $n$ nodes is the same thing as a BST on any fixed list of $n$ keys. Rotations, root accesses and whole executions on shapes are exactly the corresponding operations on labelled trees, with the same costs. The local "left smaller, right larger" invariant is equivalent to the inorder formulation used throughout. Finally, the shape type is Mathlib's `BinaryTree Unit` under another name.

All theorems here are in `Representation/Abstract.lean`, `Representation/Ordering/Abstract.lean` and `Representation/Mathlib/Abstract.lean`. Their statements mention only the model definitions of [Chapter 1](shapes.html) and [Chapter 2](rotations.html), the labelled counterparts introduced next, and three small definitions in this chapter.

## Shapes and canonical labels

### Labelled rotations, accesses and executions

`Model/Abstract.lean` defines the labelled versions of the three relations of Part I, transcribed constructor by constructor. They are the textbook notions, stated for keys of an arbitrary type `α`.

@decl RotationBST.LabelledTree.Rotate

The four constructors mirror [[RotationBST.Rotate]] exactly, with the two keys involved now visible. In `right`, the left child `x` of the root `y` is promoted: `(a x b) y c` becomes `a x (b y c)`. Every key moves with its node. Nothing in the definition mentions an order on `α`. A rotation is a purely structural operation, and the fact that it preserves BST order is a theorem ([Section 4.2](#the-textbook-invariant)).

@decl RotationBST.LabelledTree.Rotations RotationBST.LabelledTree.Access RotationBST.LabelledTree.Execution

These are copies of [[RotationBST.Rotations]], [[RotationBST.Access]] and [[RotationBST.Execution]] with one change: an access for key `x` ends with a root whose *label* is `x` (`y = x`), instead of a root whose left subtree has size `x`. The cost convention is unchanged: rotations only, at any depth.

::: check
If `α` has repeated keys, `LabelledTree.Access s t x k` is satisfied by bringing *any* node labelled `x` to the root. This is why the arbitrary-key correspondence below assumes distinct keys (`Nodup`). For the canonical labels `0, 1, …` the keys are always distinct.
:::

### Labelling is a bijection

The first three theorems say that [[RotationBST.Tree.labelFrom]] and [[RotationBST.LabelledTree.erase]] are inverse to each other on BSTs with consecutive keys.

@decl RotationBST.Representation.erase_label RotationBST.Representation.inorder_label RotationBST.Representation.reconstruct

- `erase_label`: labelling a shape and forgetting the labels returns the shape.
- `inorder_label`: the canonical labels read `lo, lo+1, …, lo + t.size - 1` in inorder. `List.range' lo n` is the list of the `n` consecutive naturals starting at `lo`.
- `reconstruct`: conversely, a labelled tree whose inorder traversal is `lo, …, lo + n - 1` (with `n` the size of its own shape) *is* the canonical labelling of that shape. So every BST on consecutive keys arises from exactly one shape.

The uniqueness half holds for arbitrary keys and does not even need distinctness:

@decl RotationBST.Representation.labels_unique

Two labelled trees with the same shape and the same inorder list are equal. The shape fixes which node is $i$-th in inorder, and the list fixes its label. Existence for arbitrary key lists is [[RotationBST.Representation.labels_exist]] in [Section 4.3](#arbitrary-keys).

### Rotations and accesses correspond exactly

@decl RotationBST.Representation.rotation_iff RotationBST.Representation.rotation_preserves_keys

`rotation_iff` says that one shape rotation is exactly one labelled rotation between the canonically labelled trees, for every offset `lo`. As stated, it only concerns labelled rotations whose target is canonically labelled. It covers all of them, because every labelled rotation preserves the inorder list (`rotation_preserves_keys`, stated for arbitrary labels with no order or distinctness hypothesis). A labelled rotation from `s.labelFrom lo` therefore ends at a tree whose labels are still `lo, lo+1, …` in inorder, which by `reconstruct` is `t.labelFrom lo` for its own shape `t`.

@decl RotationBST.Representation.rotations_iff RotationBST.Representation.access_iff

`rotations_iff` lifts the correspondence to traces *with the same count `k`*, so costs are preserved exactly, not up to a constant. `access_iff` is the statement Part I relied on: accessing implicit rank `x` in a shape is exactly accessing the explicit key `x` in its labelling by `0, …, size − 1`, with the same final tree and the same number of rotations. It is stated with offset `0`, because the requested rank is an absolute position in the whole tree.

The figure runs the shape model with the ranks displayed as words. Each rotation is a shape rotation, and the inorder list in the panel never changes.

@viz rotate {"keys": ["ant", "bee", "cat", "dog", "eel", "fox", "gnu"], "shape": "random", "seed": 6, "target": 3, "title": "Shape rotations, displayed with keys"}

## The textbook invariant

So far "BST" has meant "labelled tree with a prescribed sorted inorder list". The textbook definition is local instead: at every node, keys in the left subtree are smaller and keys in the right subtree are larger. `Representation/Ordering/Definitions/Abstract.lean` states it in that form:

@decl RotationBST.LabelledTree.Ordered

Both subtrees are ordered, every key in `l` is below the root key `x`, and every key in `r` is above it. The quantifiers range over *all* keys of each subtree (via `inorder`, used here only as the list of keys), not just over the children. A condition on children alone would be the classic incorrect definition. The relation `<` comes from any `LT α` instance, and only the theorems below assume more.

@decl RotationBST.Representation.ordered_iff

With a preorder on `α`, the local invariant is equivalent to the inorder list being strictly increasing: `List.Pairwise (· < ·)` requires `a < b` for every pair of positions, earlier before later. Strictness makes keys pairwise distinct, since `a < a` is impossible in a preorder.

@decl RotationBST.Representation.ordered_labels_exist_unique

This is the formal version of the opening paragraph of [Chapter 1](shapes.html). Given a shape with $n$ nodes and a strictly increasing list of $n$ keys, there is exactly one (`∃!`) labelled tree with that shape and that inorder list that satisfies the textbook invariant. By `ordered_iff`, the `Ordered` conjunct already follows from the other two. It is included so that the statement is the familiar one, with no reference to inorder lists needed for the meaning of "BST".

@decl RotationBST.Representation.ordered_label RotationBST.Representation.rotations_preserve_order

The canonical labelling of every shape is a BST in the textbook sense (`Nat` is ordered as usual). Rotation traces preserve the invariant *in both directions*: for `Rotations s t k`, `s` is ordered exactly when `t` is. Together with `rotations_iff`, every shape execution is an execution of ordinary BSTs that never violates the search-tree property, and conversely.

::: check
The direction "`t.Ordered → s.Ordered`" is not a typo. The proof rewrites both sides with `ordered_iff` and uses that a rotation trace leaves the inorder list unchanged, which gives both directions at once.
:::

## Arbitrary keys

Consecutive ranks are a normalization, but the correspondence does not depend on it. These theorems work for keys of any type `α`, with no order assumed at all.

@decl RotationBST.Representation.labels_exist

Any list of the right length labels any shape. Together with [[RotationBST.Representation.labels_unique]], labelling a shape `t` by a fixed list `keys` with `keys.length = t.size` is a bijection between shapes of that size and labelled trees with inorder list `keys`. For a strictly increasing list these are exactly the BSTs on those keys, by [[RotationBST.Representation.ordered_iff]].

@decl RotationBST.Representation.arbitrary_rotations_iff

For two labelled trees with the same inorder list, a trace between their shapes is exactly a labelled trace between them, with the same count. The hypothesis `keys : s.inorder = t.inorder` is needed for the backward direction: a shape trace says nothing about labels, so the labels of `t` must already be the ones a rotation trace would carry over from `s`.

@decl RotationBST.Representation.arbitrary_access_iff

This translates rank requests into key requests. Accessing rank `x` in the shape is the same as accessing the key `s.inorder[x]`, the $x$-th key in inorder, in the labelled tree, at the same cost. There are three hypotheses:

- `keys`: both trees carry the same key list, as above.
- `distinct`: the keys are pairwise distinct. Without it, the labelled access could be served by another node with the same label, which is not the node of rank `x` (see the check box in [Section 4.1](#shapes-and-canonical-labels)).
- `valid`: `x` is in range. In Lean, `s.inorder[x]` needs a proof of `x < s.inorder.length` to typecheck, and `valid` supplies it.

@decl RotationBST.Representation.execution_on_keys_iff

The same for whole request sequences. Requests are elements of `Fin keys.length`, indices into the key list, so every request is valid by construction. The shape execution serves their values as ranks (`xs.map Fin.val`), and the labelled execution serves the corresponding keys (`xs.map keys.get`, where `keys.get i` is the `i`-th key). Both endpoints must carry the list `keys` (`hs`, `ht`). The two executions then have the same endpoints, up to erasing labels, and exactly the same cost `k`.

::: note Consequence
Any theorem about request sequences over ranks, such as the splay bounds of Part IV, transfers to BSTs over any set of distinct keys with no loss: rename the keys to their ranks, apply the theorem, and translate back with `execution_on_keys_iff`.
:::

## Mathlib's binary trees

Mathlib's `BinaryTree α` stores a value of type `α` at every node. With `α = Unit` a node stores nothing, which is exactly a shape. The library provides the two obvious conversions:

@decl RotationBST.Representation.toBinaryTree RotationBST.Representation.fromBinaryTree

Mathlib's `node` takes the stored value first (`.node () l r`), and the library's `node` takes only the subtrees.

@decl RotationBST.Representation.from_toBinaryTree RotationBST.Representation.to_fromBinaryTree RotationBST.Representation.binaryTreeEquiv RotationBST.Representation.numNodes_toBinaryTree

The two round trips are identities, so the conversions are packaged as an equivalence `Tree ≃ BinaryTree Unit` (Mathlib's type of bijections with explicit inverses). Size corresponds to Mathlib's `numNodes`. Anything Mathlib proves about binary trees, such as counting results, therefore applies to shapes through `binaryTreeEquiv`. The library keeps its own `Tree` type so that the model files depend only on Lean's standard library.
