# Trees without keys

Fix keys $k_0 < k_1 < \dots < k_{n-1}$. A binary search tree on these keys has no freedom in where the keys go once its shape is fixed: an inorder traversal must read $k_0, \dots, k_{n-1}$ in that order, so the $i$-th node visited holds $k_i$. Conversely, writing $k_0, \dots, k_{n-1}$ into any $n$-node shape in inorder gives a valid BST. Forgetting the keys and writing them back are inverse operations.

The library therefore represents a BST by its **shape** alone. The key of a node is its **inorder rank**, a number in $\{0, \dots, n-1\}$ that the tree does not store but can always compute. This removes the search-tree invariant from every definition: there is no ordering condition to state, maintain or prove preserved. No BST and no access sequence is lost, as [Chapter 4](keys.html) proves.

## Shapes

@decl RotationBST.Tree

A `Tree` is either empty (`nil`) or a node with a left and a right subtree. Nothing else is stored: no key, no size field, no parent pointer, no balance information. Every finite binary tree shape is exactly one value of this type, and two values are equal exactly when the shapes are.

The `deriving` clause asks Lean to generate a decision procedure for equality (`DecidableEq`) and a printer (`Repr`). Neither adds any mathematical content.

Only `node`s represent keys. `nil` is an empty subtree, the "external node" of some textbooks. It is where an unsuccessful search ends and where an insertion puts the new key.

## Size

@decl RotationBST.Tree.size

`Tree.size` counts nodes, that is, keys. A `nil` contributes nothing. The two summands $1$ and `r.size` are written in inorder order (left, root, right), which matches how ranks are assigned below.

Lean's `Nat` is the type of natural numbers, with truncated subtraction: $3 - 5 = 0$. The library uses subtraction only on branches where it cannot truncate, as in the search below.

## Implicit keys

Inorder visits the left subtree, then the root, then the right subtree. So in `node l r` the root has rank `l.size`: exactly `l.size` keys come before it. More generally, take a subtree whose smallest key has rank $lo$ in the whole tree. Its root has rank $lo + {}$`l.size`, its left subtree starts at $lo$, and its right subtree starts at $lo + {}$`l.size`$ + 1$.

A subtree does not know its own offset $lo$. The same shape can hold keys $0..2$ in one tree and $17..19$ in another. Library functions that need actual keys (the labelling below, the search in [Chapter 8](splay.html), the potential function in [Chapter 9](analysis.html)) therefore carry the offset as an extra argument, conventionally named `lo`, and update it exactly as described here.

@viz shape {"tree": ".node (.node .nil (.node .nil .nil)) (.node (.node .nil .nil) (.node .nil .nil))"}

The squares in the figure are the `nil` subtrees. Each sits in an inorder gap: the empty subtree between ranks $i-1$ and $i$ is "gap $i$", and an $n$-node tree has $n+1$ gaps, numbered $0, \dots, n$. Growing the tree at gap $i$ adds a key there and shifts every rank at or after $i$ up by one. This is what an insertion does to ranks ([Chapter 10](beyond.html)).

## Labelled trees

To compare shapes with ordinary BSTs, the library also has the ordinary data structure: trees whose nodes carry keys of an arbitrary type `α`.

@decl RotationBST.LabelledTree

No order on `α` is assumed, not even decidable equality. The order enters only when we state that a labelled tree is a *search* tree ([Section 4.2](keys.html#the-textbook-invariant)). Two operations connect labelled trees with shapes.

@decl RotationBST.LabelledTree.erase RotationBST.LabelledTree.inorder

`erase` forgets every key and keeps the full shape. `inorder` lists the keys in symmetric order, `l.inorder ++ x :: r.inorder`. The docstring of `inorder` states the convention used throughout: **a BST on a given sorted key list is a labelled tree whose inorder traversal is that list.** This is equivalent to the familiar local condition ("left keys smaller, right keys larger"), and [Chapter 4](keys.html) proves the equivalence.

## Canonical labels

Going back from a shape to a labelled tree means writing in the ranks:

@decl RotationBST.Tree.labelFrom

`t.labelFrom lo` labels the nodes of `t` with $lo, lo+1, \dots, lo + {}$`t.size`$ - 1$ in inorder. The equations are exactly the offset arithmetic from above. The root of `node l r` gets `lo + l.size`, the left subtree is labelled from `lo`, and the right subtree from `lo + l.size + 1`. With `lo = 0` this writes the implicit keys explicitly: `(t.labelFrom 0).inorder = [0, 1, …, t.size - 1]`.

::: check
Three things should hold, and [Chapter 4](keys.html) proves each of them:

1. `(t.labelFrom lo).erase = t`. Labelling does not change the shape ([[Representation.erase_label]]).
2. `(t.labelFrom lo).inorder` is the list `lo, lo+1, …`, so the labels are the ranks offset by `lo` ([[Representation.inorder_label]]).
3. Every labelled tree whose inorder traversal is `lo, lo+1, …` is the canonical labelling of its own shape ([[Representation.reconstruct]]).

Together these say that `erase` and `labelFrom 0` are inverse bijections between $n$-node shapes and BSTs on the keys $0, \dots, n-1$.
:::

The next two chapters work only with `Tree`. Accesses are stated in terms of ranks, as in "bring the node of rank $x$ to the root", and labelled trees return in [Chapter 4](keys.html) to show that nothing was lost.
