# Split trees

The online simulation of [Chapter 17](simulation.html) keeps groups of keys that were touched at the same time, and it must later break these groups apart, a few keys at a time, as new requests touch parts of them. Each group is a binary search tree in its own right, sitting inside the big tree. What the simulation needs from it is a single operation: *split off the keys up to a given rank*, paid for by the keys of the group. Over the whole life of a group, a key may be involved in many splits, so a logarithmic cost per split is too much. The cost must be constant per key, amortized over all splits the group ever undergoes.

The classical way to achieve this is a finger search tree in which a split at rank $k$ costs $O(\log \min(k, n-k))$, the logarithm of the *smaller* side. A charge of that form adds up to $O(n)$ over any sequence of splits that eventually separates all $n$ keys. This accounting is the one used for level-linked search trees in Hoffmann, Mehlhorn, Rosenstiehl and Tarjan's linear-time Jordan sorting (1986), and Demaine, Harmon, Iacono, Kane and Pătraşcu build the *split trees* of their geometric simulation (2009) on the same principle. The difficulty in the BST model is that there are no finger pointers. Every access starts at the root, so a finger has to be *a shape of the tree*: the tree is restructured so that the endpoint is at the root and the keys near it are shallow.

The library implements split trees as 2–3–4 trees viewed as binary search trees. This chapter shows the vocabulary, all in `Structures/SplitTree`, and the contract that the simulation uses. The implementation of splitting, joining and two-ended fingers is internal to the library; it is checked by Lean but not part of the reading interface.

The chapter's main result has two halves. A finger at the minimum can be built cheaply as a shape, and from it a key of rank $k$ is reached in $O(\log k)$ rotations. Splits charged to their smaller side cost linear time in total.

```headline split-fingers
title: Fingers as tree shapes, and splits paid for by the smaller side
source: Demaine, Harmon, Iacono, Kane and Pătraşcu, *The geometry of binary search trees* (2009)
theorems: SplitTree.Results.finger_construction SplitTree.Results.finger_access SplitTree.Results.linear_accounting

Let $t$ be a 2–3–4 tree of height $h$ with $n$ keys, stored as a BST in its standard binary representation.

1. At most $3n$ rotations turn that BST into its *finger view*, a BST on the same $n$ keys whose right spine has at most $3h$ nodes.
2. In the finger view, splaying the key of rank $k$ is a legal root access that uses at most $5\lfloor\log_2(k+1)\rfloor + 6$ rotations.
3. Separately: take any order of splits that eventually separates $n$ keys, and charge $1 + \lfloor\log_2(\min(a, b) + 1)\rfloor$ for splitting a group into sides of $a$ and $b$ keys. The total charge is at most $2n$.

In Lean, $t$ is a [[SplitTree.Multiway]] with [[SplitTree.Multiway.Balanced]], its BST is [[SplitTree.Multiway.binary]], the finger view is [[SplitTree.Multiway.Finger.binaryView]], and the order of splits is a binary tree read by [[SplitTree.totalCharge]].
```

## 2–3–4 trees without keys

A 2–3–4 tree, the B-tree of order 4 (Bayer and McCreight, 1972), has internal nodes with two, three or four children, holding one, two or three keys, and all leaves at the same depth. As with binary shapes in [Chapter 1](shapes.html), the library stores no keys. A node's keys are the inorder ranks between its subtrees.

@decl RotationBST.SplitTree.Multiway RotationBST.SplitTree.Multiway.size RotationBST.SplitTree.Multiway.nodes

`size` counts keys: a node with $c$ children contributes $c - 1$ keys of its own. `nodes` counts the multiway nodes. For example, `.two (.three .nil .nil .nil) (.two .nil .nil)` has keys $0, 1$ in the left child, the root key $2$, and key $3$ in the right child: size $4$, three nodes.

@decl RotationBST.SplitTree.Multiway.Balanced

`Balanced h t` says that every leaf of `t` is at depth `h`. Each constructor requires its subtrees to have the same height, one less than the node's. The degree bounds are built into the type, so this is the full 2–3–4 invariant. A balanced tree of height $h$ has between $2^h - 1$ and $4^h - 1$ keys.

## The binary representation

In the BST model only binary trees exist, so a 2–3–4 tree is an organizing view of a binary search tree. The library fixes one binary representation:

@decl RotationBST.SplitTree.Multiway.binary

A 2-node is a binary node. A 3-node is two binary nodes leaning right, with its second key as the right child of its first. A 4-node is three binary nodes in a balanced triangle, with its middle key on top. Rotations, and therefore costs, are always counted on this binary tree; the multiway structure is bookkeeping that tells the algorithm which rotations to perform. The binary tree has the same inorder ranks, so `t.binary.size = t.size`, and its height is at most twice the multiway height.

The standard top-down repairs of a 2–3–4 tree are local restructurings of a node and its children. Before a split descends into a child that is a 2-node, the child gets an extra key, either borrowed from a sibling or obtained by merging with it:

@decl RotationBST.SplitTree.Multiway.prepareLeft RotationBST.SplitTree.Multiway.prepareRight

Each result pairs the repaired tree with the exact number of binary rotations that turn `t.binary` into the result's binary form. Merging two 2-nodes into a 4-node costs nothing: `.two (.two a b) (.two c d)` and `.four a b c d` have the same binary representation, so only the multiway reading changes. Borrowing from a 3-node takes two rotations. Borrowing from a 4-node takes three on the left and four on the right, because a 3-node leans right and the mirror image of a repair is not a repair of the mirror image. Patterns that do not match, including a child that is not a 2-node, are left unchanged at cost $0$.

## Contexts

Splitting and finger search move a focus up and down a multiway tree, so the library uses the same device as the pointer machine ([Chapter 6](pointer.html)): a *zipper*, the focused subtree together with the path of ancestors, each ancestor recorded with its other children.

@decl RotationBST.SplitTree.Multiway.Context.Frame RotationBST.SplitTree.Multiway.Context.Frame.fill

A frame is one ancestor with the focused child omitted. Its constructor names the ancestor's degree and the position of the hole: `threeMiddle a c` is a 3-node whose middle child is the focus, with `a` and `c` the other two children. `fill` puts a subtree back into the hole.

@decl RotationBST.SplitTree.Multiway.Context.Frame.Valid RotationBST.SplitTree.Multiway.Context.plug RotationBST.SplitTree.Multiway.Context.Valid RotationBST.SplitTree.Multiway.Context.edit

`plug fs t` reassembles the whole tree from the focus `t` and the frames `fs`, nearest ancestor first, exactly like [[Pointer.plug]] for binary trees. `Valid h fs` says that the result is balanced when the focus has height `h`: the siblings in the nearest frame have height `h`, those in the next frame `h + 1`, and so on. `edit` applies a local operation such as `prepareLeft` at the focus, reports its rotation count, and plugs the result back. The rotation count is unchanged by plugging, because a rotation inside a subtree is a rotation of the whole tree (`Rotations.inLeft`).

## The minimum finger

A finger at the minimum is the path from the leftmost leaf up to the root, read bottom-up. Searching for rank $k$ from the finger climbs this path until the subtree reached contains rank $k$, and then descends. The climb is the interesting part:

@decl RotationBST.SplitTree.Multiway.Finger.leftSpine RotationBST.SplitTree.Multiway.Finger.ascend RotationBST.SplitTree.Multiway.Finger.searchLevels

`leftSpine t` is the context of the leftmost leaf, nearest ancestor first. Each frame keeps all siblings, so nothing is lost. `ascend fs focus rank` climbs one frame at a time, filling the focus into its parent, and stops as soon as the focus has more than `rank` keys. The focus is always a prefix of the tree in inorder, because it is the leftmost subtree at its height, so "more than `rank` keys" means "contains rank `rank`". `searchLevels t rank` starts from the empty leftmost leaf and counts the levels climbed.

The first theorem says that the left spine is a faithful representation of the tree, with one frame per level.

**Theorem (the left spine).** For a balanced 2–3–4 tree `t` of height $h$, plugging the empty leaf into its left spine gives back `t`, the frames are valid from height $0$, and there are exactly $h$ of them.

@decl RotationBST.SplitTree.Results.finger_representation

A balanced subtree of height $j$ has at least $2^j - 1$ keys, so the climb for rank $k$ stops after about $\log_2(k+1)$ levels. Splitting needs the same from *both* ends, because the cost must depend on the smaller side. The maximum finger is the minimum finger of the mirror image:

@decl RotationBST.SplitTree.Multiway.Finger.mirror RotationBST.SplitTree.Multiway.Finger.nearSearchLevels

`mirror` reverses every node, so rank $k$ becomes rank $n - 1 - k$. `nearSearchLevels` climbs from whichever endpoint is nearer in rank.

**Theorem (climbing from the nearer end).** For a balanced 2–3–4 tree with $n$ keys and any rank $k$, the number of levels climbed from the nearer endpoint is at most $\lfloor\log_2(\min(k, n-1-k) + 1)\rfloor + 1$.

@decl RotationBST.SplitTree.Results.nearer_endpoint

This is the "logarithm of the smaller side" that the accounting below charges for.

::: check
- `nearSearchLevels` and the theorem use truncated subtraction `t.size - 1 - rank`. For `rank ≥ t.size` it is $0$, so the theorem says that an out-of-range rank needs at most one level, which is true: the climb from the minimum ends at the root and `ascend` stops when it runs out of frames. No hypothesis `rank < t.size` is needed.
- The levels are multiway levels, not BST costs. The next section turns them into BST depth.
:::

## A finger as a binary search tree

In the BST model a finger cannot be a pointer, so the library builds a binary tree whose root *is* the minimum and in which a key of rank $k$ is at depth $O(\log k)$. Take the left spine of the 2–3–4 tree and turn it into a right spine hanging from the minimum: walking down the new spine visits the separating keys of the old left spine in increasing order, and each separating key carries, as its left subtree, the binary representation of the subtree that lies just before it.

@decl RotationBST.SplitTree.Multiway.Finger.comb RotationBST.SplitTree.Multiway.Finger.BinaryView RotationBST.SplitTree.Multiway.Finger.BinaryView.tree RotationBST.SplitTree.Multiway.Finger.binaryView

`comb spine tail` is the right spine whose $i$-th node has `spine[i]` as its left subtree, ending in `tail`. `binaryView` computes the spine recursively from the left: the view of the leftmost child is extended by one spine node per key of the current node. For a 2-node `.two a b`, the old tail of `a` (its subtree to the left of the new key) moves onto the spine, and `b.binary` becomes the new tail. A 3-node adds two spine nodes and a 4-node three. The deepest left subtree on the spine is the empty leaf below the minimum, so the root of the view has no left child: it is rank $0$.

@decl RotationBST.SplitTree.Multiway.Finger.viewCost

`viewCost` is an exact count of the rotations that turn `t.binary` into the view, level by level: each level costs one rotation per spine node built so far, and twice as many plus one for a 4-node, whose binary representation has its middle key on top.

The view has four properties that the simulation uses.

**Theorem (building the finger).** For a balanced 2–3–4 tree `t` of height $h$ with $n$ keys, exactly `viewCost t` rotations take `t.binary` to the view, and `viewCost t` is at most $3n$. The view has $n$ keys, and its right spine has at most $3h$ nodes.

@decl RotationBST.SplitTree.Results.finger_construction

So creating a finger is linear in the group's size, which is what the simulation pays when it creates a new group.

**Theorem (the minimum is at the root).** For every nonempty 2–3–4 tree `t`, the `viewCost t` rotations from `t.binary` to the view form a root access of rank $0$, in the sense of [Chapter 3](accesses.html).

@decl RotationBST.SplitTree.Results.finger_minimum

**Theorem (search near the minimum).** For a balanced 2–3–4 tree `t` and a rank $k$ of `t`, the key of rank $k$ has depth at most $5\lfloor\log_2(k+1)\rfloor + 6$ in the view.

@decl RotationBST.SplitTree.Results.finger_search_depth

Depth is the search depth [[Tree.depth]] of [Chapter 1](shapes.html#depth). An ordinary root-to-node search, with no finger pointer, now costs logarithmically in the distance to the minimum.

**Theorem (access near the minimum).** For a balanced 2–3–4 tree `t` and a rank $k$ of `t`, splaying rank $k$ in the view ([[Splay.run]], [Chapter 13](splay.html)) is a legal root access with at most $5\lfloor\log_2(k+1)\rfloor + 6$ rotations.

@decl RotationBST.SplitTree.Results.finger_access

Splaying a node at depth $d$ performs exactly $d$ rotations, so this follows from the depth bound.

::: check
- `finger_search_depth` and `finger_access` assume `Balanced h t` but their bounds do not mention `h`. Roughly, the constant $5$ has two sources: the spine grows by up to three nodes per multiway level, and the binary representation of a subtree can be twice as tall as its multiway height.
- The statements mention [[Tree.depth]] (from the rotation model) and [[Splay.run]] (from the splay algorithm). They are used only to measure the view; split trees do not depend on splaying otherwise.
:::

The figure draws a random balanced 2–3–4 tree and its two binary forms, with every key at the horizontal position of its rank. Select a key to see the levels the finger climbs, and compare its depth in `t.binary` with its depth in the view. For small ranks the view is much shallower; for ranks near the maximum, switch the finger to "nearer end".

@viz splittree {"height": 3, "seed": 5, "rank": 4}

## Paying for splits

The simulation does not use one split but a whole *hierarchy* of them. A group of $n$ keys is split around some key, then each side is split again, in any interleaving with other work, until every key has been separated. Such a hierarchy is itself a binary tree: its root is the first splitting key, and its subtrees are the hierarchies of the two sides. The charge for one split is the logarithm of the smaller side:

@decl RotationBST.SplitTree.charge RotationBST.SplitTree.totalCharge

`charge left right` is $1 + \lfloor\log_2(\min(\mathit{left}, \mathit{right}) + 1)\rfloor$, where `left` and `right` are the numbers of keys remaining on each side. `totalCharge` adds the charges over a hierarchy.

**Theorem (linear accounting).** For every hierarchy of splits on $n$ keys, the total charge is at most $2n$.

@decl RotationBST.SplitTree.Results.linear_accounting

The proof keeps a reserve of $2s - \lfloor\log_2(s+1)\rfloor$ for every interval of $s$ keys. Splitting an interval of $a + b + 1$ keys into $a$ and $b$ releases the reserve of the larger interval and creates those of the two smaller ones, and the difference covers the charge, because $\lfloor\log_2(a+b+2)\rfloor \le 1 + \lfloor\log_2(\max(a,b)+1)\rfloor$. The same quantity appears, scaled by a constant number of rotations per unit, as the credit that the simulation stores with each group ([Section 17.4](simulation.html#how-the-simulation-works)).

::: caveat What this chapter does not state
The abstract is a contract, not a split-tree implementation. It states construction, minimum, search and access for a minimum finger, the climb from the nearer endpoint, and the accounting lemma. The BST implementation of splitting, with its per-split rotation bound, the two-ended finger state (a minimum finger and a maximum finger on either side of a median root), joins and rebuilding are proved in internal `Results` modules under `Structures/SplitTree`. The simulation relies on them, and their statements are checked by Lean, but they are outside the reading interface, so trusting the simulation's statement does not require reading them.
:::
