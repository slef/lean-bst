# Models

Part I fixes what a binary search tree execution is and what it costs. The literature uses several models for this, each convenient for some arguments, and the book uses all of them. This introduction lists them and shows how they relate. Every model is defined in its own chapter, and [Chapter 11](equivalence.html) proves the main correspondences.

## The models

| Chapters | Model | An execution is | Cost |
|---|---|---|---|
| {{num:shapes}}–{{num:accesses}} | [Rotations](shapes.html) | A sequence of root accesses on a tree whose keys are its inorder ranks, changed by [rotations](rotations.html). Each request rotates anywhere until the requested key is at the root. | $m + R$: one per request, one per rotation |
| {{num:keys}} | [Labelled trees](keys.html) | The same, on trees that store arbitrary ordered keys | $m + R$ |
| {{num:online}} | [Online algorithms](online.html) | A rule that chooses each access from the requests so far. Its run is an execution of the rotation model. | $m + R$ |
| {{num:dictionary}} | [Insertions and deletions](dictionary.html) | A sequence of searches, insertions and deletions by rank, with balance data in the nodes. Only the splay-tree version is formalized. | one per node of the search path, one per rotation |
| {{num:pointer}} | [Pointer machine](pointer.html) | One cursor, which starts at the root for every request, moves along edges and rotates its node over its parent | $K$: one per request, one per instruction |
| {{num:regions}} | [Touched regions](regions.html) | Each request touches a rooted subtree containing the requested key, and rearranges it | the number of touched nodes |
| {{num:geometry}} | [Geometric view](geometry.html) | An arborally satisfied set of points (key, time) containing the requests | $\lvert E\rvert$: the number of points |
| {{num:fingers}} | [Many fingers](fingers.html) | Several persistent fingers in one tree, each moving or rotating at its node | one per request, one per instruction |
| {{num:linked-search}} | [Linked searches](linked-search.html) | Static searches in a store of many trees joined by links, with a count of memory words. Not a BST. | one per visited node and per followed link |

The rotation model is the library's basic one: "a legal BST algorithm" and "the offline optimum" in later theorems refer to it, unless a theorem says otherwise. The pointer machine is the standard model of the literature. Touched regions and the geometric view describe an execution by the keys it touches, which is what lower bounds and the geometric algorithms work with. The dictionary model of [Chapter 6](dictionary.html) adds updates, for the classical trees of [Part III](part-classical.html); the dashed box in the figure marks it as not formalized yet. The last two models serve particular results. Many fingers describe a static tree searched with a lazy finger ([Chapter 13](lazy-finger.html)) and the multi-finger BSTs of the combination ([Chapter 23](combination.html)). Linked searches are the model of the multiple-tree structure ([Chapter 22](multiple-trees.html)), and are compared with nothing else.

## How the models relate

An arrow in the figure means that an execution in one model gives an execution in the other that serves the same requests, at the cost written on the arrow. The arrows between the rotation model, the pointer machine and the geometric view lose only constant factors, plus a term in $n$ when the initial tree is prescribed. So the offline optimum is the same in all three, up to constant factors. The bottom row does the same for online algorithms.

@viz modelsmap {"roadmap": "https://github.com/slef/lean-bst/blob/main/ROADMAP.md"}

The table lists every correspondence, with $m$ requests, $n$ keys, $R$ rotations, $K$ pointer cost (requests plus instructions) and $\lvert E\rvert$ points.

| From | To | Cost | Trees | Theorem |
|---|---|---|---|---|
| shape executions | labelled executions | equal, both ways | same up to labels | [[RotationBST.Representation.execution_on_keys_iff\|execution_on_keys_iff]] |
| pointer execution | rotation execution | $m + R + q \le 3K$ | final $q$ rotations away | [[RotationBST.Pointer.Results.to_rotations\|to_rotations]] |
| rotation execution | pointer execution | $K \le m + 2nR$ | same final tree | [[RotationBST.Pointer.Results.to_pointer\|to_pointer]] |
| rotation execution | pointer execution | $K + 32d \le 32R + 17m$ | final $d$ rotations away | [[RotationBST.Pointer.Results.to_pointer_lazy\|to_pointer_lazy]] |
| online rotation algorithm | online pointer algorithm | $K + 32d \le 32R + 17m$ | any initial tree | [[RotationBST.Pointer.Lazy.Online.Results.simulation\|simulation]] |
| one-finger lazy-finger execution | pointer execution | $K \le 464 \cdot \text{cost}$ | same tree | [[LazyFinger.Dynamic.Results.same_tree\|same_tree]] |
| region execution | point set | equal, both ways | initial tree chosen | [[Geometric.Equivalence.Results.ass_iff_region_execution\|ass_iff_region_execution]] |
| rotation execution | point set | $\lvert E\rvert \le 2R + m$ | initial forgotten | [[Geometric.Equivalence.Results.rotations_to_ass\|rotations_to_ass]] |
| pointer execution | point set | $\lvert E\rvert \le 6K$ | initial forgotten | [[Geometric.Equivalence.Results.pointers_to_ass\|pointers_to_ass]] |
| point set | pointer execution | $K \le 33\,\lvert E\rvert$ | initial chosen | [[Geometric.Equivalence.Results.ass_to_pointers\|ass_to_pointers]] |
| point set | rotation execution | $m + R \le 2n + 99\,\lvert E\rvert$ | initial prescribed | [[Geometric.Equivalence.Results.ass_to_rotations\|ass_to_rotations]] |
| point set | pointer execution | $K \le 64n + 3168\,\lvert E\rvert$ | initial prescribed | [[Geometric.Equivalence.Results.ass_to_pointers_from\|ass_to_pointers_from]] |
| online geometric algorithm | online BST algorithm | $R \le 6018\,(\text{points} + n)$ | any initial tree | [[Geometric.Equivalence.Results.online_bst\|online_bst]] |

Two consequences shape the rest of the book. Bounds can be stated in whichever model is most convenient and moved to the others at a constant cost: [Part II](part-bounds.html) states its sequence bounds for rotation-model algorithms, and Wilber's lower bound in [Chapter 11](wilber.html) is proved on point sets. And an algorithm can be designed in whichever model is most convenient: splaying ([Chapter 13](splay.html)) is a rotation algorithm, GreedyASS ([Chapter 16](greedy.html)) is a geometric one, and Tango ([Chapter 19](tango.html)) maintains a tree whose edges are marked by preferred paths.
