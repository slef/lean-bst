# Touched regions

The rotation model of [Chapter 3](accesses.html) counts rotations, and the pointer machine of [Chapter 6](pointer.html) counts cursor moves and rotations. A third accounting is standard in the work on dynamic optimality since Demaine, Harmon, Iacono, Kane and Pătraşcu (2009). It forgets how a search restructures and counts only *which nodes it touches*.

Serving a request touches a set of nodes that contains the requested key and forms a connected subtree containing the root. The algorithm may then rearrange the touched nodes into any shape, as long as every untouched subtree hangs back in its inorder slot. The cost is the number of touched nodes. A pointer search that visits $k$ nodes is such a step, since the cursor only travels along edges from the root and only rotates nodes it has visited. Conversely, any rearrangement of $k$ touched nodes can be performed by a pointer machine with $O(k)$ instructions. The models therefore agree up to constant factors, and [Chapter 9](equivalence.html) proves it.

The point of this model is the next chapter. Each step is described by a single set of keys, so a whole execution becomes a set of points (key, time) in the plane, and its cost is the number of points. The definitions below are in `Models/Region/Abstract.lean` and `Models/Region/View/Abstract.lean`.

## Regions

A touched region is a tree whose leaves are either empty or entire untouched subtrees. The library already has this type: the *skeletons* of the lazy pointer simulation ([[Pointer.Lazy.Skeleton]], from [Chapter 6](pointer.html)). A skeleton is built from `node`, an active node of the region, and `hole t`, an untouched subtree `t` hanging below the region. `Skeleton.tree` fills the holes in, `Skeleton.size` counts only the active nodes, and `Skeleton.fringe` lists the hole subtrees in inorder.

@decl RotationBST.Geometric.Region

`Region` is another name for the same type, so all the skeleton operations apply to regions unchanged.

::: check
Being *rooted* and *connected* is not a hypothesis: it is built into the type. A region of `s` is a skeleton `before` with `before.tree = s`, and the `node` constructors of a skeleton always form a top part of the tree it describes. The only region with no active node is `hole s`, the whole tree left untouched.
:::

Regions do not store keys, so, as everywhere in the library, keys are inorder ranks computed with an offset `lo` ([Section 1.3](shapes.html#implicit-keys)). Two functions read a region in absolute ranks:

@decl RotationBST.Geometric.Region.keys RotationBST.Geometric.Region.holes

`keys s lo` is the set of ranks of the active nodes when the region's leftmost key has rank `lo`. The root of `node l r` has rank `lo + l.tree.size`: the size of the *whole* left subtree, holes included, since untouched keys still come before it in inorder. `holes s lo` lists the hole subtrees with the rank at which each one starts. A region with $k$ active nodes has $k + 1$ holes, some of which may be empty trees.

@decl RotationBST.Geometric.Region.Same

`Same s t lo` says that two regions differ only in the arrangement of their active nodes. They have the same total size, the same active keys and the same holes at the same offsets. It is the invariant that a step preserves, stated in absolute ranks for the proofs of Wilber's bound ([Chapter 11](wilber.html)) and of the treap construction ([Chapter 20](treaps.html)).

### An example

Take the perfect tree on the ranks $0, \dots, 6$: root $3$, children $1$ and $5$, and leaves $0, 2, 4, 6$. Request $4$, and touch its search path $\{3, 5, 4\}$. Write $L$ for the subtree of $1$ (ranks $0$–$2$) and $R$ for the leaf $6$. The region is
```lean
.node (.hole L) (.node (.node (.hole .nil) (.hole .nil)) (.hole R))
```
Its keys at offset $0$ are $\{3, 4, 5\}$, and its holes are $[(0, L), (4, \mathtt{nil}), (5, \mathtt{nil}), (6, R)]$. One legal rearrangement puts $4$ at the root:
```lean
.node (.node (.hole L) (.hole .nil)) (.node (.hole .nil) (.hole R))
```
It has the same fringe $[L, \mathtt{nil}, \mathtt{nil}, R]$, the same keys and the same holes, and the step costs $3$. In the rotation model the same restructuring costs $2$ rotations, and the request itself is free.

## Steps and executions

@decl RotationBST.Geometric.RegionStep

A `RegionStep s t request` is a record of one search: a region `before` of the old tree `s`, a region `after` of the new tree `t`, a proof that both have the same fringe, and a proof that the request is one of the touched keys. The fringe condition is the whole content of "rearrange the touched nodes and leave everything else alone". It fixes the hole subtrees and their inorder order. Counting fringe entries, it also forces `before` and `after` to have the same number of active nodes, which then occupy the same ranks: `before` and `after` are `Same` at offset $0$.

::: check
- `RegionStep` is a `structure`, not a `Prop`: it is data that carries both regions, so that the cost can be read from it. The executions below quantify over it through their constructor.
- `visits` makes every step touch at least one node, the requested one. A request for the current root therefore costs $1$, like the total cost $T = m + R$ of [Section 5.2](online.html#two-cost-measures) and the unit request charge of the pointer machine.
- The new shape of the region is arbitrary. In particular, the request need not end at the root, and nothing limits how far the region is reshaped.
:::

@decl RotationBST.Geometric.RegionExecution

`RegionExecution s xs u cost` serves the requests `xs` one step at a time from `s`, ends at `u`, and charges each step the number of nodes in its `before` region. It has the same shape as [[RotationBST.Execution]] and [[RotationBST.Pointer.Execution]], with a region step in place of a root access or a pointer search.

::: note Where this model is used
The region model is the hinge between trees and geometry. [Chapter 9](equivalence.html) proves that a set of points in the key–time plane is an offline solution of the geometric problem of [Chapter 8](geometry.html), with exactly $c$ points, if and only if some region execution, from some initial tree, has cost exactly $c$. Each direction rests on a heap invariant ([Chapter 20](treaps.html)). From a region execution, the touched points are the geometric solution, and the proof that they are arborally satisfied keeps the current tree a max-heap of the time each key was last touched ([[Geometric.lastTouch]], [[Geometric.HistoryHeap]]). Rearranging a region preserves this for free, since the touched nodes are on top and all share the latest time. From a geometric solution, the tree at each time is a treap keyed by the time each key is *next* touched, and the region touched at that time is the top of the treap ([[Geometric.Region.project]]).
:::
