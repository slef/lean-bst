# How the models agree

Part I has now described binary search tree executions in five ways: rotation traces on shapes ([Chapter 3](accesses.html)), the same traces on labelled trees ([Chapter 4](keys.html)), a single-pointer machine ([Chapter 6](pointer.html)), rooted regions rearranged at each request ([Chapter 7](regions.html)), and arborally satisfied point sets ([Chapter 8](geometry.html)). This chapter proves that the last of these measures the same thing as the others. Demaine, Harmon, Iacono, Kane and Pătraşcu (2009) showed that the cheapest arborally satisfied superset of the request points has, up to constant factors, the cost of the best BST execution. Every BST question about a fixed sequence thereby becomes a question about points in the plane: no trees, no rotations, only rectangles.

```headline ass-equivalence
title: Offline BST cost and arborally satisfied sets agree up to constant factors
source: Demaine, Harmon, Iacono, Kane and Pătraşcu, *The geometry of binary search trees* (2009)
key: yes
theorems: Geometric.Equivalence.Results.rotations_to_ass Geometric.Equivalence.Results.ass_to_rotations

Fix $n$ keys and a sequence $X = x_0, \dots, x_{m-1}$ of requests. A *geometric solution* for $X$ is a finite set of points $(\text{key}, \text{time})$, with keys below $n$ and times below $m$, that contains every request point $(x_j, j)$ and is arborally satisfied: any two of its points that share neither a key nor a time span a closed rectangle containing a third point of the set. Its cost is its number of points.

1. **Trees to points.** If some tree on $n$ keys serves $X$ by root accesses with $R$ rotations in total, then $X$ has a geometric solution with at most $2R + m$ points.
2. **Points to trees.** If $X$ has a geometric solution with $|E|$ points, then from *every* initial tree on $n$ keys some sequence of root accesses serves $X$ with $R$ rotations, where $m + R \le 2n + 99\,|E|$.

So, with $\mathrm{OPT}_{\mathrm{ASS}}$ the size of a smallest geometric solution and $\mathrm{OPT}$ the least total cost $m + R$ of an execution from a given initial tree,

$$\tfrac12\,\mathrm{OPT}_{\mathrm{ASS}} \;\le\; \mathrm{OPT} \;\le\; 99\,\mathrm{OPT}_{\mathrm{ASS}} + 2n.$$

In Lean, a root-access execution is an [[RotationBST.Execution]] (with its rotation count) and a geometric solution is a [[RotationBST.Geometric.Offline]]` n xs`, whose `points` field is the point set.
```

The chapter proves this in both directions, first exactly for the region model of [Chapter 7](regions.html), then with constants for the rotation model and the pointer machine. It ends with an online version, which turns an online geometric algorithm into an online BST algorithm, and with a table of every correspondence in Part I.

All six theorems are in `Models/Equivalence/Abstract.lean`, under `Geometric.Equivalence.Results`. Their statements use the geometric definitions of [Chapter 8](geometry.html), the region model of [Chapter 7](regions.html), and the BST models of [Chapter 3](accesses.html), [Chapter 5](online.html) and [Chapter 6](pointer.html).

## What has to be compared

A geometric solution has no initial tree. [[Geometric.Offline]]` n xs` is an arborally satisfied set containing the request points $(x_j, j)$, with every point on a key below $n$ and a time below $m$ = `xs.length`, and its cost is its number of points. A BST execution starts from a given tree of size $n$. So each direction of the correspondence must decide what happens to the initial tree:

- From a BST execution to points, the initial tree is simply forgotten.
- From points to a BST execution, the conversion may choose a convenient initial tree, or it may be given one and pay to reach a convenient tree first. Rotations connect any two shapes of size $n$ in at most $2n$ steps ([[RotationBST.Geometry.reset]]), so the price of a prescribed initial tree is an additive $2n$.

All conversions in this chapter except the last are *offline*: they read a whole execution or a whole point set. The last section turns an *online* geometric algorithm into an online BST algorithm.

## Regions are points

The rooted-region model of [Chapter 7](regions.html) is the BST model of the 2009 paper. At each request the algorithm touches a connected region containing the root and the requested key, rearranges it, and pays one unit per touched node. Its executions and point sets are the same objects, with the same cost.

**Theorem (regions are points).** For every number of keys $n$, sequence `xs` and number `cost`, there is an offline geometric solution with exactly `cost` points if and only if some initial tree of size $n$ has a [[Geometric.RegionExecution]] serving `xs` with charge exactly `cost`.

@decl RotationBST.Geometric.Equivalence.Results.ass_iff_region_execution

The equivalence is exact: one touched node per point, in both directions, with no constant.

- From regions to points, record row $j$ as the keys touched by the $j$-th step. Each row contains the request, since a [[Geometric.RegionStep]] must visit it, and the rows together are arborally satisfied. The proof keeps the current tree a max-heap of last-touch times, and finds the third point of every rectangle as a common ancestor in that heap ([Section 20.4](treaps.html#priorities-from-the-past)).
- From points to regions, build a treap whose priorities are next-touch times. Before each row, the keys of that row are exactly the top region of the treap, and rearranging that region alone restores the treap for the next time ([Section 20.2](treaps.html#priorities-from-the-future)). This is the offline step: priorities come from the future of the point set.

::: check
- The initial tree `s` is existential on the right-hand side. The treap construction needs its own initial tree, the treap for the first touches. The final tree `t` is unconstrained.
- Region charges count `step.before.size`, the nodes of the touched region and not the untouched subtrees hanging from it. Point counts and region charges therefore agree exactly.
- `cost` is the same variable on both sides, so the equivalence also says that the minimum costs coincide. A minimum offline solution exists ([[Geometric.Results.optimal_exists]]).
:::

## From trees to points

An execution in the rotation model of [Chapter 3](accesses.html), or on the pointer machine of [Chapter 6](pointer.html), yields a geometric solution that is at most a constant factor larger.

**Theorem (rotations to points).** If a root-access execution from a tree `s` serves the $m$ requests `xs` with $R$ rotations, then `xs` has an offline geometric solution on `s.size` keys with at most $2R + m$ points.

@decl RotationBST.Geometric.Equivalence.Results.rotations_to_ass

The touched nodes of an access are not determined by its rotations: the rotation model allows rotations anywhere, and those far from the request touch nodes the access never needed. The proof reuses the lazy normal form of [Chapter 6](pointer.html#inside-the-lazy-simulation). The rotations of an access that are connected to the root in the rotation graph form an access on their own, and they rearrange a region of at most $2r + 1$ nodes, where $r$ is their number. That region is a region step. The other rotations are postponed to later accesses. Summing over the execution, the region charge plus twice the rotations still pending at the end is at most $2R + m$, and [[Geometric.Equivalence.Results.ass_iff_region_execution]] turns the region execution into points.

**Theorem (pointers to points).** If a pointer execution from `s` serves `xs` at total cost $K$ (requests plus instructions), then `xs` has an offline geometric solution with at most $6K$ points.

@decl RotationBST.Geometric.Equivalence.Results.pointers_to_ass

This composes two earlier bounds. [[RotationBST.Pointer.Results.to_rotations]] turns the pointer execution into a rotation execution with $m + R \le 3K$, and the previous theorem gives at most $2R + m \le 2(m + R) \le 6K$ points.

::: note Lower bounds transfer
These two theorems carry geometric lower bounds back to the tree models. Wilber's interleave bound ([Chapter 11](wilber.html)) is proved once for point sets, $\mathrm{IB} \le 2\,|E|$, and stated for rotation executions as $\mathrm{IB} \le 2(2R + m)$ and for pointer executions as $\mathrm{IB} \le 2 \cdot 6K$, through exactly these conversions.
:::

## From points to trees

Conversely, every geometric solution can be executed by a tree at constant cost per point. Here the initial tree matters, and the two theorems treat it differently.

**Theorem (points to pointers).** For every offline geometric solution $E$ of `xs` on $n$ keys, there is an initial tree of size $n$ from which a pointer execution serves `xs` at total cost at most $33\,|E|$.

@decl RotationBST.Geometric.Equivalence.Results.ass_to_pointers

The construction chooses the initial tree. It runs the treap construction of [Chapter 20](treaps.html) on the pointer machine. Each row is a region of $k$ nodes that must be rearranged, with the request visited along the way. The reshaping lemma [[RotationBST.Pointer.Lazy.Results.reshape]] transforms a region into any other with the same fringe in at most $16k$ instructions. Reshaping once to bring the request to the root, where the cursor is, and once more into the target arrangement costs $1 + 16k + 16k \le 33k$, including the request unit. Summed over the rows, this is $33$ per point.

**Theorem (points to rotations).** For every tree `s` with $n$ nodes and every offline geometric solution $E$ of the $m$ requests `xs` on $n$ keys, some root-access execution from `s` serves `xs` with $R$ rotations, where $m + R \le 2n + 99\,|E|$.

@decl RotationBST.Geometric.Equivalence.Results.ass_to_rotations

The initial shape is prescribed here, not chosen. Two steps produce the constants. First, the pointer execution of `ass_to_pointers` becomes a rotation execution by [[RotationBST.Pointer.Results.to_rotations]], which multiplies by $3$: $99 = 3 \cdot 33$. That execution starts from the treap chosen by the construction, so the theorem first rotates `s` into it, using at most $2n$ rotations ([[RotationBST.Geometry.reset]]), merged into the first access. The suffix of postponed rotations that `to_rotations` leaves at the end is dropped, since no final shape is prescribed.

::: caveat Not stated
The library states the pointer conversion only with a chosen initial tree, and the rotation conversion only with a prescribed one. A pointer conversion from a prescribed initial tree, with an additive $O(n)$ term, would follow the same pattern but is not part of the reading interface.
:::

Together, the four theorems pin down the offline optimum. Writing $\mathrm{OPT}_{\mathrm{ASS}}$ for the size of a smallest geometric solution, every rotation execution from `s` satisfies $\mathrm{OPT}_{\mathrm{ASS}} \le 2R + m$, and the best one satisfies $m + R \le 2n + 99\,\mathrm{OPT}_{\mathrm{ASS}}$. Up to constant factors and the $2n$ for the initial tree, the offline cost of a sequence is a property of a point set.

## Online: from geometric algorithms to BST algorithms

The conversions above see the whole future. The treap construction in particular orders keys by their next touch, which no online algorithm knows. An *online geometric algorithm* ([[Geometric.OnlineAlgorithm]], [Chapter 8](geometry.html)) instead adds the points of each row knowing only the past rows and the current request, and [[Geometric.rowCost]] counts the points it adds. Demaine et al. showed that such an algorithm can be simulated online by a BST with a constant-factor overhead. The library proves this in the following form.

**Theorem (online simulation).** For every online geometric algorithm `A` on $n$ keys there is a single BST [[RotationBST.Algorithm]] of [Chapter 5](online.html) such that, from every initial tree of size $n$ and on every sequence of keys below $n$, its rotation count is at most $6018$ times the number of points `A` adds, plus $6018\,n$.

@decl RotationBST.Geometric.Equivalence.Results.online_bst

- **Online in the strong sense.** The algorithm is chosen before the tree and the sequence. Like every [[RotationBST.Algorithm]], its step receives only the past requests, the current tree and the current request. It may simulate `A` on the past, since `A` sees no future either.
- **Uniform in the initial tree.** One algorithm works for every initial shape of size $n$, and the additive $6018\,n$ pays for adapting to it.
- **The constants are not sharp.** The proof is an existence argument through last-touch supernodes stored in split trees, and its constants are the product of several lemmas. They are explicit only so that the statement is closed.

This theorem is the headline of [Chapter 17](simulation.html), which proves it and states variants with total cost and on the pointer machine ([[Geometric.Simulation.Results.uniform_simulation]] is the same statement). Its main use is GreedyASS ([Chapter 16](greedy.html)): the greedy geometric rule becomes an online BST algorithm whose cost is within a constant factor of its point count.

::: caveat Direction
Only this direction is stated online. The other direction, from an online BST algorithm to an online geometric algorithm, is immediate in the region model (record the touched nodes), but the library states the tree-to-points conversions offline only, as in the previous sections.
:::

## A map of the models

The correspondences of Part I, with $m$ requests, $n$ keys, $R$ rotations, $K$ pointer cost (requests plus instructions) and $|E|$ points:

| From | To | Cost | Trees | Theorem |
|---|---|---|---|---|
| shape executions | labelled executions | equal, both ways | same up to labels | [[RotationBST.Representation.execution_on_keys_iff\|execution_on_keys_iff]] |
| pointer execution | rotation execution | $m + R + q \le 3K$ | final $q$ rotations away | [[RotationBST.Pointer.Results.to_rotations\|to_rotations]] |
| rotation execution | pointer execution | $K \le m + 2nR$ | same final tree | [[RotationBST.Pointer.Results.to_pointer\|to_pointer]] |
| rotation execution | pointer execution | $K + 32d \le 32R + 17m$ | final $d$ rotations away | [[RotationBST.Pointer.Results.to_pointer_lazy\|to_pointer_lazy]] |
| online rotation algorithm | online pointer algorithm | $K + 32d \le 32R + 17m$ | any initial tree | [[RotationBST.Pointer.Lazy.Online.Results.simulation\|simulation]] |
| region execution | point set | equal, both ways | initial tree chosen | [[Geometric.Equivalence.Results.ass_iff_region_execution\|ass_iff_region_execution]] |
| rotation execution | point set | $\lvert E\rvert \le 2R + m$ | initial forgotten | [[Geometric.Equivalence.Results.rotations_to_ass\|rotations_to_ass]] |
| pointer execution | point set | $\lvert E\rvert \le 6K$ | initial forgotten | [[Geometric.Equivalence.Results.pointers_to_ass\|pointers_to_ass]] |
| point set | pointer execution | $K \le 33\,\lvert E\rvert$ | initial chosen | [[Geometric.Equivalence.Results.ass_to_pointers\|ass_to_pointers]] |
| point set | rotation execution | $m + R \le 2n + 99\,\lvert E\rvert$ | initial prescribed | [[Geometric.Equivalence.Results.ass_to_rotations\|ass_to_rotations]] |
| online geometric algorithm | online BST algorithm | $R \le 6018\,(\text{points} + n)$ | any initial tree | [[Geometric.Equivalence.Results.online_bst\|online_bst]] |

Two consequences shape the rest of the book. Bounds can be stated in whichever model is most convenient and moved to the others at a constant cost: Part II states its sequence bounds for rotation-model algorithms, and Wilber's lower bound in [Chapter 11](wilber.html) is proved on point sets. And an algorithm can be designed in whichever model is most convenient: splaying ([Chapter 13](splay.html)) is a rotation algorithm, GreedyASS ([Chapter 16](greedy.html)) is a geometric one, and Tango ([Chapter 19](tango.html)) maintains a tree whose edges are marked by preferred paths.
