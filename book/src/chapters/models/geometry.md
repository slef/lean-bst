# The geometric view

Run a BST algorithm on a request sequence and record, for each request, the set of nodes it touches. Plot each touched key $x$ at time $t$ as the point $(x, t)$, with keys on the horizontal axis and time going upward. Demaine, Harmon, Iacono, Kane and Pătraşcu [-@demaine2009] observed that the point sets arising this way have a purely geometric description. Whenever two points do not share a row or a column, the rectangle they span contains a third point. Conversely, every point set with this property, which they call **arborally satisfied**, is the touch set of some BST execution. The cost of an execution is its number of points.

This turns BST optimization into a covering problem in the plane. The offline optimum for a request sequence is, up to a constant factor, the size of the smallest arborally satisfied superset of the request points $\{(x_t, t)\}$. Lower bounds become statements about rectangles, and Wilber's bound of [Chapter 11](wilber.html) is proved here against every arborally satisfied set. Algorithms become rules that complete one row at a time, and the most natural such rule, GreedyASS ([Chapter 16](greedy.html)), is conjectured to be dynamically optimal.

This chapter states the model: points and arborally satisfied sets, offline solutions, and online algorithms that add one row per request. Its theorems are small facts about these definitions. The result that makes the geometric view worth having, that point counts and BST costs agree up to constant factors, is the key result of [Chapter 9](equivalence.html#claim-ass-equivalence), and every definition it needs is in this chapter or in [Part I](part-models.html). The definitions are in `Models/Geometric/Definitions/Abstract.lean`, `Online/Abstract.lean`, `Offline/Abstract.lean` and `Static/Abstract.lean`, and the theorems in `Models/Geometric/Abstract.lean`. The correspondence with the tree models is [Chapter 9](equivalence.html).

## Points and rectangles

@decl RotationBST.Geometric.Point RotationBST.Geometric.Rectangle

A point is a pair (key, time) of natural numbers. Keys are inorder ranks, as in every other model, and times number the requests from $0$. `Rectangle a b p` says that `p` lies in the closed axis-parallel rectangle with opposite corners `a` and `b`; the corners need not be the lower left and upper right ones.

@decl RotationBST.Geometric.ASS

A finite point set `P` is arborally satisfied when every pair of points `a`, `b` of `P` with different keys and different times spans a rectangle containing a third point of `P`. The third point may lie on the boundary, including at one of the two other corners.

::: check
- Pairs on a common row or column impose nothing: `a.1 ≠ b.1 → a.2 ≠ b.2 → …`. Their "rectangle" is a segment.
- `p ≠ a ∧ p ≠ b` excludes the two corners themselves, and nothing else. A point at the corner $(a_1, b_2)$ satisfies the rectangle.
- Pairs are ordered, so each rectangle is checked twice. This is harmless.
:::

Since `P` is a finite set, every quantifier in `ASS` ranges over a finite set, and the library makes this explicit with decidability instances. They let small cases be checked by `decide`, and they make the brute-force GreedyASS of [Chapter 16](greedy.html) executable.

@decl RotationBST.Geometric.instDecidableRectangle RotationBST.Geometric.instDecidableASS RotationBST.Geometric.instDecidableCompletion

### An example

Serve the requests $1, 3, 0, 2$ on four keys with the fixed tree whose root is $1$, with left child $0$, right child $3$, and $2$ the left child of $3$. Each search touches its root-to-key path: $\{1\}$ at time $0$, then $\{1, 3\}$, then $\{0, 1\}$, then $\{1, 2, 3\}$. These are $8$ points, which is the fixed-tree cost [[RotationBST.StaticTree.cost]] of the sequence: one unit per request plus its depth.

The request points alone, $(1,0), (3,1), (0,2), (2,3)$, are not arborally satisfied: the rectangle of $(1,0)$ and $(3,1)$ is empty. The touched points are. In the figure, the "Requests only" and "GreedyASS" buttons load the two sets (GreedyASS happens to produce exactly the touches of this tree). Click two points to inspect their rectangle, or click cells to add and remove points; the panel finds an empty rectangle whenever there is one.

@viz geometric {"mode": "edit", "n": 4, "requests": [1, 3, 0, 2], "start": "requests", "title": "Requests 1 3 0 2: add points until every rectangle is satisfied"}

## Why tree executions are satisfied

Here is the classical argument for a fixed tree, where each request touches its search path. Take two touched points $(x, t)$ and $(y, u)$ with $x < y$ and $t \ne u$, and let $\ell$ be the lowest common ancestor of $x$ and $y$, so $x \le \ell \le y$. If $\ell \ne x$, then $\ell$ is a proper ancestor of $x$, so it was touched at time $t$, and $(\ell, t)$ is a third point in the rectangle. If $\ell = x$, then $x$ is an ancestor of $y$, so $(x, u)$ was touched and lies in the rectangle. For trees that change over time the same argument works, because the lowest common ancestor of two keys can only change at a time when it is touched.

The library states the fixed-tree case for any family of touched sets that are rooted and connected in each row:

@decl RotationBST.Geometric.RootedRows

`RootedRows t lo P` reads the tree top-down. At a node whose key is $r$ = `lo + l.size`, every point of `P` (all of which have keys in this subtree) forces $(r, \text{its time})$ into `P`: if anything below or at this node is touched at some time, the node itself is touched at that time. The points with keys below $r$ must satisfy the same condition in the left subtree, and those above $r$ in the right subtree. The empty tree admits no points.

::: check
Keys outside the tree's range are ruled out, not ignored. A point with key below `lo` is passed to the left subtree at every level, and eventually reaches a `nil`, where `P = ∅` fails. The same holds for keys at or beyond `lo + t.size`.
:::

**Theorem (fixed trees give satisfied sets).** For every tree `t`, offset `lo` and finite point set `P`, if `RootedRows t lo P` holds then `P` is arborally satisfied.

@decl RotationBST.Geometric.Results.fixed_tree_view

The proof is the induction above: a pair on the same side of the root is handled by the subtree, and a pair separated by the root, or containing it, finds a root point on one of its two rows. The dynamic version of the argument is part of the equivalence theorems of [Chapter 9](equivalence.html).

## Offline solutions

Requests are the points $(x_t, t)$:

@decl RotationBST.Geometric.requestsAt

`requestsAt time xs` places the $j$-th request on row `time + j`. With `time = 0`, request $j$ is the point $(x_j, j)$. Repeated keys are allowed; they lie in different rows.

@decl RotationBST.Geometric.Solution

A solution for a set of requests is an arborally satisfied superset of them. Its cost is its number of points.

@decl RotationBST.Geometric.Offline

An offline solution for $n$ keys and the sequence `xs` is a solution for `requestsAt 0 xs` whose points all have keys below $n$ and times below $m$ = `xs.length`. The set is chosen with the whole sequence in view, hence "offline". The bound rules out extra columns, which would be keys that do not exist, and extra rows, which would be work done after the last request.

::: check
- `Offline` extends `Solution`, so `E.points`, `E.contains` and `E.satisfied` are its fields, together with `E.bounded`.
- No initial tree is mentioned. A geometric solution corresponds to a BST execution from an initial tree of its choosing. Starting from a prescribed tree costs an extra $O(n)$, and the theorems of [Chapter 9](equivalence.html) state this term explicitly.
:::

Two facts about offline solutions. Every solution contains the $m$ request points, so its cost is at least $m$, just as the total cost of a BST execution is at least the number of requests.

**Theorem (requests are paid for).** Every offline solution for a sequence of $m$ requests has at least $m$ points.

@decl RotationBST.Geometric.Results.request_lower_bound

**Theorem (an optimum exists).** For every sequence `xs` of keys below $n$, there is an offline solution $E$ whose number of points is at most that of every offline solution for $n$ keys and `xs`.

@decl RotationBST.Geometric.Results.optimal_exists

Existence of *some* solution is the only content, since costs are natural numbers. The full grid $\{0, \dots, n-1\} \times \{0, \dots, m-1\}$ is a solution: every nondegenerate rectangle with corners on the grid contains its two other corners. The library instead runs the GreedyASS sweep of [Chapter 16](greedy.html) and takes the least cost with `Nat.find`. The minimum cost is the geometric counterpart of the offline BST optimum.

## Row by row

A BST algorithm serves requests in order, so its points arrive one row at a time. Rows are built from sets of keys:

@decl RotationBST.Geometric.row RotationBST.Geometric.History

`row time keys` puts the keys on one row. `History n time P` says that `P` uses only the $n$ keys and only rows strictly before `time`: it describes what has happened before the current request.

@decl RotationBST.Geometric.Completion

A legal row for the request at time `time` contains the request, uses only existing keys, and keeps the whole set arborally satisfied once it is added. The condition is checked on the union `P ∪ row time keys`, so a new row must satisfy the rectangles it forms with every old point, not only among its own points. Old rows cannot change.

Among legal rows, the smallest one is a natural choice:

@decl RotationBST.Geometric.GreedyRow

`GreedyRow` specifies the greedy rule by a property: a legal row of minimum cardinality. It does not say that such a row is unique, or how to find it. [Chapter 16](greedy.html) proves that it is unique and is computed by a simple sweep.

### Online algorithms

@decl RotationBST.Geometric.OnlineAlgorithm

An online geometric algorithm is a function from the current time, the current request and the points so far to the keys of the new row, with a certificate. Whenever the history is bounded and arborally satisfied and the request is valid, the row is legal. The step receives no future requests, and this is the only sense of "online".

::: check
- The certificate must hold for *every* satisfied history, not only for those the algorithm itself produces. This is stronger than necessary, and GreedyASS meets it.
- The step sees the past points but not the past request sequence. It cannot tell which point of an old row was the request. For GreedyASS this does not matter.
- Computation is uncharged, as in [Section 5.1](online.html#online-algorithms). Only points count.
:::

@decl RotationBST.Geometric.fill RotationBST.Geometric.rowCost

`fill step time P xs` runs a step function from history `P`, numbering new rows consecutively from `time`. `rowCost` charges one unit for each point added, the request included, so it is the geometric analogue of the total cost $T = m + R$.

An online run is an offline solution, and its cost is exactly its number of points.

**Theorem (online runs are solutions).** For every online geometric algorithm `A` on $n$ keys and every sequence `xs` of keys below $n$, the points that `A` produces on `xs`, starting from the empty history, form an offline solution with exactly `rowCost` points.

@decl RotationBST.Geometric.Results.online_solution

The cardinality claim needs a short argument: each row is added at a fresh time, so no two rows share a point.

Conversely, every offline solution can be read row by row as a sequence of legal moves:

@decl RotationBST.Geometric.pastPoints RotationBST.Geometric.keysAt

`pastPoints P time` is the part of `P` strictly before `time`, and `keysAt P time` the keys on row `time`.

**Theorem (rows of a solution are legal).** If a finite point set `P` is arborally satisfied, has keys below $n$ and contains the request point at time `time`, then the row of `P` at `time` is a legal completion of the rows of `P` before it.

@decl RotationBST.Geometric.Results.offline_row

The reason is that arboral satisfaction is inherited by every prefix of the rows. A rectangle spanned by two points at times at most $t$ has all its points at times at most $t$, so the third point it contains is in the prefix too. The rows of an offline solution are legal, but each may have been chosen with knowledge of later requests, and an online algorithm cannot reproduce them in general.

Reading an offline solution row by row also accounts for all of its points. Here `scheduleCost P time` adds the row sizes of the first `time` rows.

**Theorem (rows account for every point).** For every offline solution $E$ of a sequence of $m$ requests, the sizes of its first $m$ rows add up to its number of points.

@decl RotationBST.Geometric.scheduleCost RotationBST.Geometric.Results.offline_cost

For an offline solution all rows are below $m$, so the first $m$ rows hold every point.

::: note What comes next
Online and offline geometric algorithms now mirror online algorithms and offline executions in the BST models. [Chapter 9](equivalence.html) makes the correspondence precise: offline, point counts and BST costs agree up to constant factors (exactly, for the region model), and online, every geometric algorithm can be simulated by an online BST algorithm. The simulation is the subject of [Chapter 17](simulation.html), and GreedyASS, the geometric algorithm it is usually applied to, is [Chapter 16](greedy.html).
:::
