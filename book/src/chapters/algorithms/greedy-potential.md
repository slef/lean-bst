# Items, colors and potential

Iacono and Langerman [-@iacono2016] prove their Theorem 3.1 with a potential function. GreedyASS runs on its own, and a lazy finger moves in a fixed leaf-oriented reference tree $T$ alongside it. The potential is chosen so that every point GreedyASS adds is paid for, up to a constant, by a drop in the potential or by the finger's movement. This section defines that potential and proves its local properties. [Chapter 26](greedy-amortized.html) does the bookkeeping, request by request, and concludes the theorem.

The potential has two parts, both read off a snapshot of the execution.

- **Item potentials.** Every key is an *item*. Once GreedyASS has touched it, its potential depends on where its most recent access sits in the picture of the points so far, and on distances in $T$. Each item gets one of four colors, red, green, blue or purple. The color selects one of four candidate values, each a node count along a path of $T$.
- **Virgin potential.** Each component of the reference forest ([Chapter 24](reference-forest.html)) that has not been touched since it became a root carries $12$ units.

The analysis of one request has two phases. In Phase I the finger moves from the previous request to the new one, and the reference forest changes by merges and splits. In Phase II GreedyASS adds its row. Most results below say what one of these phases can do to one part of the potential.

::: note Do you need this section?
Not to check Theorem 3.1. Its statement, [[Amortized.Results.cost]], mentions only the GreedyASS sweep, its point count and the reference cost. Nothing defined here appears in it, so these definitions need not be trusted: whatever they say, Lean has checked the proof that uses them. Read this section to follow the proof, or to see how closely the formal potential follows the paper.
:::

Two results here stand out as milestones of the proof. The first is a geometric *barrier*: once a key is accessed, as long as all requests are on one side of it, no access happens on the other side (Lemma 3.4 of the paper). The second is its consequence for the reference forest: each GreedyASS row touches at most two components that were already accessed earlier and have remained roots since (Lemma 3.7). This is why virgin potential pays for most of the touched components (Lemma 3.8).

```headline greedy-potential-old-roots
title: Each GreedyASS row touches at most two old roots
source: @iacono2016
theorems: Geometric.GreedyASS.Virgin.Results.count Geometric.GreedyASS.Virgin.Results.decrease
skip: Geometric.instDecidableVisible | A decidability instance, together with the one for rectangles it uses, only lets Lean compute the filter in `greedySweep`. Any two instances for the same proposition agree, so they cannot change which keys the sweep keeps.

Let $T$ be a leaf-oriented reference tree whose $\ell$ leaves are the keys $lo, \dots, lo + \ell - 1$, and run GreedyASS from the empty point set on a sequence of requests from that range. Before the row for the current request $r$ is added, call a component of the reference forest of $r$ *old* if, at some earlier time, GreedyASS touched one of its keys while it was a root, and it has remained a root at every search since then, up to and including $r$. Call the other components *virgin*. Then the row GreedyASS adds for $r$ touches at most two old components.

Give each virgin component $12$ units of potential. If the row touches $k$ components in all, at least $k - 2$ of them are virgin, so the virgin potential drops from $V$ to some $V'$ with

$$V' + 12\,k \;\le\; V + 24 .$$

These are the paper's Lemmas 3.7 and 3.8. The second is stated additively, so that it is meaningful when $k < 2$.
```

The definitions are in `Algorithms/GreedyASS/Items/Definitions/Abstract.lean`, `Barrier/Definitions/Abstract.lean`, `Virgin/Definitions/Abstract.lean` and `Potential/Definitions/Abstract.lean`. The theorems are in the `Abstract.lean` file next to each.

## Overview

Here is the whole construction in brief. The details follow in the same order.

Picture the GreedyASS points as in [Chapter 8](geometry.html), keys left to right and time upward. For each touched key $x$, its **most recent access** is the highest point in column $x$. It lies on some row, the item's *access row*. Its **neighbors** are the nearest keys to its left and to its right that were touched in that same row. The item is classified by what happened around it since that row:

- it is **external** if it was the leftmost or rightmost point of its row;
- otherwise it is **glancing** if every later point lies strictly on one side of its column;
- otherwise it is **internal**: later points lie on both sides.

The external items are the points that are visible from far to the left or far to the right: their upper-left or upper-right quadrant is empty. They form two staircases.

The four candidate values compare the item with the reference tree $T$. All distances count nodes, both endpoints included.

| color | value | used for |
|---|---|---|
| red | distance from $x$ to the lowest common ancestor of its two neighbors | internal and glancing items |
| green | one more than the distance from $x$ to the lowest common ancestor of the nearest external items on either side | external items |
| blue | one more than the distance from $x$ to the root of its component in the current reference forest | external items |
| purple | the largest blue value of $x$ since its most recent access | glancing items |

An internal item is red. A glancing item takes the smaller of red and purple, and an external item the smaller of green and blue. An external item touched by the latest row, a *top corner*, is always blue. The item's potential is the value of its color. The total potential adds up the item potentials and $12$ for each virgin root.

## Items in the geometric view

All definitions in this section take an arbitrary finite point set `P`, a *snapshot*, not necessarily produced by GreedyASS. Theorems add the hypotheses they need: that `P` is arborally satisfied ([[Geometric.ASS]]), or that it is a [[Geometric.History]], with all points strictly before the time of the next row.

### Most recent accesses

@decl Geometric.GreedyASS.Items.greatest Geometric.GreedyASS.Items.least

`greatest` and `least` return the maximum and minimum of a finite set of naturals, or `none` for the empty set. They are written with `Option` so that a missing neighbor or an unseen key is a value, not a hypothesis.

@decl Geometric.GreedyASS.Items.times Geometric.GreedyASS.Items.latest

`times P key` is the set of times at which column `key` has a point, and `latest P key` is the latest of them, the time of the most recent access. A key that was never touched has `latest = none`. There is no artificial access at time $-1$ or at the initial tree.

@decl Geometric.GreedyASS.Items.Active

A point `q` is **active** in `P` if it belongs to `P` and is the highest point of its column. The active points are exactly the most recent accesses, one per touched key:

@decl Geometric.GreedyASS.Items.Results.most_recent

### Neighbors on the access row

@decl Geometric.GreedyASS.Items.leftNeighbor Geometric.GreedyASS.Items.rightNeighbor

The neighbors of a point `q` are the nearest keys touched at the same time `q.2`, strictly to its left and strictly to its right. [[Geometric.keysAt]] `P q.2` is the set of keys of that row. These are the paper's $L\text{-}\mathrm{Int}$ and $R\text{-}\mathrm{Int}$, taken at the item's most recent access. Their characterizations are what one expects:

@decl Geometric.GreedyASS.Items.Results.left_neighbor Geometric.GreedyASS.Items.Results.right_neighbor

### External, glancing and internal

@decl Geometric.GreedyASS.Items.LeftExternal Geometric.GreedyASS.Items.RightExternal Geometric.GreedyASS.Items.External

An active point is **left external** if no point of its own row is to its left, and **right external** if none is to its right. A point alone on its row is both. The definition looks only at the row, not at the rest of the picture. In an arborally satisfied set this is the same as an empty quadrant, closed on both sides: nothing at or to the left of `q` is at or above it, except `q` itself.

@decl Geometric.GreedyASS.Items.Results.quadrants

So the left-external points are the corners of the staircase seen from the far left: a request to the left of every key would see exactly these points. Going from left to right along this staircase, the points rise. The right-external staircase is the mirror image. The two staircases do not cross:

@decl Geometric.GreedyASS.Items.Results.external_chains

Every left-external key is at most every right-external key. Otherwise one of the two points would lie in the other's empty quadrant.

@decl Geometric.GreedyASS.Items.LeftGlancing Geometric.GreedyASS.Items.RightGlancing Geometric.GreedyASS.Items.Glancing

A nonexternal active point is **left glancing** if every point that is strictly later lies strictly to its right. Since the access, everything has happened on the right, and the left part of the picture has frozen. This is the paper's condition that the quadrant strictly above and at or to the left of the most recent access is empty. Right glancing is symmetric. A point whose row is the latest row of the snapshot has no later points, so if it is not external, it is both left and right glancing.

@decl Geometric.GreedyASS.Items.Internal

An **internal** point is active and neither external nor glancing: some later point lies strictly to its left, and some strictly to its right. (No later point is in its own column, since it is active.)

@decl Geometric.GreedyASS.Items.instDecidableActive Geometric.GreedyASS.Items.instDecidableLeftExternal Geometric.GreedyASS.Items.instDecidableRightExternal Geometric.GreedyASS.Items.instDecidableExternal Geometric.GreedyASS.Items.instDecidableLeftGlancing Geometric.GreedyASS.Items.instDecidableRightGlancing Geometric.GreedyASS.Items.instDecidableGlancing Geometric.GreedyASS.Items.instDecidableInternal

All these classes quantify over the finite set `P`, so they are decidable, and the coloring below can branch on them.

**Theorem (three classes).** Every active point is external, glancing or internal, and exactly one of the three.

@decl Geometric.GreedyASS.Items.Results.classes

A nonexternal point has both neighbors, and the neighbors are missing exactly on the external sides:

@decl Geometric.GreedyASS.Items.Results.missing_neighbors Geometric.GreedyASS.Items.Results.neighbors

### An example

Run GreedyASS on the five keys $0, \dots, 4$ with requests $0, 2, 1, 0, 3, 4$. The sweep of [Chapter 21](greedy.html) adds $12$ points:

```text
time 5   request 4   ·  ·  ·  ●  ●
time 4   request 3   ●  ·  ●  ●  ·
time 3   request 0   ●  ·  ·  ·  ·
time 2   request 1   ●  ●  ●  ·  ·
time 1   request 2   ●  ·  ●  ·  ·
time 0   request 0   ●  ·  ·  ·  ·
          key        0  1  2  3  4
```

The active points are $(0,4)$, $(1,2)$, $(2,4)$, $(3,5)$ and $(4,5)$.

- $(0,4)$ is the leftmost point of row $4$, so it is left external.
- $(1,2)$ has neighbors $0$ and $2$ on row $2$. Later, $(0,3)$ lies to its left and $(2,4)$ to its right, so it is internal.
- $(2,4)$ has neighbors $0$ and $3$ on row $4$. The only later points, $(3,5)$ and $(4,5)$, are to its right, so it is left glancing.
- $(3,5)$ and $(4,5)$ are the left-external and right-external points of the latest row.

The left-external staircase is $(0,4), (3,5)$. It rises from left to right, and its upper-left quadrants are empty. The right-external staircase is just $(4,5)$.

### The latest row and its corners

The newest row plays a special role: its two extreme points are the *top corners*, which the coloring always makes blue.

@decl Geometric.GreedyASS.Items.LatestRow Geometric.GreedyASS.Items.instDecidableLatestRow

`LatestRow P stamp` says that no point of `P` is later than `stamp`; like the classes above, it is decidable. It is a property of the snapshot, not of a separate clock. The distinction matters in Phase I, where the reference forest has already moved to the new request but the old point set is still in place. The old latest row then still counts as the latest row.

@decl Geometric.GreedyASS.Items.corners

`corners P time keys` is the set of keys of a new row `keys`, at time `time`, that are external once the row is added. These are the paper's top corners.

@decl Geometric.GreedyASS.Items.Results.latest_corners Geometric.GreedyASS.Items.Results.top_corners

Every nonempty snapshot has a left-external and a right-external point on its latest row: the extreme points of that row. A new row has at most two top corners, its leftmost and rightmost keys. Once the row is completed, "on the latest row" and "at the new time" agree, provided the row is nonempty:

@decl Geometric.GreedyASS.Items.Results.latest_row

Finally, no active point strictly to the left of a left-external point, or strictly to the right of a right-external point, is on the latest row:

@decl Geometric.GreedyASS.Items.Results.noncorner

### What a new row changes

In Phase II GreedyASS adds a row `row time keys` at a time later than every old point. The theorems of this subsection hold for any such row, not only for the one GreedyASS chooses. For a column that the row does not touch, very little changes:

**Theorem (untouched items, Fact 3.3).** Let `P` be a history before time `time`, and let `q` be active in `P` with `q.1` not among the new keys. After the row is added, `q` is still the most recent access of its column, it has the same two neighbors, and it is external if and only if it was before.

@decl Geometric.GreedyASS.Items.Results.unchanged

The paper's Fact 3.3 is the statement about neighbors. The rest is immediate from the definitions: all of these depend only on `q`'s own row and column, and the new row is neither.

Glancing status can only be lost. A left-glancing item stays left glancing exactly when the whole new row is strictly to its right. An internal item stays internal:

@decl Geometric.GreedyASS.Items.Results.glancing_update Geometric.GreedyASS.Items.Results.internal

The keys of the new row itself have nothing above them, so none of them is internal:

@decl Geometric.GreedyASS.Items.Results.accessed

## The barrier

Lemma 3.4 of the paper is a geometric fact about GreedyASS alone. Suppose key $k$ is accessed at time $s$, and every request after time $s$ is at least $k$. Then GreedyASS never accesses a key smaller than $k$ after time $s$. The point $(k, s)$ is a *barrier*: every old point to its left spans, with any later request at or to its right, a rectangle containing $(k, s)$, so no such old point is visible again.

The library first isolates the invariant that makes this work:

@decl Geometric.GreedyASS.Barrier.Left Geometric.GreedyASS.Barrier.Right

`Barrier.Left P key stamp` says that `(key, stamp)` is a point of `P` and that no point strictly to its left is later than `stamp`. It does not require `stamp` to be the latest time. One sweep cannot cross a barrier, and a stream of sweeps preserves it:

@decl Geometric.GreedyASS.Barrier.Results.left_step Geometric.GreedyASS.Barrier.Results.right_step

@decl Geometric.GreedyASS.Barrier.Results.left_stream Geometric.GreedyASS.Barrier.Results.right_stream

`left_step` concerns one [[Geometric.greedySweep]] at any time `time ≥ stamp`, for a request `request ≥ key`: every key of the row is at least `key`. `left_stream` runs the sweep with [[Geometric.fill]] on a whole list of requests that are all at least `key`. The barrier is still a barrier at the end, and the points strictly to the left of `key` are exactly the old ones. Neither statement needs `P` to be arborally satisfied.

Right after `(key, stamp)` is accessed, row `stamp` is the latest row, so the barrier condition holds automatically. This gives the paper's lemma:

**Theorem (Lemma 3.4).** Let `P` be a history before time `stamp + 1` containing `(key, stamp)`. Run GreedyASS on requests that are all at least `key`, from time `stamp + 1`. Then every point added after time `stamp` has key at least `key`. Symmetrically, for requests that are all at most `key`.

@decl Geometric.GreedyASS.Barrier.Results.no_left Geometric.GreedyASS.Barrier.Results.no_right

The paper assumes the later requests are strictly greater than $k$; the library allows them to equal $k$. Two accessed endpoints on the same row confine all later accesses to the interval between them, as long as the requests stay in that interval:

@stmt Geometric.GreedyASS.Barrier.Results.interval

[Chapter 24](reference-forest.html) combines the barrier with the reference forest ([[Reference.Results.barrier]]): if a component has stayed a root since one of its keys was accessed, all later searches are on one side of that key, and so are all later accesses.

## Virgin roots

The second part of the potential lives on the reference forest. After a search for $x$, [[Reference.forest]] lists the components hanging off the path to $x$, together with $x$ itself as a one-leaf component. A component is **virgin** while none of its keys has been accessed since it became a root. Each virgin root holds $12$ units. When a row touches a virgin root, the root stops being virgin, and its $12$ units pay for accesses. When the finger moves and the forest changes, new roots are born virgin, and the lazy finger pays for them.

Unlike the item definitions, these definitions run GreedyASS itself, from the empty point set at time $0$:

@decl Geometric.GreedyASS.Virgin.points Geometric.GreedyASS.Virgin.keys

`points history` is the set of GreedyASS points after serving `history`, and `keys history request` is the row GreedyASS adds for the next request, at time `history.length`.

@decl Geometric.GreedyASS.Virgin.NonVirgin

`NonVirgin t lo history request c` describes the moment just before the row for `request` is added. It holds when the history splits as `before ++ first :: after` such that:

- the row GreedyASS added for `first` touched a key of `c`; and
- `c` was a root of the reference forest at the search for `first`, at every later search in the history, and at the current `request`.

So `c` was accessed while it was a root, and has stayed a root without interruption. The definition is a function of the history and the reference tree. It is an observation of the proof, not state that GreedyASS keeps. The paper's definition is the same, read the other way: a root that has been a root continuously since time $k$ is $i$-virgin if none of its keys was accessed at times $k$ to $i$. The paper's count includes the current row $i$. The library's `NonVirgin` stops just before it, and `update` below adds the current row.

@decl Geometric.GreedyASS.Virgin.touched Geometric.GreedyASS.Virgin.oldTouched Geometric.GreedyASS.Virgin.roots

`touched` is the set of roots of the current forest that contain a key of the new row; the paper's $t_i$ is their number. `oldTouched` is the set of those that are not virgin. `roots` is the set of virgin roots before the row is added.

@decl Geometric.GreedyASS.Virgin.before Geometric.GreedyASS.Virgin.after

`before` is the virgin potential before the new row, $12$ per virgin root. `after` is the virgin potential after it: only the virgin roots the row does not touch keep their $12$ units.

### How virgin status evolves

Nothing is old before the first request:

@decl Geometric.GreedyASS.Virgin.Results.initial

**Theorem (one step of history).** After `request` is served, a component is old at the next request `next` exactly when it is a root of `next`'s forest and either it was already old at `request`, or it was a root at `request` and the row for `request` touched it.

@decl Geometric.GreedyASS.Virgin.Results.lifetime

The "root of `next`'s forest" condition is what makes a component lose its old status when the finger's movement merges it away or splits it. If it reappears later, it is reborn virgin. Two consequences follow. Taking `next = request`, the virgin roots after the row are those before it minus the touched ones, so `after` is really the virgin potential of the completed history. And a component that is a root at both the old and the new request has the same status for both:

@decl Geometric.GreedyASS.Virgin.Results.update Geometric.GreedyASS.Virgin.Results.survival

### Phase II: at most two old roots

An old root constrains the next row. It contains a key that was accessed while it was a root, and since then every search has been on one side of that key ([[Reference.Results.point_side]]). By the barrier, every access is then on that side too, including the current row:

@decl Geometric.GreedyASS.Virgin.Results.barrier

This plays the role of the paper's Lemma 3.6. The hypothesis `valid` says that every request, past and current, is a leaf of `t`.

Now the components of the forest are disjoint intervals in key order. If an old component is touched by the row, the whole row lies on one side of one of its keys. So, among the touched components, an old one can only be the leftmost or the rightmost.

**Theorem (Lemma 3.7).** For valid requests, the row GreedyASS adds for the current request touches at most two old roots of the current forest.

@decl Geometric.GreedyASS.Virgin.Results.count

The count includes the searched one-leaf component, which may be old too. Every touched virgin root gives up its $12$ units, which is an exact identity:

@decl Geometric.GreedyASS.Virgin.Results.exact

Combined with the count, this gives the paper's Lemma 3.8, which says that at least $12(t_i - 2)$ units of virgin potential are released in Phase II. The library states it without subtraction, so it is also correct when fewer than two roots are touched:

**Theorem (Lemma 3.8).** For valid requests, $\mathit{after} + 12 \cdot |\mathit{touched}| \le \mathit{before} + 24$.

@decl Geometric.GreedyASS.Virgin.Results.decrease

### Phase I: new roots are born virgin

When the finger moves from `old` to `new`, the forest changes by a sequence of merges and splits ([[Transitions.Trace]], [Chapter 24](reference-forest.html)). A split creates two roots and a merge creates one ([[Transitions.introductions]]). Each new root may be virgin, so the virgin potential can grow by $12$ per root created. Old roots that survive keep their status, by `survival`.

@decl Geometric.GreedyASS.Virgin.Results.transition Geometric.GreedyASS.Virgin.Results.forest_change

The left side, `before t lo (history ++ [old]) new`, is the virgin potential in the new forest after `old` was served: the virgin part of the paper's intermediate potential $\Phi'_i$. The right side starts from `after t lo history old`, the potential after `old`'s row. `transition` holds for every trace between the two forests. `forest_change` applies it to [[Transitions.plan]], the concrete route that merges up from `old` to the lowest common ancestor and then splits down to `new`.

The paper's Lemma 3.2 allows $24$ units for each merge or split, item and virgin potential together. The virgin part uses at most $24$ for a split and $12$ for a merge, so it leaves $12$ units per merge for the item potentials:

@decl Geometric.GreedyASS.Virgin.Results.phase_one_budget

Here [[Transitions.edges]] is the number of reference edges between `old` and `new`, and the plan has one event per edge ([[Transitions.Results.transition]]). Using the reserved $12$ units per merge for the item potentials is part of [Chapter 26](greedy-amortized.html).

### The example: virgin roots

Take the reference tree $T$ = `node (node nil nil) (node nil (node nil nil))`, with leaves $0, \dots, 4$:

```text
           •
         /   \
        •     •
       / \   / \
      0   1 2   •
               / \
              3   4
```

The searches for $3$ and for $4$ give the same forest: the subtree on $\{0,1\}$ and the single leaves $\{2\}$, $\{3\}$, $\{4\}$. Just before the last row, the old roots are $\{0,1\}$, $\{2\}$ and $\{3\}$, which the row at time $4$ touched. Only $\{4\}$ is virgin, so the virgin potential is $12$. The last row $\{3,4\}$ touches two roots, one old and one virgin. Afterwards no root is virgin, so the virgin potential is $0$. Lemma 3.8 reads $0 + 12 \cdot 2 \le 12 + 24$.

## Four candidate values

Every value is a node count in the reference tree, computed with the distances of [Chapter 24](reference-forest.html): [[Distance.toLCA]] `t lo x a b` is the number of nodes on the path from leaf $x$ up to the lowest common ancestor of leaves $a$ and $b$, and [[Distance.toRoot]] `c x` is the number of nodes from $x$ up to the root of a component $c$. A value that the paper calls infinite is `⊤` in `WithTop Nat`.

### Red: the access row's neighbors

@decl Geometric.GreedyASS.Potential.red

`red t lo P q` is the node distance from `q.1` to the lowest common ancestor of its two neighbors on its access row, or `⊤` if a neighbor is missing. This is the paper's $\mathrm{Red}_i(x) = d(x, \mathrm{Lca}(L\text{-}\mathrm{Int}, R\text{-}\mathrm{Int}))$, where $d$ counts nodes. The value only makes sense when the neighbors surround `q.1`. For nonexternal points they do, and red is finite:

@decl Geometric.GreedyASS.Potential.Results.red_defined

A row that does not touch `q`'s column changes neither its neighbors nor its red value (Lemma 3.14). The library proves this for every untouched active point, external or not:

@decl Geometric.GreedyASS.Potential.Results.red_stable

### Green: the nearest external items

@decl Geometric.GreedyASS.Potential.externalKeys Geometric.GreedyASS.Potential.leftExternal Geometric.GreedyASS.Potential.rightExternal

`externalKeys P` is the set of columns whose active point is external. `leftExternal P x` and `rightExternal P x` are the nearest such columns strictly to the left and right of `x`, the paper's $L\text{-}\mathrm{Ext}$ and $R\text{-}\mathrm{Ext}$:

@decl Geometric.GreedyASS.Potential.Results.externals Geometric.GreedyASS.Potential.Results.left_neighbor Geometric.GreedyASS.Potential.Results.right_neighbor

@decl Geometric.GreedyASS.Potential.green

`green t lo P x` is one more than the node distance from `x` to the lowest common ancestor of its external neighbors, and `⊤` if either is missing. In particular the leftmost and the rightmost external items have infinite green value, as in the paper:

@decl Geometric.GreedyASS.Potential.Results.green_infinite

### Blue: the current forest

@decl Geometric.GreedyASS.Potential.blue

`blue t lo searched x` follows the search path to `searched` from the root. At the first node where the path to `x` leaves it, `x` is in the sibling subtree, which is a component of the forest. The value is then the edge depth of `x` in that component plus $2$. If the two paths never separate, `x` is the searched leaf, and the value is $2$. In terms of [Chapter 24](reference-forest.html), blue is the paper's $\mathrm{Blue}_i(x) = d(x, r_i(x)) + 1$, with $r_i(x)$ the root of `x`'s component:

@decl Geometric.GreedyASS.Potential.Results.blue_root

The blue value is always at least $2$. `blue` is defined by the same recursion for every search, valid or not; `blue_root` describes it whenever `x` lies in a component of the searched forest.

@decl Geometric.GreedyASS.Potential.currentBlue

`currentBlue t lo searches x` is the blue value for the last search of `searches`, the current position of the finger. Before any search it is $0$. The list `searches` is the request history. Its entry with index $i$ is the request that produced the row at time $i$.

The comparison behind the paper's Fact 3.2 is that green is at most blue exactly when both external neighbors lie in the item's component:

@decl Geometric.GreedyASS.Potential.Results.green_comparison

### Purple: the largest blue since the last access

@decl Geometric.GreedyASS.Potential.purple

`purple t lo searches stamp x` is the maximum of the blue values of `x` over the searches at index `stamp` and later, through the current search. For an item whose most recent access is at time `stamp`, this is the highest blue value since that access, the paper's $\mathrm{Purple}_i(x)$. The maximum is a `Finset.sup`, so it is $0$ if `stamp` is past the end of the list. The update rule below assumes `stamp ≤ searches.length`.

Appending a search raises purple to the new blue value if that is larger. Purple measured from the newest search alone is the new blue value:

@decl Geometric.GreedyASS.Potential.Results.purple_update

### The example: values

In the example the current search is $4$. The forest is $\{0,1\}, \{2\}, \{3\}, \{4\}$. The external keys are $0$, $3$ and $4$. A dash marks a candidate that the item's class does not use.

| item | class | red | green | blue | purple | color | value |
|---|---|---|---|---|---|---|---|
| $0$ | left external | — | $\infty$ | $3$ | — | blue | $3$ |
| $1$ | internal | $3$ | — | — | — | red | $3$ |
| $2$ | left glancing | $3$ | — | — | $2$ | purple | $2$ |
| $3$ | top corner | — | $5$ | $2$ | — | blue | $2$ |
| $4$ | top corner | — | $\infty$ | $2$ | — | blue | $2$ |

Item $1$ is red: its neighbors $0$ and $2$ meet at the root, and the path from $1$ to the root has three nodes. Item $2$ has red value $3$ as well, through neighbors $0$ and $3$. Since its access at time $4$, it has been a one-leaf component, with blue value $2$, so its purple value is $2$, and purple wins. Item $0$ has no external item to its left, so its green value is infinite, and it is blue: two nodes up to the root of $\{0,1\}$, plus one. The item potentials add up to $12$, and with no virgin roots left, that is the whole potential.

## The coloring

@decl Geometric.GreedyASS.Potential.Color

@decl Geometric.GreedyASS.Potential.color

`color t lo searches P q` is `none` for a point that is not active. For an active point, it follows the classification:

- **External.** A top corner, on the latest row of `P`, is blue. Any other external point is green if its green value is at most its current blue value, and blue otherwise. Ties go to green.
- **Glancing.** Red if its red value is strictly less than its purple value, and purple otherwise. Ties go to purple.
- **Internal.** Always red.

These are the paper's rules, ties included.

@decl Geometric.GreedyASS.Potential.value

The value of a point is the candidate that its color selects. An inactive point has value $0$. For glancing points, and for external points other than top corners, the rule amounts to taking the smaller of the two candidates:

@decl Geometric.GreedyASS.Potential.Results.internal Geometric.GreedyASS.Potential.Results.glancing Geometric.GreedyASS.Potential.Results.external

@decl Geometric.GreedyASS.Potential.Results.corner Geometric.GreedyASS.Potential.Results.green_location

A green item is external, not a top corner, and its green value is at most its blue value. In particular, a green value that is used is finite. In fact every value is finite: nonexternal points have both neighbors, and external points can always fall back on blue.

@decl Geometric.GreedyASS.Potential.Results.finite

::: caveat Two independent arguments
`color` takes the request history `searches` and the point set `P` as separate arguments, and nothing in the definition ties them together. The potential of [Chapter 26](greedy-amortized.html) uses the actual GreedyASS points of the history. The paper's intermediate Phase I potential uses the old point set with the new search appended. Top-corner status always comes from the latest row of `P`. So in that intermediate snapshot, the corners of the old latest row are still top corners and stay blue, although the finger has moved: `corner` holds for any `searches`.
:::

Untouched internal and glancing points keep their values when a row is added. The glancing case needs the point to be still glancing afterwards:

@decl Geometric.GreedyASS.Potential.Results.internal_stable Geometric.GreedyASS.Potential.Results.glancing_stable

Glancing items that become internal, and external items, can change value. [Chapter 26](greedy-amortized.html) shows that, for untouched items, these changes are never increases (Lemmas 3.13 to 3.17).

## Amounts and totals

The potential is a sum over keys, so the last definitions move from points to keys.

@decl Geometric.GreedyASS.Potential.itemColor Geometric.GreedyASS.Potential.itemValue

`itemColor` and `itemValue` evaluate `color` and `value` at the most recent access of the column. A key that was never touched has no color and value $0$. This is also how the intermediate Phase I colors are computed, from the old point set.

@decl Geometric.GreedyASS.Potential.Results.item

@decl Geometric.GreedyASS.Potential.itemAmount Geometric.GreedyASS.Potential.totalAmount

`itemAmount` converts the value to a natural number, with `untopD 0`. By `finite` no information is lost. `totalAmount` sums the amounts over a set of keys. The potential of [Chapter 26](greedy-amortized.html), [[Amortized.potential]], is `totalAmount` over the keys below `lo + leaves t`, at the GreedyASS points of the history, plus the virgin potential `before` at the last request. In the example it is $12 + 0 = 12$.

For counting, the keys of a row are sorted by their colors:

@decl Geometric.GreedyASS.Potential.coloredKeys Geometric.GreedyASS.Potential.unseenKeys

`coloredKeys … keys c` is the set of keys in `keys` whose item has color `c`, and `unseenKeys P keys` is the set of keys never touched in `P`. Before the new row is added, the keys of the row are either unseen or have one of the four colors. After the row is added, every key of the row is active, so it has a color:

@decl Geometric.GreedyASS.Potential.Results.partition Geometric.GreedyASS.Potential.Results.row

The unseen keys need an extra allowance in the library's accounting: an unseen key has no old potential to pay for its first access. The library pays for first accesses with a separate, one-time budget: there are at most $n$ of them over the whole run.

@decl Geometric.GreedyASS.Potential.firstAccesses

`firstAccesses time P xs` runs the GreedyASS sweep from snapshot `P` at time `time` on the requests `xs`, and counts, row by row, the keys that are touched for the first time.

@decl Geometric.GreedyASS.Potential.Results.first_accesses Geometric.GreedyASS.Potential.Results.startup

`first_accesses` is exact: the number of columns touched at the start, plus the first accesses, is the number of columns touched at the end. `startup` bounds this by $n$ when the history is arborally satisfied and it and all requests use keys below $n$. This one-time charge is part of the term linear in the number of reference leaves in Theorem 3.1 ([Chapter 26](greedy-amortized.html)).
