# Treaps

[Chapter 9](equivalence.html) states that every arborally satisfied point set can be executed by a binary search tree that touches exactly one node per point. The proof, due to Demaine, Harmon, Iacono, Kane and Pătraşcu (2009), is a data structure: a treap whose priorities are the times at which keys will next be touched. The converse, that the touched nodes of any rooted-region execution form an arborally satisfied set, rests on the mirror-image invariant, a heap of the times at which keys were last touched. This chapter presents the definitions these two arguments are built from, and how the proofs use them.

Together the two arguments prove the exact form of the equivalence, with no constant factors at all: a point set and a BST execution in the rooted-region model of [Chapter 7](regions.html) cost the same.

The last two sections leave the geometric setting. They state the classical facts about treaps for arbitrary distinct priorities, and define the *random* treaps that Lazy Finger Theorem 1 uses in [Chapter 14](lazy-finger.html).

```headline treap-regions
title: Arborally satisfied sets are exactly rooted-region executions
source: Demaine, Harmon, Iacono, Kane and Pătraşcu, *The geometry of binary search trees* (2009)
theorems: Geometric.Equivalence.Results.ass_iff_region_execution

For every $n$, every request sequence $X = x_0, x_1, \dots$ and every number $c$, the following are equivalent:

- there is an arborally satisfied set of exactly $c$ points, with keys less than $n$ and times less than $|X|$, that contains the point $(x_i, i)$ of every request;
- some BST on $n$ keys can serve $X$ in the rooted-region model, touching exactly $c$ nodes in total.

The initial tree is not fixed: the construction chooses it, and it needs the whole sequence in advance. In Lean, the point sets are [[Geometric.Offline]] solutions and the executions are [[RegionExecution]]s.
```

Apart from [[Geometric.Heap]], which the general treap facts at the end of the chapter use, none of the definitions of the next five sections appears in a theorem statement of the reading interface. They live in `Structures/Treap/Abstract.lean`, `Models/Region/Abstract.lean` and `Models/Region/View/Abstract.lean`, and they are shown so that the proofs of [[Geometric.Equivalence.Results.ass_iff_region_execution]] and [[Geometric.Equivalence.Results.ass_to_pointers]] can be followed in the source. The regions and region executions they manipulate were defined in [Chapter 7](regions.html), and points, rows and arboral satisfaction in [Chapter 8](geometry.html).

## Treaps on ranks

A *treap* (Seidel and Aragon, 1989; the same objects are Vuillemin's Cartesian trees, 1980) is a binary search tree whose nodes also carry priorities, arranged in heap order: every node has priority at most that of each of its descendants. When priorities are distinct, the treap on a given key set is unique: its root is the key of minimum priority, and its two subtrees are the treaps of the keys on either side. On shapes, where keys are inorder ranks, heap order is a property of a shape and a priority function on ranks:

@decl RotationBST.Geometric.Heap

`Heap priority t lo` reads the subtree `t` as holding the ranks `lo, lo+1, …, lo + t.size - 1`, as in [Chapter 1](shapes.html#implicit-keys). Its root `lo + l.size` must have priority at most that of *every* rank `lo + x` in the interval, not just its two children, and both subtrees must be heaps on their own intervals. On a heap the two formulations agree, and quantifying over the interval makes the invariant easy to restrict to a subtree, exactly like [[RotationBST.LabelledTree.Ordered]] in [Chapter 4](keys.html#the-textbook-invariant).

::: check
- The priority type `α` only needs `≤`. The library uses it with `WithTop Nat` for next touches and with the order dual of `WithBot Nat` for last touches, below.
- There is no tie-breaking rule. With equal priorities several shapes satisfy `Heap`, and every statement that uses it holds for all of them. The construction needs this freedom: once a key is never touched again its priority is `⊤`, and many keys share it.
- Every interval has a treap. The library proves it, for priorities in a linear order, by the textbook recursion: put a key of minimum priority at the root and recurse on both sides. The statement is [[Geometric.TreapOrder.Results.exists_tree]], below.
:::

## Priorities from the future

Fix an arborally satisfied point set $P$ and a time $t$. The priority of a key is the first time, at or after $t$, at which $P$ touches it:

@decl RotationBST.Geometric.nextTouch

The value is the minimum of the times of the points in column `key` at or after `time`, in `WithTop Nat`, so a key with no such point gets `⊤`, read "never again". This priority depends on the future of the execution, and the construction is offline for that reason alone.

Here is the invariant of the construction: *before row $t$ is served, the tree is a treap for* `nextTouch P t`. Its first consequence needs no geometry at all. A key touched at time $t$ has priority exactly $t$, the smallest value any key can have at time $t$. If $x$ is touched at time $t$, every ancestor of $x$ has priority at most $t$, so it is touched at time $t$ as well. The keys of row $t$ are therefore closed under taking ancestors: they form a rooted connected region at the top of the tree. A row of the point set is a legal step of the rooted-region model of [Chapter 7](regions.html).

The proof reads this region off the tree by descending from the root while the visited key is touched on the current row. It is the definition `Region.project` in `Models/Region/Defs.lean`. Like the next three definitions of this chapter, it belongs to the proof, not to any theorem statement, so the book describes it without quoting its Lean. `project P time t lo` turns `t` into a [[Region]]. A node whose key is touched at `time` becomes a region node, and the first untouched key on each branch closes the descent: its whole subtree becomes a hole, kept intact. On any tree, `project` returns a region whose `tree` is `t` again. On a next-touch treap it selects the whole row: the internal lemma `Region.project_keys` states that the active keys of the projection are exactly the keys touched at `time` in the interval. This is where the descent's "stop at the first untouched key" is justified: below an untouched key nothing is touched on this row.

## Rearranging the touched region

After row $t$, only the priorities of touched keys change. An untouched key $x$ has `nextTouch P (t+1) x = nextTouch P t x`, because its next touch was already after $t$. Every hole of the region is therefore still a treap for the new priorities, and it is enough to rearrange the region itself. Inside the region, the target order is heap order among its own nodes, `Region.ActiveHeap`: `ActiveHeap priority s lo` asks that every region node have priority at most that of every active key below it, ignoring the holes entirely. Any region can be rearranged into this order without changing its fringe: the internal lemma `Region.heapify` (in `Models/Region/Heapify.lean`) produces a region `u` with [[Region.Same]]` s u lo` and `ActiveHeap priority u lo`. It brings an active key of minimum priority to the top and recurses on both sides, with the holes riding along in inorder. Planning the rearrangement is free in the model; only the touched nodes are charged.

Heap order among the active nodes is not yet a treap. A rearranged node may now sit directly above a hole, and its new priority must not exceed the priorities inside that hole. This is the one place where arboral satisfaction enters:

@decl RotationBST.Geometric.RowAdjacent

`RowAdjacent P time a b` says that no point of row `time` lies between `a` and `b`, except possibly at `a` itself. A hole of the region is a maximal interval of keys untouched at $t$, and it hangs from one of the two touched keys that bound it. So every key $b$ of a hole is row-adjacent to its parent $a$. The internal lemma `adjacent_nextTouch` (in `Structures/Treap/Priorities.lean`) then states:

> If $P$ is arborally satisfied, $(a, t) \in P$, $a \ne b$, and $a$ and $b$ are row-adjacent at time $t$, then `nextTouch P (t+1) a ≤ nextTouch P (t+1) b`.

The argument is short. Suppose $b$ is next touched at time $f > t$. The rectangle spanned by $(a, t)$ and $(b, f)$ contains a third point of $P$, and in an arborally satisfied set one can find such a point on one of the two sides through $(a, t)$. The bottom side is row $t$ between $a$ and $b$, which adjacency rules out. So the point is in column $a$, at a time in $(t, f]$, and $a$ is touched again no later than $b$.

With this lemma, `Region.restore` (in `Structures/Treap/Restore.lean`) shows that a region in active heap order, whose holes are treaps and whose keys are exactly the row, is a treap for time $t+1$. The invariant is restored, and the next row is again the top region of the tree.

::: note The whole construction
Take a treap for `nextTouch P 0` on the $n$ keys; this is the initial tree, and the construction chooses it. For each row $t$: project the row, which contains the request, rearrange it into heap order for time $t+1$, and continue. Each step is a [[RegionStep]] charging the size of the row, so the total charge is exactly the number of points of $P$. This is the forward direction of [[Geometric.Equivalence.Results.ass_iff_region_execution]]. Serving each region on the pointer machine instead, by two applications of the reshaping lemma [[RotationBST.Pointer.Lazy.Results.reshape]], costs at most $33$ instructions per touched node, which is [[Geometric.Equivalence.Results.ass_to_pointers]].
:::

The figure runs the construction on the GreedyASS solution ([Chapter 16](greedy.html)) of a request sequence you choose. The point set is drawn below the tree with the same horizontal axis, so each column of points sits under its key. Steps alternate between highlighting the touched region of the current row and rearranging it. The hanging subtrees never change; only the highlighted nodes move.

@viz treap {"n": 8, "requests": [3, 5, 1, 6, 3, 0, 7, 3, 4]}

::: exercise Watch the priorities
Step through the whole sequence and check that the highlighted region is always at the top of the tree, and that it contains every point of the current row. Then pick a key whose next touch is far away and follow it: it sinks below the keys that will be needed sooner. Switch the priority labels to "last touch" and check that the same trees are also ordered by the past, most recent on top. The next section explains why.
:::

The figure's JavaScript port breaks priority ties by the smaller key, which is one of the choices `Heap` allows. Its test suite checks every invariant above on the GreedyASS point sets computed by Lean: heap order before and after each row, `project` returning exactly the row, unchanged fringes, the adjacency inequality, and a total charge equal to the number of points.

## Priorities from the past

The converse direction starts from an arbitrary execution of the rooted-region model and must show that the touched nodes, row by row, form an arborally satisfied set. There is no future to consult, only the history. The proof uses two definitions from `Models/Region/View/Defs.lean`. `lastTouch P key` is the latest time at which the history `P` touches `key`, in `WithBot Nat`, and `⊥` if it never has. `HistoryHeap P t` says that `t` is a max-heap of last touches, with the most recently touched keys on top. It is stated with [[Geometric.Heap]] by reversing the order: `OrderDual.toDual` turns "minimum of the dual" into "maximum". Keys never touched have priority `⊥`, the bottom of the original order, so they sink below every touched key.

The invariant is maintained by every rooted-region step, whatever rearrangement it chooses:

- Initially the history is empty, every key has priority `⊥`, and every tree is a history heap.
- A step touches a rooted region at the new time $t$. Every key of the region now has last touch $t$, the maximum, and the region is at the top of the tree. Its holes are untouched and keep their order. So any rearrangement of the region is again a history heap (`region_history_heap`, in `Models/Region/View/Preservation.lean`).

The invariant gives arboral satisfaction one row at a time. Let $a = (x, s)$ be an old point and $b = (y, t)$ a point of the new row, with $x \ne y$, so $s < t$. The rooted region touched at time $t$ contains $y$, so it also contains every ancestor of $y$. The internal lemma `between_ancestor` finds a key $c$ of the region between $x$ and $y$ whose last touch is at least that of $x$; on the tree, $c$ is the lowest common ancestor of $x$ and $y$, which lies between them in inorder and above $x$ in the heap. If $c \ne y$, the point $(c, t)$ is a third point of the rectangle. If $c = y$, then $y$ was last touched at some time in $[s, t)$, and that point lies on the rectangle's side. Pairs inside the new row are degenerate, and pairs of old points were handled before. This is `region_ass`, and iterating it along a [[RegionExecution]] gives the backward direction of [[Geometric.Equivalence.Results.ass_iff_region_execution]], with exactly one point per touched node.

::: check
The two invariants describe the same trees in the treap construction. Before row $t$, the tree is a min-heap of next touches and, by the argument above, a max-heap of last touches. The figure's "last touch" labels show the second order on the trees built for the first. Keys touched recently and keys needed soon are near the root, and the construction of the previous section is one particular way of keeping both.
:::

## Where these definitions sit

The treap construction is the only offline argument of the geometric chapters. Its priorities come from the future of the point set, so it converts a whole solution, never a request at a time. The online direction, in [Chapter 17](simulation.html), cannot know next touches and replaces the treap by last-touch supernodes stored in the split trees of [Chapter 21](split-trees.html).

## Treaps for arbitrary priorities

Everything so far used treaps for one kind of priority, the next touches. Three classical facts hold for priorities in any linear order. They are stated in `Structures/Treap/Order/Abstract.lean` and are used by the random treaps of the next section. All three read a tree on the ranks `lo, lo+1, …, lo + n - 1`, as [[Geometric.Heap]] does.

**Theorem (existence).** For every priority function into a linear order, every interval of $n$ ranks has a treap of size $n$. Ties are allowed.

@decl RotationBST.Geometric.TreapOrder.Results.exists_tree

The proof is the recursion of the first section: a key of minimum priority is the root, and both sides are built recursively. The priorities can be anything, not only next-touch times.

**Theorem (uniqueness).** If the priorities are distinct on the interval, two treaps of the same size on it are the same tree.

@decl RotationBST.Geometric.TreapOrder.Results.unique_shape

Distinctness is needed only on the interval, `Set.InjOn priority (Set.Ico lo (lo + t.size))`. Keys outside it may share priorities.

**Theorem (ancestors are interval minima).** Let the priorities be distinct on the interval, and let $a$ and $x$ be two of its ranks. Then $a$ lies on the search path to $x$ exactly when $a$ has the smallest priority among all ranks between $a$ and $x$, inclusive.

@decl RotationBST.Geometric.TreapOrder.Results.ancestor_minimum

The search path ([[Tree.searchPath]]) runs from the root to $x$ and includes both. So "on the search path to $x$" means "an ancestor of $x$, or $x$ itself", and for $a = x$ both sides hold trivially. The proof follows the root, which has the minimum priority of the whole interval. If the root is $a$, both sides hold. If the root is $x \ne a$, or lies strictly between $a$ and $x$, both sides fail: $a$ is not on the path, and the root is a rank of the interval with a smaller priority than $a$. Otherwise $a$ and $x$ lie in the same subtree, and the induction continues there. This is a deterministic identity, with no probability in it. It turns every ancestor event of a treap into an event about which key of an interval has the smallest priority.

## Random treaps

Lazy Finger Theorem 1 (Bose, Douïeb, Iacono and Langerman, 2013) gives, for any positive weights, a randomized static tree in which, for every pair of keys $x, y$, the expected cost of moving the lazy finger from $x$ to $y$ is within a constant factor of the weighted dynamic-finger charge of the pair. The library states it as [[LazyFinger.Random.Results.weighted_charge]] in [Chapter 14](lazy-finger.html). The random tree is a treap with random priorities, and this section defines the probability space. It lives in `Structures/Treap/Random/Definitions/Abstract.lean` and contains no measure theory: it is a finite weighted average over orders of the keys.

A random order replaces random priorities. The key listed first gets the smallest priority and becomes the root of the treap, and so on down the list.

@decl RotationBST.Treap.Random.IsOrder

`IsOrder s xs` says that `xs` lists every key of the finite set `s` exactly once.

@decl RotationBST.Treap.Random.average

`average w s f` is the expected value of `f xs` when the order `xs` of `s` is drawn as follows. The first key is chosen from `s` with probability proportional to its weight, $w(x)/\sum_{k \in s} w(k)$. The rest of the order is drawn in the same way from the remaining keys. Written out, the order $x_1, \dots, x_m$ has probability

$$
\prod_{i=1}^{m} \frac{w(x_i)}{w(x_i) + w(x_{i+1}) + \dots + w(x_m)} ,
$$

which is sampling without replacement proportional to weight (the Plackett–Luce distribution). With equal weights every order has probability $1/m!$. Equivalently, though the library never uses this, one may give the keys independent exponential priorities with rates $w(x)$ and sort them increasingly.

To read a random treap off an order, use the position in the list as the priority, `xs.idxOf`. On a genuine order these positions are distinct (`order_idxOf_injective`), so by [[Geometric.TreapOrder.Results.unique_shape]] the order determines the treap. If `T xs` is a treap for `xs.idxOf`, then `average w s (fun xs => g (T xs))` is the expectation of `g` over the random treap.

::: check
- The definition is total. The empty set gives `f []`, and nothing in the definition requires positive weights. With nonpositive weights it is not an expectation. With total weight $0$, Lean's division by zero gives $0$ for every term. The probability statements all assume `0 < w x` on the set.
- Under that hypothesis the proof files establish what an expectation should satisfy. The total probability is one (`average_const`), and the average is linear (`average_add`, `average_mul`, `average_sum`). It depends only on the values of `f` on genuine orders (`average_congr`, `average_mono`).
- `exists_order_le_average` is the finite probabilistic method: some genuine order makes `f` at most its average. This turns the randomized tree into a deterministic one.
:::

@decl RotationBST.Treap.Random.firstIn RotationBST.Treap.Random.firstProbability

`firstIn s xs` is the first key of `s` in the list `xs`, that is, the key of `s` with the smallest priority, or `none` if `xs` contains no key of `s`. `firstProbability w u s a` is the probability that `a` comes first among `s` when the whole universe `u` is ordered at random. The basic lemma is `firstProbability_eq` (in `Random/Minimum.lean`):

> If the weights are positive on `u`, `s ⊆ u` and `a ∈ s`, then `firstProbability w u s a` $= w(a) / \sum_{k \in s} w(k)$.

The keys outside `s` do not bias which key of `s` comes first. Combined with [[Geometric.TreapOrder.Results.ancestor_minimum]], this gives the ancestor probabilities of a random treap. Let $W[i, j]$ be the total weight of the ranks between $i$ and $j$ inclusive:

- $a$ lies on the search path to $x$ with probability $w(a) / W[\min(a, x), \max(a, x)]$ (`exists_random_treap`, in `Random/Tree.lean`);
- $a$ lies on the search paths to both $x$ and $y$ with probability $w(a) / W[\min(a, x, y), \max(a, x, y)]$ (`common_ancestor_probability`).

The lazy-finger distance between $x$ and $y$ counts the ancestors of $x$ and of $y$ that are not common ancestors. Summing these probabilities over $a$ gives the exact expected distance [[LazyFinger.Random.Results.expected_distance]], and bounding the sums gives [[LazyFinger.Random.Results.weighted_charge]]. Both are in [Chapter 14](lazy-finger.html).

::: caveat What the statements say about the trees
The two theorems of [Chapter 14](lazy-finger.html) assert that *some* family of trees `T : List Nat → Tree`, each of size $n$, has the stated average. They do not say that `T xs` is a treap. The treap is the witness built in the proof, by `exists_random_treap`. Their statements depend on this chapter only through `average`, the distribution over orders.
:::
