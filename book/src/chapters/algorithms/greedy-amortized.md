# Paying for each row

This section completes the proof of Theorem 3.1 of Iacono and Langerman (2016). The theorem says that GreedyASS ([Chapter 21](greedy.html)) serves every request sequence about as fast as a fixed *leaf-oriented* reference tree whose search starts where the previous search ended. [Chapter 24](reference-forest.html) built the reference forest, and [Chapter 25](greedy-potential.html) built the potential: item potentials of four colors, plus a virgin potential on the roots of the forest. What remains is the accounting. For each row that GreedyASS adds, the number of points plus the change in potential is at most $24$ times the reference distance between the two searches, plus $24$, plus a one-time charge for keys never accessed before. Adding these bounds over the rows gives the theorem.

The theorem is the base of [Chapter 23](greedy-finger.html). Its consequences there, the ordinary lazy-finger bound, the weighted dynamic finger bound and the dynamic finger bound (Theorems 4.1 and 4.2 and Corollary 1), all follow from it.

```headline greedy-leaf-finger
title: GreedyASS is within a constant factor of every leaf-oriented lazy finger
source: Iacono and Langerman, *Weighted dynamic finger in binary search trees* (2016)
theorems: Geometric.GreedyASS.Potential.Amortized.Results.cost Geometric.GreedyASS.Potential.Amortized.Results.bst Geometric.GreedyASS.Potential.Amortized.Results.pointer
skip: Geometric.instDecidableVisible | A decidability instance, together with the one for rectangles it uses, only lets Lean compute the filter in `greedySweep`. Any two instances for the same proposition agree, so they cannot change which keys the sweep keeps.

Let $T$ be a leaf-oriented binary tree with $L$ leaves, labelled $\ell, \ell+1, \dots, \ell+L-1$ from left to right; its internal nodes carry no keys. For leaves $x, y$ let $e_T(x, y)$ be the number of edges on the path from $x$ to $y$ in $T$. The *reference cost* of a sequence $X = x_1, \dots, x_m$ of leaves is

$$R_T(X) \;=\; m + \sum_{i=2}^{m} e_T(x_{i-1}, x_i),$$

one unit per request plus the edges a finger walks between consecutive requests. Equivalently, it is $\sum_{i=2}^m d_T(x_{i-1},x_i)$ plus $1$ for the first request, where $d_T$ counts the *nodes* on the path, as in the paper. The finger starts at the first request for free, and no initial walk from the root is charged.

**Geometric form (Theorem 3.1).** GreedyASS, run from the empty history on $X$, adds at most

$$24\,R_T(X) + 15\,L$$

points in total.

**BST form.** For every $n$ there is one online BST algorithm, fixed before the initial tree, the reference tree and the requests are known, such that for every initial BST on $n$ keys, every leaf-oriented reference $T$ with leaves $0, \dots, n-1$, and every sequence $X$ of keys less than $n$, its total cost (rotations plus one per request) is at most

$$144456\,R_T(X) + 96303\,n.$$

**Pointer form.** For every $n$ there is one online BST algorithm whose run on the pointer machine of [Chapter 6](pointer.html) is, under the same quantifiers, a legal pointer execution serving $X$ with at most $4622232\,R_T(X) + 3081471\,n$ instructions.

In Lean, $R_T$ is [[Amortized.referenceCost]] and $e_T$ is [[Reference.Transitions.edges]]. The reference tree is an ordinary [[RotationBST.Tree]], read as leaf-oriented by [[Reference.leaves]]. The point count is [[Geometric.rowCost]] of [[Geometric.greedySweep]], and the BST costs are [[RotationBST.Algorithm.totalCost]] and the cost of [[Pointer.Lazy.Online.run]].
```

The paper states the bound as $O\bigl(\min_T \sum_i d_T(s_{i-1}, s_i) + n\bigr)$. The Lean statements hold for every reference tree $T$ at once, with explicit constants. In the BST and pointer forms the algorithm is chosen before $T$, so the minimum over $T$ follows. None of the constants is meant to be sharp. The $15L$ startup term is twelve units for each initial virgin root and three for the first access to each key; the paper leaves both of these implicit, and the Lean proof pays them explicitly ([Section 26.8](#what-the-formalization-adds)).

A reader who only wants the result can stop here. The rest of the section is the proof, in the order of the paper's Sections 3.4 to 3.6. [Section 26.1](#the-plan-of-the-proof) gives the plan of the proof and a map from the paper's lemmas to the Lean theorems. [Section 26.2](#the-benchmark-and-the-potential) defines the benchmark and the potential. Then come Phase I ([Section 26.3](#phase-i-moving-the-reference-forest)), the two halves of Phase II ([Section 26.4](#phase-ii-the-accessed-items) and [Section 26.5](#phase-ii-the-unaccessed-items)), the color counting they rely on ([Section 26.6](#at-most-six-blue-or-purple-items-per-root)), the assembly of Phase II ([Section 26.7](#phase-ii-assembled)), and the final summation ([Section 26.7](#one-row-a-whole-stream-and-the-theorem)). The statements live in `Algorithms/GreedyASS/Potential/{PhaseOne,Accessed,Unaccessed,Counting,PhaseTwo,Amortized}/Abstract.lean` and their `Definitions/Abstract.lean` files.

## The plan of the proof

Fix the reference tree $T$ and write $s_1, \dots, s_m$ for the requests. At time $i$, the *reference forest* $F_i$ is $T$ with the proper ancestors of the leaf $s_i$ removed ([[Reference.forest]], [Chapter 24](reference-forest.html)). Its roots are the siblings of the nodes on the path from the root of $T$ down to $s_i$, together with the leaf $s_i$ itself.

The potential $\Phi_i$ after row $i$ has two parts ([Chapter 25](greedy-potential.html)):

- **Item potential.** Each key that has been accessed carries a natural number determined by its color. Red and green measure distances in $T$ to the lowest common ancestor of the key's neighbors, in its row or among the external keys. Blue is one plus the node distance from the key to its root in the current forest. Purple is the largest blue value since the key's last access. Never-accessed keys carry $0$.
- **Virgin potential.** Each root of the current forest carries $12$ if no key in its interval has been accessed since it became a root, and $0$ otherwise.

The amortized cost of row $i$ is the number of points it adds, $|\mathrm{Row}_i|$, plus $\Phi_i - \Phi_{i-1}$. The proof bounds it in two phases, separated by an *intermediate potential* $\Phi'_i$. This is the potential computed with the new forest $F_i$ but the old point set $P_{i-1}$.

1. **Phase I** ($\Phi_{i-1} \to \Phi'_i$): the forest changes from $F_{i-1}$ to $F_i$ while the points stay fixed. The change is a sequence of merges up from $s_{i-1}$ to the lowest common ancestor of $s_{i-1}$ and $s_i$, followed by splits down to $s_i$: one event per edge of the path. Each event raises the potential by at most $24$. So $\Phi'_i \le \Phi_{i-1} + 24\,e_T(s_{i-1}, s_i)$.
2. **Phase II** ($\Phi'_i \to \Phi_i$): the row is added while the forest stays $F_i$. Every accessed key that ends red pays for its own point, because its potential drops by at least one. Keys accessed for the first time cost at most $3$ each. The remaining accessed keys end blue or purple, and there are at most $6$ of them in each root touched by the row. Every touched root except at most two loses its $12$ units of virgin potential. Untouched keys never gain. So $|\mathrm{Row}_i| + \Phi_i \le \Phi'_i + 24 + 3u_i$, where $u_i$ is the number of keys accessed for the first time.
3. **Summation.** The two phases give $|\mathrm{Row}_i| + \Phi_i \le \Phi_{i-1} + 24\,(e_T(s_{i-1},s_i) + 1) + 3u_i$ for each row after the first. The first row has no Phase I; it starts from the virgin potential of $F_1$, at most $12L$. The sum telescopes. The $u_i$ count distinct keys, so they add up to at most $L$. Since $\Phi_m \ge 0$, the total number of points is at most $24\,R_T(X) + 15L$.

The table maps the steps to the paper and to the Lean theorems.

| Step | Paper | Lean |
|---|---|---|
| Blue and purple counts per root | Lemma 3.1 | [[Counting.Results.counts]] |
| A split or merge costs at most $24$ | Lemma 3.2 | [[PhaseOne.Results.local_change]], [[PhaseOne.Results.charges]] |
| Phase I | Lemma 3.3 | [[PhaseOne.Results.step]] |
| Virgin roots lost in Phase II | Lemmas 3.7, 3.8 | [[Virgin.Results.count]], [[Virgin.Results.decrease]] |
| Accessed items, by color after Phase I | Lemmas 3.9–3.12 | [[Accessed.Results.green_exact_change]], [[Accessed.Results.purple_change]], [[Accessed.Results.blue_change]], [[Accessed.Results.red_change]] |
| Unaccessed items | Lemmas 3.13–3.17 | [[Unaccessed.Results.external_point]], [[Unaccessed.Results.red_unchanged]], [[Unaccessed.Results.internal_cover]], [[Unaccessed.Results.nonexternal_change]] |
| Phase II | Lemma 3.18 | [[PhaseTwo.Results.step]] |
| One row | Lemma 3.19 | [[Amortized.Results.step]] |
| The whole sequence | Theorem 3.1 | [[Amortized.Results.stream]], [[Amortized.Results.cost]] |

## The benchmark and the potential

The benchmark charges a lazy finger on the leaves of $T$. Between two consecutive requests, the finger walks the path between their leaves.

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.edgeCost RotationBST.Geometric.GreedyASS.Potential.Amortized.referenceCost

`edgeCost t lo xs` sums [[Reference.Transitions.edges]]` t lo x y` over consecutive pairs `x, y` of `xs`. That function descends from the root of `t` while both leaves are on the same side, and at their lowest common ancestor returns the sum of the two leaf depths in that subtree, counted in edges. So it is the number of edges on the leaf-to-leaf path, and $0$ when $x = y$. The offset `lo` is the label of the leftmost leaf, so the leaves of `t` are `lo, …, lo + leaves t - 1`.

`referenceCost` adds one unit per request. Since the paper's distance $d_T$ counts nodes, $d_T = e_T + 1$, and

$$\texttt{referenceCost}\;t\;\ell\;X \;=\; m + \sum_{i=2}^m e_T(x_{i-1},x_i) \;=\; 1 + \sum_{i=2}^m d_T(x_{i-1},x_i) \qquad (m \ge 1).$$

A repeated request costs one unit, the cheapest possible charge for a search. The first request also costs one unit: the finger is assumed to start on it, rather than at the root. An initial walk from the root would add at most the height of $T$, which is less than $L$, so the convention changes nothing up to the startup term.

The potential after a history `xs` is the potential of [Chapter 25](greedy-potential.html), evaluated on the actual GreedyASS points:

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.potential

The first term is the item potential [[Potential.totalAmount]], summed over the keys `0, …, lo + leaves t - 1`. The point set is [[Virgin.points]]` xs`, the set GreedyASS produces from the empty history, and the search list is `xs` itself, so blue values are measured in the forest of the last request. Keys below `lo` are never accessed and contribute $0$, so the range is just a convenient finite domain containing every column. The second term is [[Virgin.before]] at the last request `last`, with the completed history `xs` (which already contains `last`). It is $12$ times the number of roots of the last search's forest that have not been accessed since they became roots. The empty history has potential $0$.

All quantities are natural numbers, so the potential is never negative. This is what lets the summation drop the final potential at the end.

## Phase I: moving the reference forest

Phase I keeps the point set `P` of the completed history `prior ++ [old]` fixed and replaces the forest of `old` by the forest of `next`. The resulting intermediate item potential is [[Potential.totalAmount]] with the search list `prior ++ [old] ++ [next]` and the old points. Appending `next` without a new row changes exactly two things: blue is now measured in the forest of `next`, and every purple maximum now includes that new blue value.

### Values on any cut

The forest of `old` is turned into the forest of `next` one split or merge at a time, and the forests in between are not search forests. To follow the potential through them, the library evaluates every item on an arbitrary ordered cut of $T$ into subtrees ([[Reference.Transitions.Cut]]).

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.rootBlue

`rootBlue roots x` finds the component of the cut containing `x` and returns one plus the node distance from `x` to that component's root ([[Reference.Distance.toRoot]]). This is the paper's $\mathrm{Blue}(x) = d(x, r(x)) + 1$ for that cut. On a search forest it is the existing blue value:

**Theorem (cut blue agrees with blue).** For every leaf $x$ of $T$ and every search $s$, `rootBlue` on the forest of $s$ equals [[Potential.blue]]` t lo s x`.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.forest_blue

Given a blue candidate `b`, the value of a point is selected as follows. The color rule of [Chapter 25](greedy-potential.html) is rewritten with minima and maxima, which makes the dependence on `b` explicit:

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.select

An inactive point has value $0$. A top corner, an external point in the latest row, has value `b`. Another external point has $\min(\mathrm{green}, b)$: green when green is at most blue, as the color rule says, and blue otherwise. A glancing point has $\min(\mathrm{red}, \max(\mathrm{purple}, b))$, where `purple` is the historical maximum over the old search list and `b` adds the current forest's contribution. An internal point has its red value. The location classes, red and green depend only on `P`, so they are fixed throughout Phase I. Only `b` moves, and `select` is monotone in `b`.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.valueAt RotationBST.Geometric.GreedyASS.Potential.PhaseOne.itemAt RotationBST.Geometric.GreedyASS.Potential.PhaseOne.amountAt RotationBST.Geometric.GreedyASS.Potential.PhaseOne.totalAt

`valueAt` applies `select` with the candidate `rootBlue roots q.1`. `itemAt` applies it to a key's most recent access, or gives $0$ for a key never accessed. `amountAt` converts the result to a natural number, and `totalAt` sums over a finite domain. As with [[Potential.itemAmount]], the conversion `untopD 0` would turn $\infty$ into $0$. It loses nothing, because the selected value is always finite:

**Theorem (cut values are finite).** For every cut and every key, `itemAt` is the finite number `amountAt`.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.amount

The two ends of Phase I are the two potentials it connects.

**Theorem (initial cut).** If `P` is a history before time $|prior| + 1$ with all keys in the leaf range, then on the forest of `old`, with the search list `prior ++ [old]`, `totalAt` equals the item potential [[Potential.totalAmount]] for `prior ++ [old]`.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.initial

**Theorem (final cut).** If `P` is a history before time $|searches|$ with all keys in the leaf range, then on the forest of `searched`, with the search list `searches`, `totalAt` equals the item potential for `searches ++ [searched]`, the intermediate potential.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.final

In the initial theorem, the purple maximum over `prior ++ [old]` already includes the blue value at `old`, so taking the maximum with `b` changes nothing. In the final theorem, the maximum with `b` is exactly what appending `searched` to the search list adds. Throughout Phase I the search list in `totalAt` stays `prior ++ [old]`; only the cut moves.

### Which items can gain

A split replaces a root by its two children. Every key below it gets one node closer to its root, so `b` decreases and, by monotonicity, no value increases. A merge is the reverse. Every key of the two merged components gets one node farther from its root, so `b` grows by exactly one, and each value grows by at most one. Only some keys can actually gain:

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Sensitive RotationBST.Geometric.GreedyASS.Potential.PhaseOne.instDecidableSensitive

A point is *sensitive* to the candidate `b` if raising `b` can raise its selected value. This holds for an external point that is a top corner or whose green value exceeds `b`, and for a glancing point whose red value exceeds `b`. Internal points never depend on `b`, and the other external and glancing points are capped by green or red. The instance only makes the predicate decidable, so that it can be used in a filter.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.chargedKeys

`chargedKeys t lo P c` collects the columns of the active points inside the component `c` that are sensitive to the blue candidate of `c`, one plus their distance to its root. Historical purple maxima can only cap values further, so every key whose value can grow when `c` is merged into its parent lies in this set. The set is small:

**Theorem (six charged keys per subtree).** For every subtree occurrence $c$ of $T$ and every arborally satisfied `P`, at most $6$ columns are charged.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.charges

The count is the argument of Lemma 3.1, run with the candidate of `c` instead of the current colors: at most two sensitive glancing points, two sensitive left-external points and two sensitive right-external points. Among three glancing points of one subtree, the middle one has its row neighbors between the outer two. By the nesting of lowest common ancestors (the paper's Fact 3.1), its red value is then below the subtree's blue candidate, so it is not sensitive. External points work the same way, with green in place of red. [Section 26.6](#at-most-six-blue-or-purple-items-per-root) gives the same argument for the actual colors.

### Splits, merges and the plan

**Theorem (one event).** Let `P` be arborally satisfied with keys in the leaf range. A split or merge of an ordered cut of $T$, whose parent component is a subtree of $T$, increases `totalAt` by nothing if it is a split, and by at most $12$ if it is a merge.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.local_change

A merge joins two components, each with at most $6$ charged keys gaining at most one unit each. The hypotheses come from [Chapter 24](reference-forest.html). `cut` says the current components are an ordered partition of the leaves into actual subtrees of $T$. `step` is the local rewrite, and `admissible` says the parent of the event occurs in $T$. Two adjacent intervals are not enough for a merge: they must be siblings in $T$.

**Theorem (any trace).** Along a certified trace of splits and merges from a cut, `totalAt` increases by at most $12$ per merge.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.trace_change

**Theorem (the plan).** If `P` is arborally satisfied, is a history before time $|prior| + 1$, and has keys in the leaf range, then the intermediate item potential exceeds the item potential of `prior ++ [old]` by at most $12$ times the number of merges in [[Reference.Transitions.plan]]` t lo old next`.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.items_change

The plan is the LCA-routed sequence of [Chapter 24](reference-forest.html): merges from the leaf `old` up to the lowest common ancestor, then splits down to `next`. Its events correspond to the edges of the path, so there are exactly $e_T(old, next)$ of them. The virgin side of the budget is [[Virgin.Results.phase_one_budget]] from [Chapter 25](greedy-potential.html). A split creates two new roots, which may be virgins worth $12$ each, and a merge creates one. So the virgin potential grows by at most $24$ per split and $12$ per merge, and the remaining $12$ per merge pays for the items. Together:

**Theorem (Phase I, Lemma 3.3).** Let `prior ++ [old] ++ [next]` be requests in the leaf range, and let `P` be the GreedyASS points of `prior ++ [old]`. On any domain, the intermediate item potential plus the virgin potential of the forest of `next` is at most the item potential after `old` plus the virgin potential left after `old`'s row, plus $24\,e_T(old, next)$.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results.step

The left side is $\Phi'_i$ and the right side is $\Phi_{i-1} + 24\,e_T(s_{i-1}, s_i)$. Here `Virgin.after t lo prior old` is the virgin potential once `old`'s row has been added, and [[Virgin.before]]` t lo (prior ++ [old]) next` is the virgin potential of the forest of `next` before the next row. The paper bounds Phase I by $24\,d_T$, counting nodes. The Lean bound, $24\,e_T$, counts the events, which is one per edge.

## Phase II: the accessed items

Phase II keeps the forest of the current search `searched` and adds GreedyASS's row, `keys = greedySweep |searches| searched P`, to the old points `P`. Colors before the row are the intermediate ones: search list `searches ++ [searched]`, points `P`. Colors after it use the same search list and `P ∪ row |searches| keys`. Most statements below assume that `P` is a history before time $|searches|$ (so the new row is the latest), and some also that it is arborally satisfied with keys in the leaf range.

After the row, an accessed key is never green. Its point is in the latest row. If it is external, it is a top corner, which is blue by the color rule. Otherwise no point lies above it, so it is glancing, and it is red or purple. Every new value is also bounded by the current blue value:

**Theorem (new accesses are capped by blue).** For any finite set `keys` placed on the new row, and any `x ∈ keys`, the new value of `x` is at most [[Potential.blue]]` t lo searched x`. It is strictly smaller if `x` ends red.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.new_access

For a top corner the value is blue itself. For a glancing point, purple is a maximum over the searches since its last access, which is now only `searched`, so it is blue, and red is selected only when it is strictly smaller.

The remaining lemmas split the accessed keys by their color after Phase I, as the paper does. Each says that the potential does not increase, and decreases by at least one if the key ends red.

**Theorem (Lemma 3.10, old purple).** If an accessed key was purple, its new value is at most its old one, and strictly smaller if it ends red.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.purple_change

The old purple value is a maximum that includes the current blue value, and the new value is at most that blue value.

**Theorem (Lemma 3.11, old blue).** If an accessed key was blue, its new value is at most its old one, and strictly smaller if it ends red.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.blue_change

The old blue value is the current blue value, since Phase I already moved to the current forest.

**Theorem (the search separates the neighbors).** Let `P` be a history before time `time`, and let an active point `q` of `P` have row neighbors $a < q.1 < b$. If GreedyASS accesses `q.1` at `time` for the request `searched`, then $a < \texttt{searched} < b$.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.search_interval

Otherwise the neighbor's point, which is in `q`'s row, would lie in the rectangle between `q` and the request, and `q` would not be visible. This is the first observation in the paper's proof of Lemma 3.12.

**Theorem (Lemma 3.12, old red).** Let `P` be a history with keys in the leaf range. If a key accessed by GreedyASS was red, its new value is at most its old one, and strictly smaller if it ends red.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.red_change

By the previous theorem, the lowest common ancestor of the old row neighbors lies above the subtree containing both `x` and the search, so the old red value is at least the current blue value. The new value is at most blue, and strictly smaller when red.

**Theorem (Lemma 3.9, old green).** Let `P` be arborally satisfied, a history, with keys in the leaf range. If a key accessed by GreedyASS was green, it becomes red and its value decreases by exactly one.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.green_exact_change RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.green_change

A green key $x$ shares its forest root with its two external neighbors, so the search lies outside that root, on one side of all three. The sweep then accesses all three and nothing between them. The new row neighbors of $x$ are its old external neighbors, and the new red value is the old green value minus one. Since the search is outside, $x$ is not a top corner. The paper also allows the result to be purple. The Lean proof shows it is always red, and `green_change` is the inequality form used in the accounting.

A key with no earlier access, a *first access*, has old value $0$. Old points lie in old columns, so a column without points can enter the row only as the request itself. The request's leaf is a singleton root, and its blue value is $2$.

**Theorem (first accesses).** If a key accessed by GreedyASS had no earlier access, its old amount is $0$ and its new amount at most $2$. Summed over all first-accessed keys of the row, the new amounts plus one unit of actual cost per key are at most $3$ per key.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.first_access RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.first_access_total

The values live in `WithTop Nat`, because red and green are $\infty$ when a neighbor is missing. The selected value is always finite, so the natural-valued amount is exact:

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.amount

The per-color lemmas combine into a unit credit. The bracket `if … then 1 else 0` is one if the key ends red:

**Theorem (unit credit).** Under the hypotheses of the red lemma, for a key accessed by GreedyASS that was red, blue or purple, the new amount, plus one if it ends red, is at most the old amount. Summed over any such set of keys, the new total plus the number of keys ending red is at most the old total.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.charge RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.total

Adding the green and first-access cases accounts for every point of the row:

**Theorem (the whole row).** Let `P` be arborally satisfied, a history before time $|searches|$, with keys in the leaf range, and let `keys` be the GreedyASS row. Then the number of points of the row plus the new item potential of `keys` is at most the intermediate item potential of `keys`, plus the number of keys ending blue, plus the number ending purple, plus $3$ per first access.

@decl RotationBST.Geometric.GreedyASS.Potential.Accessed.Results.whole_row

In the paper, accessed keys that were blue or purple after Phase I are charged to Lemma 3.1 in Lemma 3.19, even when they end red. The Lean statement pays for those that end red by the strict decrease in the lemmas for old blue and old purple keys, so it charges only the colors after the row.

## Phase II: the unaccessed items

Keys not on the new row must not gain potential. Their colors can still change, because the new row changes which points are external or glancing, and which external keys are neighbors.

External keys come first.

**Theorem (the row is on one side).** Let `P` be arborally satisfied, a history before `time`. If an external point `q` of `P` is not accessed, every key of the new row lies on the same side of `q.1`.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.sweep_side

**Theorem (external neighbors move inward).** If `x` has external neighbors $a < x < b$ in `P`, and a new row lies on one side of `x`, then `x` still has external neighbors $u, v$ after the row, with $a \le u < x < v \le b$.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.neighbor_interval

**Theorem (green does not increase).** Under a new row on one side of `x`, the green value of `x` does not increase.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.green_change

Closer neighbors have a lower common ancestor, so the distance from `x` to it does not grow (the paper's Fact 3.1).

**Theorem (Lemma 3.13).** Let `P` be arborally satisfied, a history before `time`. The value of an unaccessed external point does not increase when the GreedyASS row is added. This includes former top corners, which change from blue to the minimum of green and blue. The same holds for the natural-valued amount of its key, and for the sum over any set of unaccessed external keys.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.external_point RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.external_change RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.external_sum

These three statements use one search list on both sides, so the forest, and therefore blue, is fixed. Only the geometry changes.

The other unaccessed keys are glancing or internal, and their row neighbors do not change. A red key stays red:

**Theorem (Lemmas 3.14 and 3.17, red).** If an unaccessed key is red, it is still red after any new row, with the same amount. This includes a glancing key that becomes internal.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.red_unchanged

A purple glancing key can become internal, and internal keys are always red. The paper's Lemma 3.16 shows that this cannot raise its value: the red value is at most the purple value. The library proves this for every internal point of a GreedyASS history:

**Theorem (Lemma 3.16, purple covers red).** Let `searches` be any request list and `P` its GreedyASS points. For every internal point `q` of `P`, its red value is at most its purple value: the largest blue value over the searches since `q`'s row.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.internal_cover

For an internal point, there have been searches on both sides since its last access, and the closest ones are at least as far out as its row neighbors. Let $r$ be the lowest common ancestor of the two closest searches, and $r'$ the child of $r$ containing the key. At the time of the later of the two searches, $r'$ was a root of the forest. The blue value at that time is the distance to $r$, which is at least the red value. The hypothesis `valid` only asks that the requests are bounded by some `n`, and `n` is arbitrary, so it holds for every list.

**Theorem (Lemma 3.17).** Let `searches ++ [searched]` be bounded requests. Every active, non-external point of the GreedyASS points of `searches` whose key is not in the next row has a value that does not increase when the row is added, with the search list `searches ++ [searched]` on both sides.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.nonexternal_change

Combining the cases, and adding the keys never accessed, which stay at $0$:

**Theorem (every unaccessed key).** For bounded requests, every key not on the next GreedyASS row has a natural-valued amount that does not increase when the row is added. The same holds for the sum over any set of such keys.

@decl RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.untouched_change RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results.untouched_sum

## At most six blue or purple items per root

The accessed keys that end blue or purple are not paid for by their own potential. They are paid for by virgin potential, and that works because there are few of them in each root of the forest. This is the paper's Lemma 3.1. The library counts per component:

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.purpleKeys RotationBST.Geometric.GreedyASS.Potential.Counting.blueKeys RotationBST.Geometric.GreedyASS.Potential.Counting.leftBlueKeys RotationBST.Geometric.GreedyASS.Potential.Counting.rightBlueKeys

`purpleKeys` and `blueKeys` are the columns of `P` inside the component `c` whose item color is purple or blue. `leftBlueKeys` and `rightBlueKeys` keep only the blue points that are left or right external. A blue item is always external, and a purple one is always glancing:

**Theorem (where blue and purple items are).** If a key is purple, its most recent point is active, glancing and purple. If it is blue, its most recent point is active, external and blue.

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.Results.locations

The counting rests on two bracketing facts and two "middle" lemmas.

**Theorem (brackets).** In an arborally satisfied `P`, if three glancing points have keys $p < q < r$, then the row neighbors of $q$ exist and lie in $[p, r]$. If $p$ and $r$ are external, then the external neighbors of any key strictly between them exist and lie in $[p, r]$.

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.Results.glancing_neighbors RotationBST.Geometric.GreedyASS.Potential.Counting.Results.external_neighbors

**Theorem (the middle one is red, or green).** Let $c$ be a root of the forest of `searched`, and color with the search list `searches ++ [searched]`. If `P` is arborally satisfied and a history before time $|searches| + 1$, then among three glancing points with keys in $c$, the middle one is red. Among three external points with keys in $c$, the middle one is green, provided it is not in the latest row.

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.Results.red_middle RotationBST.Geometric.GreedyASS.Potential.Counting.Results.green_middle

The bracket puts the lowest common ancestor of the middle point's neighbors at or below the lowest common ancestor of the outer two, by the nesting of lowest common ancestors (the paper's Fact 3.1). The outer two are in $c$, so that ancestor is inside $c$, and red is strictly less than blue, which is at most purple; for external points, green is at most blue. The color rule then picks red, or green. The green half needs neither satisfaction nor the history hypothesis. Its exclusion of the latest row is necessary, since top corners are blue by definition.

**Theorem (two per direction).** If `P` is arborally satisfied and a history before time $|searches| + 1$, then each root of the forest of `searched` contains at most two left-external and at most two right-external blue items.

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.Results.directional

Among three left-external blue points in one root, the middle one has a left-external point to its right. Arboral satisfaction then keeps it out of the latest row, so it is not a top corner, and by the previous theorem it is green, a contradiction. Right-external points are symmetric. Since every blue item is external, this gives at most four blue items per root.

**Theorem (Lemma 3.1).** Let `P` be arborally satisfied, a history before time $|searches| + 1$. Every root of the forest of `searched` contains at most $4$ blue and $2$ purple items, colored with the search list `searches ++ [searched]`. The same holds for the intermediate colors, with `P` a history before time $|searches|$.

@decl RotationBST.Geometric.GreedyASS.Potential.Counting.Results.counts RotationBST.Geometric.GreedyASS.Potential.Counting.Results.intermediate

The paper's statement does not mention top corners. The Lean statement covers them, since they are blue items and are included in `blueKeys`, and it uses the actual historical purple values.

## Phase II assembled

Phase II has three parts: the accessed keys, the unaccessed keys, and the virgin roots. The statements now use the actual GreedyASS histories: [[Virgin.points]]` searches` before the row, [[Virgin.points]]` (searches ++ [searched])` after it, and the row [[Virgin.keys]]` searches searched`.

**Theorem (all items).** Let `searches ++ [searched]` be requests in the leaf range, and let the domain contain the new row. Then the number of points of the row plus the new item potential is at most the intermediate item potential, plus the number of row keys ending blue or purple, plus $3$ per first access.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results.items

**Theorem (six per touched root).** The number of row keys ending blue or purple is at most $6$ times the number of roots of the forest of `searched` whose interval contains a key of the row ([[Virgin.touched]]).

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results.colors

The virgin side is [[Virgin.Results.decrease]] from [Chapter 25](greedy-potential.html), the paper's Lemmas 3.7 and 3.8. At most two touched roots are not virgins, and every other touched root loses its $12$ units. So the virgin potential after the row plus $12$ per touched root is at most the virgin potential before it plus $24$. Since $6$ per touched root suffices for the colors, the bound has slack. The Lean accounting charges only the colors after the row, while the paper's Lemma 3.19 also charges the colors before it, which needs the full $12$.

**Theorem (Phase II, Lemma 3.18).** Let `searches ++ [searched]` be requests in the leaf range. On any domain containing the row, and in particular on all keys below `lo + leaves t`: the number of points of the row, plus the new item potential, plus the remaining virgin potential, is at most the intermediate item potential plus the virgin potential of the forest of `searched`, plus $24$, plus $3$ per first access.

@decl RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results.domain_bound RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results.step

On the full domain, the left side is $|\mathrm{Row}_i| + \Phi_i$ and the right side is $\Phi'_i + 24 + 3u_i$.

## One row, a whole stream, and the theorem

The two phases combine into the amortized cost of one row.

**Theorem (Lemma 3.19).** Let `prior ++ [old] ++ [next]` be requests in the leaf range, and let `row` be GreedyASS's row for `next`. Writing $\Phi(h)$ for `potential t lo h`,

$$|\mathrm{row}| + \Phi(\textit{prior}, \textit{old}, \textit{next}) \;\le\; \Phi(\textit{prior}, \textit{old}) + 24\,e_T(\textit{old}, \textit{next}) + 24 + 3\,u,$$

where $u$ is the number of keys of the row that have never been accessed.

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.Results.step

This is the paper's $24\,d_T(s_{i-1}, s_i) + 24$, with $d_T$ replaced by $e_T = d_T - 1$, and with first accesses charged explicitly. The $24 + 24\,e_T$ is exactly $24$ times the contribution of the request `next` to `referenceCost`.

The first row is different: there is no previous search and no Phase I. Its forest is new, and each of its at most $L$ roots may carry $12$ units of virgin potential, so the first row is charged at most $12L + 24 + 3u$ (internally `Amortized.startup`). Summing over the rows:

**Theorem (whole stream).** For every sequence `xs` of requests in the leaf range, the number of GreedyASS points plus the final potential is at most

$$12L + 24\,R_T(X) + 3\cdot\#\{\text{columns with at least one point}\}.$$

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.Results.stream

The statement keeps the final potential on the left and charges first accesses by the number of distinct columns, `(Virgin.points xs).image Prod.fst`. Every column with a point was accessed for the first time exactly once, so the per-row charges $3u_i$ add up to three per column. The startup $12L$ is paid once.

Since the final potential is a natural number and every column is a leaf of $T$, the stream bound gives the headline:

**Theorem (Theorem 3.1, geometric form).** For every leaf-oriented reference tree $T$ with leaves `lo, …, lo + leaves t - 1` and every sequence `xs` of such leaves, the number of points GreedyASS adds from the empty history is at most $24\,R_T(X) + 15\,L$.

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.Results.cost

`rowCost greedySweep 0 ∅ xs` is the actual sweep of [Chapter 21](greedy.html), run from time $0$ on an empty history, counting every point added, requests included. The bound holds for every $T$, so it holds for the minimizing one.

The simulation of [Chapter 22](simulation.html) turns the bound into one on binary search trees. Its normalized form, [[Geometric.Simulation.Results.normalized_simulation]], gives one online BST algorithm with total cost at most $6019$ points $+\,6018\,n$ from every initial tree on $n$ keys. With $L = n$ and offset $0$, the constants are $6019 \cdot 24 = 144456$ and $6019 \cdot 15 + 6018 = 96303$.

**Theorem (Theorem 3.1, BST form).** For every $n$ there is an online BST algorithm such that for every initial tree on $n$ keys, every reference tree with $n$ leaves, and every sequence of keys less than $n$, the total cost (rotations plus one per request) is at most $144456\,R_T(X) + 96303\,n$.

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.Results.bst

::: check
- **One algorithm for all references.** `∃ algorithm` comes before `∀ initial` and `∀ reference`. The algorithm is the simulation of GreedyASS, which never looks at a reference tree. A single algorithm therefore meets the bound for every $T$ simultaneously, which is what the paper's $\min_T$ requires.
- **Two different trees.** `initial` is an ordinary BST with $n$ nodes (`initial.size = n`), where the algorithm runs. `reference` is read as leaf-oriented, with $n$ leaves (`leaves reference = n`) and $n - 1$ internal nodes, and it only enters the bound.
- **Cost model.** [[RotationBST.Algorithm.totalCost]] is rotations plus one per request ([Chapter 5](online.html)). The $96303\,n$ term includes the simulation's startup and the $15n$ of the geometric bound.
:::

The pointer-machine version composes the geometric bound with [[Geometric.Simulation.Results.pointer_simulation]], whose constants are $192593$ per point and $192576$ per key: $192593 \cdot 24 = 4622232$ and $192593 \cdot 15 + 192576 = 3081471$.

**Theorem (Theorem 3.1, pointer form).** For every $n$ there is an online BST algorithm such that for every initial tree on $n$ keys, every reference tree with $n$ leaves, and every sequence of keys less than $n$, its pointer-machine run is a legal pointer execution serving the sequence, at a cost of at most $4622232\,R_T(X) + 3081471\,n$ instructions.

@decl RotationBST.Geometric.GreedyASS.Potential.Amortized.Results.pointer

As in [Chapter 22](simulation.html), the three occurrences of `Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs` are one term: the final pointer state and its accumulated cost. The first conjunct says that the instructions form a [[Pointer.Execution]] serving `xs` from `initial`, and the second bounds their number.

## What the formalization adds

The Lean proof follows the paper's structure closely. It differs in a few places where the paper is informal or slightly loose.

::: note Startup and first accesses
The paper's proof of Theorem 3.1 says that the initial potential is zero and that the potential is always nonnegative. Two charges are left implicit there. First, the forest of the first search has up to $L$ roots, all virgin, with $12$ units each, and nothing pays for them in Lemma 3.19 at $i = 1$. Second, Lemmas 3.9–3.12 classify accessed keys by their color after Phase I, but a key accessed for the first time has no color. The Lean proof charges $12$ per leaf for the first forest and $3$ per key for first accesses: one unit for the point, at most two for the new potential. Together these give the $15L$ term. Both are $O(n)$, which the paper's bound allows.
:::

::: note Distances
The paper's $d_T$ counts nodes. Phase I really performs one split or merge per *edge* of the path, so the Lean bound has $24\,e_T$ where the paper has $24\,d_T$. With the $+24$ of Phase II, the amortized cost of a row is $24\,d_T(s_{i-1}, s_i)$, which is $24$ times the row's contribution to `referenceCost`.
:::

::: note Slightly stronger lemmas
An accessed green item always becomes red ([[Accessed.Results.green_exact_change]]), where the paper also allows purple. Lemma 3.16 is proved for every internal point of a GreedyASS history, not only for keys that were glancing just before ([[Unaccessed.Results.internal_cover]]). The Phase II accounting charges blue and purple colors only after the row, so $6$ of the $12$ virgin units per touched root suffice there.
:::

::: details Where the proofs are
Phase I is in `Algorithms/GreedyASS/Potential/PhaseOne/` (values on cuts, the six-key count, single events, traces, and the plan). The accessed-item lemmas are in `Accessed/` (one file per color, plus the row accounting and the first accesses), and the unaccessed ones are in the proof files behind `Unaccessed/Abstract.lean`. The counting is in `Counting/{Blue,Purple,External,Geometry}.lean`. Phase II is in `PhaseTwo/`, and the summation, the startup and the composition with the simulation are in `Amortized/{Step,Startup,Stream,Simulation}.lean`. None of these proof files is part of the reading interface.
:::
