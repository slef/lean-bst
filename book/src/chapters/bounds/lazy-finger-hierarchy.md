# Where lazy finger stands

[Chapter 14](lazy-finger.html) introduced the lazy finger: a *static* BST in which each search starts where the previous one ended, instead of at the root. This chapter places that model between its two natural neighbours.

- Below it is the classical **root-finger** static tree, the setting of static optimality ([Chapter 12](bounds.html)). The tree is fixed and every search starts at the root.
- Above it is the **dynamic** BST of Part I. It also searches from the root each time, but may rotate.

Theorem 6 of Bose, Douïeb, Iacono and Langerman says that, up to constant factors, lazy finger is never worse than root finger and never better than a dynamic BST, and that both gaps can be arbitrarily large. The chapter also states the consequences listed in §1.4 of their paper: the optimal lazy-finger tree has static optimality, the static finger property and the dynamic finger property, all at once.

Throughout, $X = x_1, \dots, x_m$ is a sequence of keys in $\{0, \dots, n-1\}$ (*valid* requests), and all three costs charge one unit per request plus one per pointer move or rotation. We write

- $\mathrm{RF}_t(X) = \sum_j \bigl(1 + \mathrm{depth}_t(x_j)\bigr)$ for the root-finger cost in a tree $t$ ([[RotationBST.StaticTree.cost]]);
- $\mathrm{LF}^*_n(X)$ for the optimal lazy-finger cost over all trees on $n$ keys, with the finger initially at the root ([[LazyFinger.optimalCost]]; the minimum is attained);
- $\mathrm{OPT}$ for the least cost of a [[RotationBST.Pointer.Execution]], a legal execution of the pointer machine of [Chapter 6](pointer.html) that starts each search at the root.

```headline lazy-finger-hierarchy
title: Lazy finger sits strictly between root-finger static trees and dynamic BSTs
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
key: yes
theorems: LazyFinger.Results.optimal_root_finger LazyFinger.Dynamic.Results.optimal LazyFinger.Sequential.Results.family LazyFinger.Separation.Results.family

This is Theorem 6 of the paper. Let $X$ be a sequence of $m$ valid requests on $n$ keys.

1. **Lazy finger beats root finger up to a factor 2.** For every tree $t$ on $n$ keys, $\mathrm{LF}^*_n(X) \le 2\,\mathrm{RF}_t(X)$.
2. **A dynamic BST follows lazy finger up to a constant factor.** From every initial tree $s$ on $n$ keys there is a legal pointer-machine execution serving $X$ whose cost $k$ satisfies
$$k \;\le\; 16\,n + 464\,\mathrm{LF}^*_n(X).$$
3. **The first gap is unbounded.** For every startup allowance $a : \mathbb N \to \mathbb N$ there is a family of sequences $X_m$, of length $m$ on $n_m \ge 1$ keys, such that for every constant $C$, once $m$ is large enough,
$$C\,\mathrm{LF}^*_{n_m}(X_m) + a(n_m) \;<\; \mathrm{RF}_t(X_m) \quad\text{for every tree } t \text{ on } n_m \text{ keys}.$$
4. **The second gap is unbounded.** For every $a$ there is a family $X_m$ on $n_m \ge 1$ keys such that for every $C$, once $m$ is large enough, every initial tree $s$ on $n_m$ keys admits a legal execution serving $X_m$ at a cost $k$ with
$$C\,k + a(n_m) \;<\; \mathrm{LF}^*_{n_m}(X_m).$$

Item 2 is an existence statement about executions, so it compares lazy finger with the *offline* optimum. It does not give an online algorithm, and the execution may depend on the whole sequence. The families in items 3 and 4 are fixed before $C$ is chosen, so the ratios tend to infinity along one family: $\mathrm{LF}^* = o(\mathrm{RF})$ and $\mathrm{OPT} = o(\mathrm{LF}^*)$, even after any one-time startup allowance.
```

```headline lazy-finger-consequences
title: The optimal lazy-finger tree has static optimality, static finger and dynamic finger at once
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
theorems: LazyFinger.Consequences.Results.simultaneous

This is the list of consequences in §1.4 of the paper. For every sequence $X$ of $m$ valid requests on $n$ keys there is a tree $t$ on $n$ keys whose lazy-finger cost, from the root, is the optimum $\mathrm{LF}^*_n(X)$, and this cost is at most

- $2\bigl(m + \sum_x q_x \log_2 (m / q_x)\bigr)$, where $q_x$ counts the requests for $x$ (static optimality);
- $6 \sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$, for every finger $f$ (static finger);
- $n + 4 \sum_j \bigl(1 + \log_2(|x_j - x_{j-1}| + 1)\bigr)$ with $x_0 = p$, for every key $p < n$ (dynamic finger).

The tree may depend on the sequence; it is chosen before $f$ and $p$. The term $n$ pays once for starting the finger at the root rather than at $p$.
```

To confirm the results, the two boxes suffice. The rest of the chapter explains them in the order of the comparison chain. [Section 15.1](#the-chain-at-a-glance) gives an overview of the chain. [Section 15.2](#a-dynamic-bst-can-follow-a-lazy-finger) proves item 2, by simulating the lazy finger with a pointer machine. [Section 15.3](#sequential-scans-separate-lazy-from-root-finger) proves item 3 with sequential scans. [Section 15.4](#neighbourhoods-in-a-fixed-tree) counts nearby keys in a fixed tree, and [Section 15.5](#alternating-pairs-separate-dynamic-from-lazy-finger) uses the count to prove item 4 with alternating pairs. [Section 15.6](#consequences-for-the-optimal-tree) derives the consequences. Item 1 is proved in [Chapter 14](lazy-finger.html). The definitions are in `Bounds/LazyFinger/{Sequential,Separation,Neighborhood}/Definitions/Abstract.lean`, and the theorems in the `Abstract.lean` files of `Bounds/LazyFinger/Dynamic`, `Sequential`, `Separation`, `Neighborhood` and `Consequences`.

## The chain at a glance

All three models use the same keys and charge one unit per request. They differ in where a search starts and whether the tree may change.

| Model | Tree | A search starts at | Cost of a request | Lean |
|---|---|---|---|---|
| Root finger | fixed | the root | $1 + \mathrm{depth}_t(x)$ | [[RotationBST.StaticTree.cost\|StaticTree.cost]] |
| Lazy finger | fixed | the previous request | $1 + d_t(x_{j-1}, x_j)$ | [[LazyFinger.cost\|LazyFinger.cost]] |
| Dynamic BST | rotates | the root | moves and rotations, plus one | [[RotationBST.Pointer.Execution\|Pointer.Execution]] |

Here $d_t(x, y)$ is the number of edges on the path between $x$ and $y$ in $t$, which is [[LazyFinger.distance]]. The first search of a lazy finger starts at the root.

The chain reads

$$\mathrm{OPT} \;\lesssim\; \mathrm{LF}^* \;\le\; 2\,\min_t \mathrm{RF}_t,$$

where $\lesssim$ hides the factor $464$ and the additive $16n$ of item 2. In words:

- **Lazy finger is at least as good as root finger, up to a factor 2.** Going from $x$ to $y$ through their lowest common ancestor is never longer than going from the root to $x$ and then from the root to $y$. Charging each move to one of the two root-to-key paths gives the factor 2. This is [[LazyFinger.Results.root_finger]] for a fixed tree and [[LazyFinger.Results.optimal_root_finger]] for the optimum, both in [Chapter 14](lazy-finger.html).
- **A dynamic BST is at least as good as lazy finger, up to a constant factor.** A dynamic BST could simply keep the tree fixed and walk from one request to the next, but the pointer machine restarts every search at the root. So the simulation has to carry a finger along inside the tree. [Section 15.2](#a-dynamic-bst-can-follow-a-lazy-finger) shows how.
- **Lazy finger can be much better than root finger.** A sequential scan $0, 1, \dots, n-1$ costs $O(1)$ amortized per request with a lazy finger in *every* tree, while every root-finger tree pays about $\log_2 n$ per request.
- **A dynamic BST can be much better than lazy finger.** A sequence that alternates $x, y, x, y, \dots$ for a long time, for each pair $(x, y)$ in turn, is cheap for a BST that brings the current pair to the top. A fixed tree, however, must place most pairs far apart.

## A dynamic BST can follow a lazy finger

The goal of this section is item 2 of the headline. Let $t$ be a tree and $X$ a sequence. The lazy finger walks along the edges of $t$ from one request to the next. A pointer machine can perform the same walk, but it must return to the root before each search. The library closes this gap in three steps.

1. The lazy-finger distance is exactly the length of a shortest pointer walk ([Section 15.2.1](#walking-the-edge-distance)).
2. A lazy finger is therefore a *one-finger execution* in the multi-finger model of [Chapter 10](fingers.html), at exactly the lazy-finger cost ([Section 15.2.2](#one-persistent-finger)).
3. A multi-finger execution with a constant number of fingers can be simulated by a conventional BST at a constant factor. This is the *finger hand* of [Chapter 35](finger-hands.html). The method is due to Demaine, Iacono, Langerman and Özkan (2013). Optimizing over reference trees then gives the theorem ([Section 15.2.3](#from-one-finger-to-a-conventional-bst)).

### Walking the edge distance

The pointer machine's configurations ([[RotationBST.Pointer.Config]]) are a cursor on a node of a tree. Its instructions ([[RotationBST.Pointer.Step]]) move the cursor to a parent or child, or rotate. The navigation-only instructions are [[RotationBST.Pointer.Move]], and a sequence of them is a [[RotationBST.Pointer.Walk]]; a walk never changes the tree.

**Theorem (the distance is walkable).** For valid keys $x, y$ of a tree $t$, there are cursors at $x$ and at $y$ in $t$ joined by exactly $d_t(x, y)$ pointer instructions, and in fact by a navigation-only walk of that length.

@decl LazyFinger.Dynamic.Results.walk LazyFinger.Dynamic.Results.readonly

The first statement uses [[RotationBST.Pointer.Trace]], which allows any instruction, and the second uses a [[RotationBST.Pointer.Walk]]. Both fix the tree: `a.tree = t` and `b.tree = t`.

**Theorem (the distance is shortest).** Every navigation-only walk from a cursor at $x$ to a cursor at $y$ has at least $d(x, y)$ steps. Conversely, from a cursor at $x \ne y$ some single move reaches a key $z$ with $d(z, y) + 1 = d(x, y)$.

@decl LazyFinger.Dynamic.Results.shortest LazyFinger.Dynamic.Results.toward

So [[LazyFinger.distance]], defined by recursion on the tree, is the graph metric of the tree as the pointer machine sees it, and it can be followed greedily, one legal move at a time.

### One persistent finger

The multi-finger model of [Chapter 10](fingers.html) keeps several cursors in one shared tree ([[RotationBST.Multifinger.State]]). A request is served by any finger reaching the requested key, and the fingers stay where they are between requests ([[RotationBST.Multifinger.Execution]]). With one finger this is exactly a lazy finger.

**Theorem (lazy finger is a one-finger execution).** Let $t$ be a tree, $p$ a valid key and $X$ a valid sequence. There is a one-finger execution from the state "tree $t$, finger at $p$" that serves $X$ and costs exactly the lazy-finger cost of $X$ from $p$. Its final state has the same tree and the finger at some key $q$.

@decl LazyFinger.Dynamic.Results.persistent

The cost is [[LazyFinger.costFrom]] `t p xs`, one unit per request plus the walked distance, with no rounding. The tree never changes.

### From one finger to a conventional BST

The pointer machine restarts each search at the root. To serve the next request it must therefore reach the finger's position again, cheaply. The finger hand of [Chapter 35](finger-hands.html) does this. It maintains, inside the one physical tree, a compact representation of the paths that join the root to all fingers, the *hand*. With it, the root reaches any finger, and a finger takes a step, at amortized constant cost for a fixed number of fingers. In the library, a multi-finger execution with $f$ fingers and cost $c$ becomes a conventional execution of cost at most $(344 + 60(f + 1))\,c$. For one finger this is $464\,c$, the constant below. When all fingers start at the root, the hand starts in the original tree with zero potential, so no startup term appears.

**Theorem (same initial tree).** For every tree $t$ and valid sequence $X$ there is a legal pointer-machine execution from $t$ serving $X$ at cost at most $464\,\mathrm{LF}_t(X)$, where $\mathrm{LF}_t$ is the lazy-finger cost in $t$ from the root.

@decl LazyFinger.Dynamic.Results.same_tree

The comparison is between two executions that start in the same tree. If the dynamic BST may choose its initial tree, it starts in an optimal lazy-finger tree:

@decl LazyFinger.Dynamic.Results.optimal_tree

Here the initial tree `t` is part of the witness, and depends on the whole sequence. Usually the initial tree is prescribed instead. The pointer machine can transform any tree on $n$ keys into any other with at most $16n$ instructions ([[RotationBST.Pointer.Results.reshape]], [Chapter 6](pointer.html)), and the library charges that reshaping to the first request:

@decl LazyFinger.Dynamic.Results.reference

The statement covers the empty sequence and the empty universe, where the execution is empty.

**Theorem (dynamic BSTs follow optimal lazy finger, Theorem 6).** Let $s$ be any tree on $n$ keys and $X$ a valid sequence. There is a legal pointer-machine execution from $s$ that serves $X$ at cost $k \le 16n + 464\,\mathrm{LF}^*_n(X)$.

@decl LazyFinger.Dynamic.Results.optimal

The initial tree is quantified *before* the optimal lazy-finger tree is chosen inside the proof. The execution reshapes $s$ into that tree and then simulates the finger. It therefore knows the whole sequence: the theorem bounds the offline optimum, and is not an online algorithm. When there are at least as many requests as keys, the unit request charges pay for the reshaping, since $\mathrm{LF}^*_n(X) \ge m \ge n$:

@decl LazyFinger.Dynamic.Results.long_sequence

## Sequential scans separate lazy from root finger

The first separation uses the simplest possible sequence: scan the keys in order, and repeat.

@decl LazyFinger.scans LazyFinger.scanPrefix

`scans n rounds` is `rounds` copies of $0, 1, \dots, n-1$. `scanPrefix n length` stops the repetition at exactly `length` requests: it takes $\lfloor \mathit{length}/n \rfloor$ full scans and then the first $\mathit{length} \bmod n$ keys of another. For $n = 0$ the division gives $0$, so the prefix is empty, and the validity statement below requires $n > 0$.

@decl LazyFinger.Sequential.Results.prefix_length LazyFinger.Sequential.Results.prefix_valid

**Lazy finger scans in linear time.** In any fixed tree, an inorder traversal crosses each edge twice, and the jump from the last key back to the first crosses each edge at most once more. With the unit per request, a scan costs at most $4n$.

**Theorem (scans with a lazy finger).** For every tree $t$ on $n$ keys, `rounds` scans cost at most $4 \cdot \mathit{rounds} \cdot n$ with a lazy finger starting at the root, and also from any valid starting key. A scan prefix of length $m \ge n$ costs at most $8\lfloor m/n\rfloor n \le 8m$.

@decl LazyFinger.Sequential.Results.lazy_scan LazyFinger.Sequential.Results.lazy_scan_from LazyFinger.Sequential.Results.lazy_prefix

The bounds hold for *every* tree shape, so they bound the optimum $\mathrm{LF}^*_n$ too.

**Root finger pays the entropy.** Each key is requested equally often in `scans`, so the entropy bound of [Chapter 12](bounds.html) is $m(1 + \log_2 n)$, and every fixed tree pays at least a third of it ([[StaticTree.Results.entropy_lower_bound]]).

**Theorem (scans with a root finger).** For every tree $t$ on $n$ keys, $\mathit{rounds} \cdot n\,(1 + \log_2 n) \le 3\,\mathrm{RF}_t(\text{scans})$.

@decl LazyFinger.Sequential.Results.root_scan

**The gap.** The ratio between the two bounds is about $(1 + \log_2 n)/12$, which is larger than any constant $C$ once $n = 2^{12C}$.

**Theorem (a strict gap for every factor).** Let $C \ge 0$, $\mathit{rounds} \ge 1$ and $n = 2^{12C}$. For any two trees on $n$ keys, a lazy finger in the first and a root finger in the second, $C$ times the lazy-finger cost of `rounds` scans is less than the root-finger cost.

@decl LazyFinger.Sequential.Results.strict_gap

The two trees are independent, so neither model gets to see the other's choice. The next statements turn this into statements about the optimum $\mathrm{LF}^*$, with increasingly strong quantifiers.

**Theorem (unbounded ratio).** For every $C$ there is a universe $n \ge 1$ and a valid sequence of length $n$ (one scan) such that $C\,\mathrm{LF}^*_n(X) < \mathrm{RF}_t(X)$ for every tree $t$ on $n$ keys. Moreover, for every startup allowance $a$, there is such a sequence of length at least $n$ with $C\,\mathrm{LF}^*_n(X) + a(n) < \mathrm{RF}_t(X)$.

@decl LazyFinger.Sequential.Results.unbounded_ratio LazyFinger.Sequential.Results.gap_beyond_startup

A single sequence for each $C$ could be an artefact of a short length. The next two theorems fix a universe for each $C$ and then let the length be any large enough $m$: the witness is `scanPrefix n m` with $n = 2^{24C}$, and the threshold is about $3\,a(n)\,n$.

**Theorem (every long length).** For every $C$ and every allowance $a$ there are $n \ge 1$ and a threshold $T \ge n$ such that every length $m \ge T$ has a valid sequence $X$ of length $m$ with $C\,\mathrm{LF}_u(X) + a(n) < \mathrm{RF}_t(X)$ for all trees $u, t$ on $n$ keys, and hence with $C\,\mathrm{LF}^*_n(X) + a(n) < \mathrm{RF}_t(X)$.

@decl LazyFinger.Sequential.Results.all_lengths_shapes LazyFinger.Sequential.Results.all_lengths

**Theorem (one family, Theorem 6).** For every allowance $a$ there is a single family of sequences $X_m$, one of each length $m$, on universes $n_m \ge 1$, such that for every $C$, eventually, $C\,\mathrm{LF}^*_{n_m}(X_m) + a(n_m) < \mathrm{RF}_t(X_m)$ for every tree $t$ on $n_m$ keys.

@decl LazyFinger.Sequential.Results.family

::: note Why the universe must grow
On a fixed universe the ratio is bounded: every root-finger tree has depth less than $n$, so $\mathrm{RF}_t(X) \le n\,m \le n\,\mathrm{LF}^*_n(X)$. A family with an unbounded ratio therefore needs $n_m \to \infty$. The library builds it by diagonalization, from the eventual witnesses of `all_lengths`. At length $m$ it takes the largest factor $C \le m$ whose threshold is at most $m$, and uses that factor's universe and witness. Short lengths use a one-key fallback. Here $n_m$ grows extremely slowly, roughly like $2^{24C}$ for the factor $C$ that $m$ can afford, but the theorem only asserts existence.
:::

## Neighbourhoods in a fixed tree

The second separation needs a lower bound on lazy-finger distances in *every* tree. The bound comes from counting: every node of a binary tree has at most three neighbours, so few keys are close to any given key.

@decl LazyFinger.ball

`ball t x r` is the set of valid ranks $y < n$ with $d_t(x, y) \le r$.

**Theorem (neighbourhoods are small).** For every valid $x$, the ball of radius $r$ around $x$ has at most $7^r$ keys.

@decl LazyFinger.Neighborhood.Results.cardinality

The true bound for a graph of maximum degree three is $1 + 3(2^r - 1)$. The base $7$ is cruder, but any fixed base gives the logarithmic lower bounds below, and it changes only constants.

All keys outside the ball are at distance at least $r + 1$. Summing gives the following bounds.

**Theorem (distance sums).** For valid $x$,

$$(r + 1)\,n \;\le\; (r + 1)\,7^r + \sum_{y < n} d_t(x, y).$$

If $n \ge 2 \cdot 7^r$, then $(r + 1)\,n \le 2 \sum_y d_t(x, y)$, so the average distance from $x$ is at least $(r+1)/2$. Summing over $x$ as well, $(r + 1)\,n^2 \le 2 \sum_x \sum_y d_t(x, y)$.

@decl LazyFinger.Neighborhood.Results.distance_sum LazyFinger.Neighborhood.Results.average LazyFinger.Neighborhood.Results.pairs

Taking the largest $r$ with $2 \cdot 7^r \le n$, the average distance between two keys of any tree on $n$ keys is at least about $\tfrac12 \log_7(n/2)$. Every statement is in exact natural-number arithmetic, without asymptotics.

## Alternating pairs separate dynamic from lazy finger

The second separation uses a sequence with very little to remember at any moment, but too many different moments for one fixed tree.

@decl LazyFinger.pairBlock LazyFinger.pairBlocks LazyFinger.pairSequence LazyFinger.pairSequenceAtLength

- `pairBlock x y rounds` is $x, y, x, y, \dots$, with `rounds` copies of the pair.
- `pairBlocks` concatenates such blocks for a list of pairs.
- `pairSequence n rounds` does this for all $n^2$ ordered pairs $(x, y)$ with $x, y < n$, in lexicographic order. Pairs with $x = y$ are included and are harmless.
- `pairSequenceAtLength n m` takes $\lfloor m / 2n^2 \rfloor$ rounds and pads with copies of key $0$ to reach length exactly $m$. The padding key is valid when $n > 0$.

@decl LazyFinger.Separation.Results.length LazyFinger.Separation.Results.valid LazyFinger.Separation.Results.prescribed_length LazyFinger.Separation.Results.prescribed_valid

**Lazy finger pays the average distance.** In a fixed tree $t$, each repetition in the block of $(x, y)$ contains the transition $x \to y$, which costs $d_t(x, y)$. So the sequence costs at least $\mathit{rounds} \cdot \sum_{x, y} d_t(x, y)$, whatever the starting finger and the transitions between blocks. The neighbourhood bound gives:

**Theorem (lazy-finger lower bound).** For every tree $t$ on $n \ge 2\cdot 7^r$ keys, $\mathit{rounds}\,(r + 1)\,n^2 \le 2\,\mathrm{LF}_t(\text{pairSequence})$. The padded sequence of length $m$ satisfies the same bound with $\lfloor m/2n^2 \rfloor$ in place of $\mathit{rounds}$.

@decl LazyFinger.Separation.Results.lazy_lower LazyFinger.Separation.Results.prescribed_lower

Since the sequence has $m = 2\,\mathit{rounds}\,n^2$ requests, this is about $\tfrac14 \log_7(n/2)$ per request, in every tree.

**A dynamic BST pays a constant.** Before the block of $(x, y)$, a dynamic BST reshapes its tree so that $x$ and $y$ both lie at depth at most one. A reshape costs at most $16n$ instructions. Then every request of the block costs a constant.

**Theorem (dynamic upper bound).** From every initial tree $s$ on $n$ keys there is a legal pointer-machine execution of `pairSequence n rounds` at cost at most $n^2(16n + 6\,\mathit{rounds})$. If $\mathit{rounds} \ge 16n$, the cost is at most $7\,\mathit{rounds}\,n^2$, which is $3.5$ per request.

@decl LazyFinger.Separation.Results.dynamic_upper LazyFinger.Separation.Results.dynamic_linear

Every reshape is a real sequence of pointer instructions, charged in full; nothing switches trees for free. The final tree `t` keeps all $n$ keys. For the padded sequence, the repeated key is served after one more reshape, and is charged as well:

@decl LazyFinger.Separation.Results.prescribed_dynamic

**The gap.** Taking $n$ large enough that $\log_7 n$ exceeds a multiple of $C$, and long blocks, gives the separation. The quantifiers are those of the previous section. The optimal lazy-finger tree is chosen after the sequence is known, and the dynamic BST may start from any tree.

**Theorem (strict separation).** For every $C$ there is a universe $n \ge 1$ and a valid sequence of length at least $n$ such that from every initial tree on $n$ keys there is a legal execution of cost $k$ with $C k < \mathrm{LF}^*_n(X)$. The same holds with $C k + a(n) < \mathrm{LF}^*_n(X)$ for any startup allowance $a$.

@decl LazyFinger.Separation.Results.strict LazyFinger.Separation.Results.with_startup

**Theorem (every long length).** For every $C$ and $a$ there are $n \ge 1$ and a threshold $T \ge n$ such that every length $m \ge T$ has such a sequence of length exactly $m$.

@decl LazyFinger.Separation.Results.all_lengths

**Theorem (one family, Theorem 6).** For every allowance $a$ there is a single family $X_m$ of sequences, one of each length $m$, on universes $n_m \ge 1$, such that for every $C$, eventually, every initial tree on $n_m$ keys admits a legal execution of cost $k$ with $C k + a(n_m) < \mathrm{LF}^*_{n_m}(X_m)$.

@decl LazyFinger.Separation.Results.family

The family is built by the same diagonalization as in [Section 15.3](#sequential-scans-separate-lazy-from-root-finger), from the witnesses `pairSequenceAtLength n m` of `all_lengths`.

::: note What the sequence shows
Inside a block only two keys are in use, so almost every request has working-set number at most two. A dynamic BST exploits this. A static tree cannot, because over the whole sequence every pair is used and most pairs are far apart. Once the blocks are long ($\mathit{rounds} \ge 16n$), the working-set bound of the sequence is $O(m)$ while $\mathrm{LF}^*$ is $\Omega(m \log n)$. So, informally, the optimal lazy-finger tree does not have the working-set property, although it has the three properties of the next section. The library does not state this corollary.
:::

## Consequences for the optimal tree

The characterization of [Chapter 14](lazy-finger.html) compares $\mathrm{LF}^*$ with the weighted dynamic-finger benchmark [[WeightedFinger.costFrom]]: one positive weight per key, and a charge of $1 + \log_2\bigl(w[x_{j-1}, x_j] / \min(w_{x_{j-1}}, w_{x_j})\bigr)$ per request, where $w[x, y]$ is the total weight of the keys between $x$ and $y$ inclusive. Particular weightings give the classical bounds.

**Unit weights give dynamic finger.** With every weight equal to $1$, the interval mass is $|x - y| + 1$ and the minimum weight is $1$, so the charge is $1 + \log_2(|x_{j-1} - x_j| + 1)$. That is the dynamic-finger benchmark [[Bounds.dynamicFingerCostFrom]], with the predecessor $x_0 = p$ of the first request given explicitly.

@decl LazyFinger.Consequences.Results.unit_weights

**Theorem (dynamic finger).** Let $p < n$ and let $X$ be valid. The optimal lazy-finger cost with the finger starting at $p$ is at most $4$ times the dynamic-finger cost from $p$. With the finger starting at the root, $\mathrm{LF}^*_n(X) \le n + 4\,\mathrm{DF}_p(X)$, and if $m \ge n$ then $\mathrm{LF}^*_n(X) \le 5\,\mathrm{DF}_p(X)$.

@decl LazyFinger.Consequences.Results.dynamic_finger_from LazyFinger.Consequences.Results.dynamic_finger LazyFinger.Consequences.Results.dynamic_finger_long

The first bound uses the optimum with a specified start, [[LazyFinger.optimalCostFrom]]. The additive $n$ in the second pays once for moving the finger from the root to $p$ ([[LazyFinger.Results.initialization]]). The factor $5$ in the third absorbs it, since the dynamic-finger cost is at least $m \ge n$.

**Theorem (static optimality).** $\mathrm{LF}^*_n(X) \le 2\bigl(m + \sum_x q_x \log_2(m/q_x)\bigr)$.

@decl LazyFinger.Consequences.Results.static_optimality

The proof takes a root-finger tree whose cost is at most the entropy bound [[Bounds.staticCost]] ([[StaticTree.Results.entropy_upper_bound]]), and applies the factor 2 of the hierarchy.

**Theorem (static finger).** For every $f$, $\mathrm{LF}^*_n(X) \le 6 \sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$.

@decl LazyFinger.Consequences.Results.static_finger

The finger $f$ is any natural number, even one outside the key universe. The bound follows from static optimality, because the entropy bound is at most three times the static-finger bound [[Bounds.fingerCost]] ([Chapter 12](bounds.html)). Neither of these two bounds needs an additive term.

**Theorem (all three at once, §1.4).** For every valid $X$ there is a tree on $n$ keys that attains $\mathrm{LF}^*_n(X)$ and satisfies the three bounds, the static-finger bound for every $f$ and the dynamic-finger bound for every $p < n$.

@decl LazyFinger.Consequences.Results.simultaneous

::: check
`simultaneous` adds nothing beyond the three separate bounds and the attainment of the optimum ([[LazyFinger.Results.optimal_attained]]). Each bound is about the optimal *value* $\mathrm{LF}^*_n(X)$, so any optimal tree satisfies all three. What the theorem makes explicit is the quantifier order: one tree, chosen from the sequence, serves every $f$ and every $p$. It is not an online rule for choosing the tree.
:::
