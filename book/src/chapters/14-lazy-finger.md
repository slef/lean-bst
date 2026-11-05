# The lazy finger

A static binary search tree never changes shape. The classical way to search it, the **root finger**, starts every search at the root, so a search for $x$ costs the depth of $x$. Its optimum is well understood: the best static tree serves a sequence in time proportional to $m$ plus the entropy of the access frequencies ([Chapter 12](bounds.html#comparison-with-a-fixed-tree)). Bose, Douïeb, Iacono and Langerman (2013) studied a different way to search the same tree, the **lazy finger**: each search starts where the previous one ended. To go from $x$ to $y$, the finger climbs from $x$ to their lowest common ancestor and descends to $y$. Up to a factor of two, lazy finger is at least as good as root finger: the walk through the LCA is never longer than the walk up to the root and down again, which costs at most twice a root-finger search. And it is no better than a BST with rotations, which can simulate it. Between those two, it can be much better than root finger: a sequential scan $0, 1, \dots, n-1, 0, 1, \dots$ of length $m \ge n$ costs $O(m)$ with a lazy finger in every tree, but $\Omega(m \log n)$ with a root finger in every tree.

The optimal root-finger cost is a function of the access frequencies alone. The optimal lazy-finger cost depends on the frequencies of *consecutive pairs*. The natural entropy of those, the conditional entropy, is not the answer: the paper shows that no BST, static or not, is bounded by it within any constant factor and additive startup term ([Chapter 16](conditional-entropy.html)). What does capture it is the **weighted dynamic finger** bound of Iacono and Langerman: give every key $k$ a positive weight $w_k$, and charge a move from $x$ to $y$

$$1 + \log_2 \frac{\sum_{k = \min(x,y)}^{\max(x,y)} w_k}{\min(w_x, w_y)}.$$

The paper's main theorem, its Theorem 5, says that the best static tree with a lazy finger costs, up to constant factors, exactly as much as the best choice of weights. This chapter formalizes it, together with the four results it is assembled from: a random tree that realizes any weights (Theorem 1), the tree that this gives for a given sequence (Corollary 2), and the weights that represent a given tree (Lemma 3 and Corollary 4).

```headline lazy-finger-characterization
title: The optimal lazy-finger tree costs the best weighted dynamic finger bound, up to constant factors
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
key: yes
theorems: LazyFinger.Results.characterization_from LazyFinger.Results.characterization LazyFinger.Results.characterization_long_sequence

Let $X = x_1, \dots, x_m$ be requests to the keys $\{0, \dots, n-1\}$, and let $p < n$ be a starting key. Write $d_T(x, y)$ for the number of edges between $x$ and $y$ in a tree $T$, and $W(x,y) = \sum_{k=\min(x,y)}^{\max(x,y)} w_k$. Define, with $x_0 = p$,

$$\mathrm{LF}_p(X) = \min_{T} \sum_{i=1}^m \bigl(1 + d_T(x_{i-1}, x_i)\bigr), \qquad \mathrm{WDF}_p(X) = \inf_{w > 0} \sum_{i=1}^m \Bigl(1 + \log_2 \frac{W(x_{i-1}, x_i)}{\min(w_{x_{i-1}}, w_{x_i})}\Bigr),$$

the minimum over all binary search trees on the $n$ keys, and the infimum over all weightings that are positive on the $n$ keys. Let $\mathrm{LF}(X)$ be defined like $\mathrm{LF}_p(X)$, except that the first search starts at the root of $T$. Then

$$\mathrm{WDF}_p(X) \le 3\,\mathrm{LF}_p(X), \qquad \mathrm{LF}_p(X) \le 4\,\mathrm{WDF}_p(X),$$

and, for the root start, with an additive $n$ for the initial position,

$$\mathrm{LF}(X) + n \le 4\,\bigl(\mathrm{WDF}_p(X) + n\bigr), \qquad \mathrm{WDF}_p(X) + n \le 4\,\bigl(\mathrm{LF}(X) + n\bigr).$$

If $m \ge n$, the additive term is not needed: $\mathrm{WDF}_p(X) \le 6\,\mathrm{LF}(X)$ and $\mathrm{LF}(X) \le 5\,\mathrm{WDF}_p(X)$.

Both costs charge one unit per request, and the minimum over trees is attained. In Lean, $\mathrm{LF}_p$ is [[LazyFinger.optimalCostFrom]], $\mathrm{LF}$ is [[LazyFinger.optimalCost]], and $\mathrm{WDF}_p$ is [[WeightedFinger.optimalCostFrom]].
```

```headline lazy-finger-weights
title: Weights give a tree, and every tree is represented by weights
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
theorems: LazyFinger.Results.tree_for_weights LazyFinger.Results.tree_weights_two_sided LazyFinger.Results.tree_weights

With the notation of the previous box, write $\mathrm{LF}_p(T, X) = \sum_i (1 + d_T(x_{i-1}, x_i))$ for the lazy-finger cost of one tree $T$ from $x_0 = p$, $c_w(x, y) = 1 + \log_2\bigl(W(x,y) / \min(w_x, w_y)\bigr)$ for the weighted charge, and $\mathrm{WDF}_p(w, X) = \sum_i c_w(x_{i-1}, x_i)$.

- **Weights give a tree** (Corollary 2). For every weighting $w$ positive on $\{0, \dots, n-1\}$, every $p < n$ and every sequence $X$ of keys less than $n$, there is a tree $T$ on the $n$ keys with $\mathrm{LF}_p(T, X) \le 4\,\mathrm{WDF}_p(w, X)$. The tree may depend on $w$ and on $X$.
- **Trees give weights** (Lemma 3). For every tree $T$ there is one weighting $w$, positive everywhere, such that $1 + d_T(x, y) \le c_w(x, y) \le 3 + 2\,d_T(x, y)$ for all keys $x, y$ of $T$, and hence, for every valid start $p$ and sequence $X$, $\mathrm{LF}_p(T, X) \le \mathrm{WDF}_p(w, X) \le 3\,\mathrm{LF}_p(T, X)$.
- **The reverse comparison** (Corollary 4) is the upper half: $c_w(x,y) \le 3 + 2\,d_T(x,y)$ and $\mathrm{WDF}_p(w, X) \le 3\,\mathrm{LF}_p(T, X)$.

In Lean, $\mathrm{LF}_p(T, X)$ is [[LazyFinger.costFrom]], $c_w$ is [[WeightedFinger.charge]] and $\mathrm{WDF}_p(w, X)$ is [[WeightedFinger.costFrom]].
```

```headline random-weighted-tree
title: A random tree realizes the weighted dynamic finger bound for every pair
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
theorems: LazyFinger.Random.Results.weighted_charge

Let $w$ be positive on $\{0, \dots, n-1\}$. Draw a random order of the keys by repeatedly choosing one of the remaining keys with probability proportional to its weight. There is an assignment of a tree $T_\sigma$ on the $n$ keys to every order $\sigma$ such that, for all keys $x, y < n$,

$$\mathbb E_\sigma\bigl[\,1 + d_{T_\sigma}(x, y)\,\bigr] \;\le\; 4\,\Bigl(1 + \log_2 \frac{W(x,y)}{\min(w_x, w_y)}\Bigr).$$

The assignment depends on $w$ and $n$ only, so one random tree serves every pair at once. This is Theorem 1 of the paper, which attributes it to Seidel and Aragon; in the proof, $T_\sigma$ is the treap whose priority order is $\sigma$. In Lean, the expectation is [[Treap.Random.average]] and the right side is $4$ times [[WeightedFinger.charge]].
```

The first box is the paper's Theorem 5; the second and third are the steps of its proof. To confirm them, a reader needs only the tree shapes and depths of [Chapter 1](shapes.html), the lazy-finger distance and costs of [Section 14.1](#distance-in-a-fixed-tree) and [Section 14.3](#the-lazy-finger-cost), the weighted charge of [Section 14.5](#weighted-dynamic-finger), and, for the third box, the weighted sampling of [Chapter 31](treaps.html). The [checking page](checking.html) lists the exact reading path of each.

The rest of the chapter goes through these definitions in order and states every theorem again, in English before its Lean form. [Section 14.1](#distance-in-a-fixed-tree) defines the distance between two keys in a fixed tree, and [Section 14.2](#search-paths-and-ancestors) recounts it with ancestors, the form used for random trees. [Section 14.3](#the-lazy-finger-cost) and [Section 14.4](#the-optimal-tree) define the lazy-finger cost and its optimum, and compare them with root finger. [Section 14.5](#weighted-dynamic-finger) defines the weighted charge. [Section 14.6](#a-random-tree-for-given-weights) proves Theorem 1, [Section 14.7](#from-weights-to-a-tree-and-back) the two directions between weights and trees, and [Section 14.8](#the-characterization) assembles Theorem 5. The last section, [Section 14.9](#distance-as-boundary-crossings), rewrites the cost as a sum over the subtrees of the tree. It is not needed for Theorem 5; it is the form in which [Chapter 29](optimal-lazy-finger.html) computes the optimal tree by dynamic programming. The results that place lazy finger between root finger and rotations, and the consequences of the characterization, are in [Chapter 15](lazy-finger-hierarchy.html).

The definitions are in `Bounds/LazyFinger/Definitions/Abstract.lean`, `Bounds/WeightedFinger/Definitions/Abstract.lean`, `Bounds/LazyFinger/Edges/Definitions/Abstract.lean` and `Bounds/LazyFinger/Frequencies/Definitions/Abstract.lean`, and search paths in `Models/Rotation/Search/Abstract.lean`. The theorems are in the `Abstract.lean` files of `Bounds/LazyFinger`, `Bounds/WeightedFinger`, `Bounds/LazyFinger/Random` and `Bounds/LazyFinger/Edges`.

## Distance in a fixed tree

Keys are ranks, as everywhere in the library ([Chapter 1](shapes.html#implicit-keys)): a tree on $n$ nodes holds the keys $0, \dots, n-1$ in inorder, and the root of `node l r` is the rank `l.size`. The paper writes $r(T, i, j)$ for the time to move a pointer from $i$ to $j$; the library calls it the distance.

@decl RotationBST.LazyFinger.distance

If both ranks lie in the left subtree, or both strictly in the right subtree (with ranks shifted by `l.size + 1`), the path between them stays in that subtree, and the recursion follows it. Otherwise the root separates them, or is one of them. Then the root is their lowest common ancestor, and the path goes up from $x$ to the root and down to $y$, so its length is the sum of the two depths. Depth is [[Tree.depth]] ([Chapter 1](shapes.html#depth)), with the root at depth $0$, so the distance from a key to itself is $0$ and the distance between a parent and a child is $1$.

::: check
- The distance counts **edges**, not nodes. The cost of a search adds one unit for the request itself ([Section 14.3](#the-lazy-finger-cost)).
- On ranks that are not keys of the tree, `distance` still returns a number, because every Lean function is total, but that number means nothing. Every theorem that uses it either holds for all ranks or assumes valid ones.
:::

The depth of the lowest common ancestor is defined by the same recursion:

@decl RotationBST.LazyFinger.lcaDepth

The definitions fit together as in the paper's formula $r(T, i, j) = d_T(i) + d_T(j) - 2\,d_T(\mathrm{LCA}_T(i,j))$.

**Theorem (LCA identity).** For every tree $T$ and all ranks $x, y$, $\;d_T(x, y) + 2\,\mathrm{lcaDepth}_T(x, y) = \mathrm{depth}_T(x) + \mathrm{depth}_T(y)$.

@decl RotationBST.LazyFinger.Results.lca_identity

The identity has no hypotheses: the three totalized functions descend in lockstep, so it holds even on invalid ranks. It is stated with the subtraction moved to the other side, to stay in natural numbers.

Distance behaves like a metric on the keys. It is symmetric, it vanishes on the diagonal, and it vanishes nowhere else.

**Theorem (basic properties).** For every tree $T$: $d_T(x, y) = d_T(y, x)$ for all $x, y$; $d_T(x, x) = 0$ for every key $x$; and for keys $x, y$, $d_T(x, y) = 0$ exactly when $x = y$.

@decl RotationBST.LazyFinger.Results.symmetric RotationBST.LazyFinger.Results.repeated_key RotationBST.LazyFinger.Results.zero_distance

The triangle inequality also holds, since $d_T$ is a path length in a tree, but it is not part of the reading interface.

## Search paths and ancestors

A second description of the distance counts nodes instead of edges. Every node on the path between $x$ and $y$ is an ancestor of exactly one of them, apart from their common ancestors, which the path avoids above the LCA. This is the description that makes random trees tractable, because the probability that one key is an ancestor of another has a closed form ([Section 14.6](#a-random-tree-for-given-weights)).

The library describes the ancestors of $x$ by the search path to $x$:

@decl RotationBST.Tree.searchPath

`searchPath t lo x` lists the keys visited by an ordinary root-to-leaf search for $x$, in a tree whose inorder ranks start at `lo`, so that its root is `lo + l.size`. The search compares $x$ with the root and stops there, or continues left or right. The offset `lo` makes the keys absolute: a subtree of a larger tree can be searched with its true key range, which is how the recursion itself uses it. On valid inputs the path starts at the root and ends at $x$. For an $x$ outside the tree's range the path is the unsuccessful search path, ending at a leaf.

The search path holds exactly the proper ancestors of $x$ and $x$ itself. Below, "ancestor" includes the node itself.

**Theorem (ancestors and common ancestors).** Let $T$ have keys $lo, \dots, lo + n - 1$, and let $x, y$ be two of them. The search path to $x$ has $\mathrm{depth}(x) + 1$ keys, and the two search paths have exactly $\mathrm{lcaDepth}(x, y) + 1$ keys in common, the ancestors of the LCA.

@decl RotationBST.LazyFinger.Results.ancestor_count RotationBST.LazyFinger.Results.common_ancestor_count

Inside the statements, `x - lo` converts the absolute key back to the rank that [[Tree.depth]] and [[LazyFinger.lcaDepth]] expect.

Subtracting gives the distance as a sum of events, one for each key $a$: $a$ counts once if it is an ancestor of exactly one endpoint, and not at all otherwise.

**Theorem (distance as ancestor events).** For keys $x, y$ of $T$,

$$d_T(x, y) \;=\; \sum_{a} \Bigl([a \preceq x] + [a \preceq y] - 2\,[a \preceq x \text{ and } a \preceq y]\Bigr),$$

where $a$ ranges over the keys of $T$ and $a \preceq x$ means that $a$ is on the search path to $x$.

@decl RotationBST.LazyFinger.Results.distance_events

The sum is in $\mathbb R$, with Iverson brackets written as `if … then 1 else 0`. Each term is $0$ or $1$; the subtraction is real only so that the statement can be averaged directly. Taking expectations over a random tree turns each bracket into the probability of an ancestor event, which is exactly how Theorem 1 is proved.

## The lazy-finger cost

A lazy finger serves a request for $x$, with the finger at $p$, by walking from $p$ to $x$ and leaving the finger at $x$. The cost of a sequence follows the finger:

@decl RotationBST.LazyFinger.costFrom RotationBST.LazyFinger.cost

`costFrom t p xs`, written $\mathrm{LF}_p(T, X)$ in the headline boxes, starts with the finger at the key `p` and charges each request $1 + d_T(x_{i-1}, x_i)$, with $x_0 = p$. The unit is a charge per request, as in the static cost [[StaticTree.cost]] and the total cost of an online algorithm ([Chapter 5](online.html)). Without it, a repeated request would cost nothing.

`cost t xs` is the paper's convention: the first search starts at the root, which in a node `node l r` is the rank `l.size`. On the empty tree there is no root, and `cost` returns `xs.length`, one unit per request. The empty tree has no keys, so this case only matters for totality.

In the paper's notation, $\mathtt{cost}(T, X) = m + R_\ell(T, X)$, and the root-finger cost is $\mathtt{StaticTree.cost}(T, X) = m + R_r(T, X)$ ([Chapter 12](bounds.html#comparison-with-a-fixed-tree)).

**Theorem (request charge).** For every tree, start and sequence, `costFrom` is at least the number of requests.

@decl RotationBST.LazyFinger.Results.request_charge

The start matters only once. Moving the initial finger from $p$ to the root changes the distance of the first move by at most the depth of $p$, which is less than $n$.

**Theorem (initialization).** For every tree $T$ on $n$ keys, every key $p$ of $T$ and every sequence of keys of $T$, the lazy-finger costs from $p$ and from the root differ by at most $n$, in both directions.

@decl RotationBST.LazyFinger.Results.initialization

Lazy finger is never much worse than root finger in the same tree: the path from $x_{i-1}$ through the LCA to $x_i$ is no longer than the path from $x_{i-1}$ up to the root and down to $x_i$.

**Theorem (lazy finger versus root finger).** For every tree $T$ and every sequence $X$, the lazy-finger cost from the root is at most twice the root-finger cost: $\mathtt{cost}(T, X) \le 2\,\mathtt{StaticTree.cost}(T, X)$.

@decl RotationBST.LazyFinger.Results.root_finger

The proof bounds each move by $\mathrm{depth}(x_{i-1}) + \mathrm{depth}(x_i)$ and sums: each depth appears at most twice, and the first search starts at the root, where $\mathrm{depth}(x_0) = 0$. With the unit charges this gives $m + 2\sum_i \mathrm{depth}(x_i) \le 2\,(m + \sum_i \mathrm{depth}(x_i))$. This is the comparison of §1.4 of the paper. The theorem has no validity hypothesis.

## The optimal tree

The benchmark of the chapter is the best fixed tree for a given sequence.

@decl RotationBST.LazyFinger.optimalCost RotationBST.LazyFinger.optimalCostFrom

`optimalCost n xs` is the infimum of `cost t xs` over all shapes `t` with $n$ nodes, and `optimalCostFrom n p xs` the same with every tree started at the key `p`. Both are `sInf` of a set of natural numbers. Such a set has a least element whenever it is nonempty, and it is never empty here, since there are trees of every size. So both infima are minima, attained by actual trees.

**Theorem (attainment).** For every $n$, every start $p$ and every sequence, some tree on $n$ keys has lazy-finger cost exactly `optimalCost n xs`, and some tree on $n$ keys has cost from $p$ exactly `optimalCostFrom n p xs`.

@decl RotationBST.LazyFinger.Results.optimal_attained RotationBST.LazyFinger.Results.optimal_from_attained

These are existence statements. They do not compute the optimal tree. The paper's $O(n^3)$ dynamic program, and its proof of optimality, are the subject of [Chapter 29](optimal-lazy-finger.html).

**Theorem (the optimum is a lower bound).** For every tree $T$ and every sequence, $\mathtt{optimalCost}(|T|, X) \le \mathtt{cost}(T, X)$; and the optimum is at least the number of requests.

@decl RotationBST.LazyFinger.Results.optimal_le RotationBST.LazyFinger.Results.optimal_request_charge

Combined with the comparison with root finger, the optimal lazy-finger tree is at most twice as expensive as *every* root-finger tree, and in particular as the optimal one.

**Theorem (optimal lazy finger versus root finger).** For every tree $T$ and every sequence $X$, $\mathtt{optimalCost}(|T|, X) \le 2\,\mathtt{StaticTree.cost}(T, X)$.

@decl RotationBST.LazyFinger.Results.optimal_root_finger

This is the first inequality of the paper's Theorem 6, the hierarchy root finger, lazy finger, rotations. [Chapter 15](lazy-finger-hierarchy.html) proves the rest of the hierarchy, and the separations that make it strict.

## Weighted dynamic finger

The other side of the characterization is a bound that mentions no tree at all. Assign each key $k$ a weight $w_k$. The mass of a key range counts both endpoints:

@decl RotationBST.WeightedFinger.mass

`mass w x y` is $W(x, y) = \sum_{k = \min(x,y)}^{\max(x,y)} w_k$. It does not depend on the order of $x$ and $y$.

@decl RotationBST.WeightedFinger.charge

The charge for moving from $x$ to $y$ is $1 + \log_2\bigl(W(x,y) / \min(w_x, w_y)\bigr)$. It is small when the range between the two keys is light compared with the lighter endpoint. Think of $W(x, y)/w_x$ as the number of "units of weight $w_x$" that separate the keys. With unit weights it is $|x - y| + 1$, the rank distance of the dynamic finger bound; with weights concentrated near a few keys, moves among those keys are cheap even when many light keys lie between them.

The charge is a real number with a real logarithm. When the weights are positive, the ratio is at least $1$ and the logarithm is nonnegative. The definition itself assumes nothing, and with zero or negative weights the value is a totalized artefact (`Real.logb 2` of a nonpositive number is defined in Mathlib, but is not meaningful here). The theorems assume positivity where they need it.

**Theorem (basic properties of the charge).**
- With unit weights, the charge from $x$ to $y$ is $1 + \log_2(|x - y| + 1)$, the dynamic finger charge of [[Bounds.dynamicFingerCostFrom]].
- If $w_x > 0$, a repeated key costs exactly $1$.
- The charge is symmetric in $x$ and $y$.
- Multiplying all weights by the same positive constant does not change the charge.
- If the weights are positive on the range between $x$ and $y$, the charge is at least $1$.

@decl RotationBST.WeightedFinger.Results.unit_weights RotationBST.WeightedFinger.Results.repeated_key RotationBST.WeightedFinger.Results.symmetric RotationBST.WeightedFinger.Results.scale_invariant RotationBST.WeightedFinger.Results.request_charge

Scale invariance means that only the relative weights matter; the weights need not sum to $1$. The lower bound $1$ is the request charge again: like the lazy-finger cost, the weighted charge pays one unit for every request, including repeats.

The bound for a sequence adds the charges of consecutive requests, from an explicit start:

@decl RotationBST.WeightedFinger.costFrom

`costFrom w p xs` is $\mathrm{WDF}_p(w, X) = \sum_i c_w(x_{i-1}, x_i)$ with $x_0 = p$, the weighted dynamic finger bound of Iacono and Langerman. The optimal choice of weights gives a function of the sequence alone:

@decl RotationBST.WeightedFinger.optimalCostFrom

`optimalCostFrom n p xs` is the infimum of `costFrom w p xs` over all weightings that are positive on the keys $0, \dots, n-1$. Values of $w$ outside that range are unconstrained, and on valid requests the charges never read them.

::: check
- **An infimum, not a minimum.** The weights range over a continuum, and the library does not claim that a best weighting exists. The paper writes $\min_W$.
- **Valid inputs.** In Lean, `sInf` of a set of reals that is not bounded below is $0$. The library proves the lower bound $m$ for the set when the start and the requests are keys, so every theorem about `optimalCostFrom` assumes $p < n$ and that every request is less than $n$.
- **A start key.** The weighted bound always starts from a key $p$. Unlike a tree, a weighting has no root to start from.
:::

Under those hypotheses the optimum behaves as expected.

**Theorem (the weight optimum).** Let $p < n$ and let every request be less than $n$. Then $\mathrm{WDF}_p(X) \ge m$, and $\mathrm{WDF}_p(X) \le \mathrm{WDF}_p(w, X)$ for every weighting $w$ positive on the $n$ keys.

@decl RotationBST.WeightedFinger.Results.optimal_request_charge RotationBST.WeightedFinger.Results.optimal_le

## A random tree for given weights

The first step of the characterization builds a tree from weights. The tree is random: it is the treap of Seidel and Aragon, whose priorities are drawn according to the weights. The paper describes it as "recursively pick the root using the normalized weights of all nodes as probabilities". The library draws a whole random order of the keys at once, by weighted sampling without replacement, and builds the treap in which earlier keys sit higher. The expectation over this sampling process is [[Treap.Random.average]], defined in [Chapter 31](treaps.html): it chooses the first key of the order with probability proportional to its weight, removes it, and averages recursively over the order of the rest. It is a finite sum, not a measure-theoretic expectation.

The key fact about the treap is the probability of an ancestor event: a key $a$ is an ancestor of $x$ exactly when $a$ comes first, among the keys between $a$ and $x$, in the order, and under weighted sampling that happens with probability $w_a / W(a, x)$. Averaging the ancestor-event formula of [Section 14.2](#search-paths-and-ancestors) gives the expected distance exactly.

**Theorem (expected distance in a weighted treap).** Let $w$ be positive on the keys $lo, \dots, lo + n - 1$. There is an assignment $\sigma \mapsto T_\sigma$ of a tree on $n$ nodes to every order, such that for all keys $x, y$ in the range,

$$\mathbb E_\sigma\bigl[d_{T_\sigma}(x, y)\bigr] \;=\; \sum_{a} \Bigl(\frac{w_a}{W(a, x)} + \frac{w_a}{W(a, y)} - 2\,\frac{w_a}{W(\min(a,x,y), \max(a,x,y))}\Bigr),$$

where $a$ ranges over the keys and the expectation is over the weighted random order.

@decl RotationBST.LazyFinger.Random.Results.expected_distance

The tree $T_\sigma$ holds the ranks $0, \dots, n-1$ and stands for the keys $lo, \dots, lo + n - 1$; hence `x - lo` in the statement. The third term is the probability that $a$ is a common ancestor: it must come first in the smallest range containing $a$, $x$ and $y$. The family is existential in the statement. In the proof it is the treap of the order, chosen through the existence of heap-ordered trees in [Chapter 31](treaps.html).

Bounding the sum by logarithms gives Theorem 1. Split the keys $a$ into those below, between and above $x$ and $y$. For a key outside the range, the term is a difference of two probabilities, such as $w_a / W(a, x) - w_a / W(a, y)$ for $a < x \le y$, and these differences sum to a logarithmic amount that does not depend on the weight outside the range. For a key inside the range, the terms are like $w_a / W(x, a)$, and the inequality $b/(a + b) \le \ln(a + b) - \ln a$ compares their sum with the growth of $\ln W(x, a)$ as $a$ moves from $x$ to $y$. The library obtains $4 \ln\bigl(W(x,y)/\min(w_x, w_y)\bigr)$ for the expected distance, then replaces $\ln$ by $\log_2$ and adds the request charge.

**Theorem 1 (a random tree realizes the weights).** Let $w$ be positive on $\{0, \dots, n-1\}$. There is an assignment $\sigma \mapsto T_\sigma$ of a tree on $n$ nodes to every order such that, for all keys $x, y < n$, $\;\mathbb E_\sigma[1 + d_{T_\sigma}(x, y)] \le 4\,c_w(x, y)$.

@decl RotationBST.LazyFinger.Random.Results.weighted_charge

The quantifiers carry the content. The family $T$ is chosen after $w$ and $n$ and before $x$ and $y$, so one random tree is good for all pairs at once, and, by linearity of expectation, for every sequence. The paper states the bound as $O(\lg(W/\min))$ without the request charge; the library's form, with the unit on both sides, has the explicit constant $4$.

::: note Two statements, two families
`expected_distance` and `weighted_charge` are proved from the same treap family, but each statement quantifies its own family existentially. As stated, they do not assert that one family satisfies both.
:::

## From weights to a tree and back

Theorem 1 is an average over trees. For a fixed sequence, some single tree is at least as good as the average: this is the probabilistic method, and it is Corollary 2 of the paper.

**Corollary 2 (weights give a tree).** Let $w$ be positive on $\{0, \dots, n-1\}$, let $p < n$, and let $X$ be a sequence of keys less than $n$. There is a tree $T$ on $n$ keys with $\mathrm{LF}_p(T, X) \le 4\,\mathrm{WDF}_p(w, X)$.

@decl RotationBST.LazyFinger.Results.tree_for_weights

The proof sums Theorem 1 over the consecutive pairs of $X$, so that the expected cost of $T_\sigma$ is at most $4\,\mathrm{WDF}_p(w, X)$, and then picks an order $\sigma$ whose cost is at most the average. The tree therefore depends on the sequence as well as on the weights. It is fixed once chosen: it serves all of $X$ without changing.

The converse direction represents a given tree by weights. The proof gives a key at depth $d$ the weight $4^{-(d+1)}$, the same weights as in the proof of the entropy bound of [Chapter 12](bounds.html#comparison-with-a-fixed-tree). (The paper uses $4^{-d}$; the constant factor cancels in every charge, by scale invariance.)

- **Lower bound on the charge.** The range between $x$ and $y$ contains their LCA, whose weight is $4^{-(\ell + 1)}$ for $\ell$ its depth. The lighter endpoint has weight $4^{-(\max(d_x, d_y) + 1)}$. So the mass ratio is at least $4^{\max(d_x, d_y) - \ell}$, and its logarithm at least $2\max(d_x,d_y) - 2\ell \ge d_x + d_y - 2\ell = d_T(x, y)$.
- **Upper bound on the charge.** The range between $x$ and $y$ lies inside the subtree of their LCA. In that subtree the weights decrease by a factor of $4$ per level while the number of nodes per level at most doubles, so the total is at most a constant times the LCA's weight. Dividing by the lighter endpoint's weight, the logarithm is at most a constant plus $2\,(\max(d_x, d_y) - \ell) \le 2\,d_T(x, y)$.

**Lemma 3 (trees give weights).** For every tree $T$ there is a weighting $w$, positive everywhere, such that for all keys $x, y$ of $T$, $\;1 + d_T(x, y) \le c_w(x, y) \le 3 + 2\,d_T(x, y)$. Consequently, for every key $p$ of $T$ and every sequence $X$ of keys of $T$, $\;\mathrm{LF}_p(T, X) \le \mathrm{WDF}_p(w, X) \le 3\,\mathrm{LF}_p(T, X)$.

@decl RotationBST.LazyFinger.Results.tree_weights_two_sided

The weighting depends on $T$ only: one weighting works for every pair, every start and every sequence. The sequence bounds follow by summing the pairwise bounds, using $3 + 2d \le 3\,(1 + d)$.

**Corollary 4 (the reverse comparison).** For every tree $T$ there is a weighting $w$, positive everywhere, with $c_w(x, y) \le 3 + 2\,d_T(x, y)$ for all keys $x, y$ of $T$, and $\mathrm{WDF}_p(w, X) \le 3\,\mathrm{LF}_p(T, X)$ for every key $p$ and every sequence $X$ of keys of $T$.

@decl RotationBST.LazyFinger.Results.tree_weights

Corollary 4 is the upper half of Lemma 3, and it is the half that the characterization uses: every tree's cost is at least a third of the weighted bound of its own weights, hence at least a third of the optimal weighted bound.

::: caveat Compared with the paper
The paper's Lemma 3 states the lower bound on the charge, $r(T, i, j) \le \lg\bigl(W(i,j)/\min(w_i, w_j)\bigr)$, and its proof shows $\lg(\cdot) \ge 2\,r(T, i, j)$. Its Corollary 4, $\sum_i r(T, x_{i-1}, x_i) = \Omega(\min_W \sum_i \lg(\cdot))$, needs the opposite comparison, $\lg(\cdot) = O(1 + r(T, i, j))$ for the same weights. The library proves both directions in `tree_weights_two_sided`. The upper bound uses the total weight of the LCA's subtree, as sketched above, not only the LCA's own weight.
:::

## The characterization

The two directions combine as in the paper's proof of Theorem 5. For the upper bound, take any weighting $w$: Corollary 2 gives a tree of cost at most $4\,\mathrm{WDF}_p(w, X)$, so the optimal tree costs at most that much, and taking the infimum over $w$ gives $\mathrm{LF}_p \le 4\,\mathrm{WDF}_p$. For the lower bound, take an optimal tree, which exists by attainment: Corollary 4 gives a weighting whose weighted cost is at most $3\,\mathrm{LF}_p$, and the infimum over weights is at most that.

**Theorem 5 (characterization from a common start).** Let $p < n$ and let $X$ be a sequence of keys less than $n$. Then $\mathrm{WDF}_p(X) \le 3\,\mathrm{LF}_p(X)$ and $\mathrm{LF}_p(X) \le 4\,\mathrm{WDF}_p(X)$.

@decl RotationBST.LazyFinger.Results.characterization_from

This is the cleanest form: both benchmarks start from the same key, and there is no additive term. The paper's tree cost starts at the root of each tree, which has no counterpart for weights. The initialization theorem of [Section 14.3](#the-lazy-finger-cost) bounds the difference by $n$, and gives the root-start form.

**Theorem 5 (root start).** Let $p < n$ and let $X$ be a sequence of keys less than $n$. Then $\mathrm{WDF}_p(X) \le 3\,(\mathrm{LF}(X) + n)$ and $\mathrm{LF}(X) \le n + 4\,\mathrm{WDF}_p(X)$.

@decl RotationBST.LazyFinger.Results.characterization_root

On the weighted side, $p$ is any key: the comparison holds for every choice of start for the weights simultaneously. Adding $n$ to both benchmarks makes the two inequalities symmetric:

**Theorem 5 (with startup).** Under the same hypotheses, $\mathrm{LF}(X) + n \le 4\,(\mathrm{WDF}_p(X) + n)$ and $\mathrm{WDF}_p(X) + n \le 4\,(\mathrm{LF}(X) + n)$.

@decl RotationBST.LazyFinger.Results.characterization

On long sequences the additive term disappears, because both benchmarks charge at least one unit per request, so each is at least $m \ge n$.

**Theorem 5 (long sequences).** If moreover $n \le m$, then $\mathrm{WDF}_p(X) \le 6\,\mathrm{LF}(X)$ and $\mathrm{LF}(X) \le 5\,\mathrm{WDF}_p(X)$.

@decl RotationBST.LazyFinger.Results.characterization_long_sequence

::: caveat Compared with the paper
The paper states Theorem 5 as $\min_T \sum_i r(T, x_{i-1}, x_i) = \Theta\bigl(\min_W \sum_i \lg(W(x_{i-1}, x_i) / \min(w_{x_{i-1}}, w_{x_i}))\bigr)$, with $x_0$ the root of $T$. The library's statements differ in four explicit ways.
- **Unit charges.** Both sides charge one unit per request. The paper's sums have none.
- **The start.** The weighted side starts from an explicit key $p$. The tree side starts either from the same key (`characterization_from`) or from the root, at the price of an additive $n$ (`characterization_root`, `characterization`) or of the assumption $m \ge n$ (`characterization_long_sequence`).
- **Infimum.** The minimum over weights is an infimum; the minimum over trees is attained.
- **Constants.** All constants are explicit, and $\log_2$ is base two on both sides.
:::

The characterization is used in two places. [Chapter 15](lazy-finger-hierarchy.html) derives from it that the optimal lazy-finger tree satisfies the static finger, static optimality and dynamic finger bounds simultaneously, and [Chapter 23](greedy-finger.html) proves that GreedyASS is competitive with both benchmarks at once.

## Distance as boundary crossings

The last section gives a third description of the cost, which is not needed for the characterization. Each edge of a tree connects a subtree to its parent, and each subtree holds a contiguous range of keys. A move from $x$ to $y$ uses that edge exactly when one of $x, y$ is in the subtree's range and the other is not. So the lazy-finger cost of a sequence is a sum, over the subtrees, of the number of times the sequence crosses the boundary of the subtree's key range. The number of crossings of a range depends only on the range and the sequence, not on the tree. This turns the search for an optimal tree into an optimization over nested ranges, which is the dynamic program of [Chapter 29](optimal-lazy-finger.html).

@decl RotationBST.LazyFinger.cut RotationBST.LazyFinger.intervalCost RotationBST.LazyFinger.edgeMovement RotationBST.LazyFinger.crossings

- `cut lo hi x y` is $1$ if exactly one of $x, y$ lies in the half-open range $[lo, hi)$, and $0$ otherwise.
- `intervalCost w t lo` sums a toll `w lo hi` over the key ranges of all nonempty subtrees of `t`, whose keys start at `lo`, *including `t` itself*. The toll of the whole tree's range stands for the edge from the tree to its parent, which a subtree has and the whole tree does not.
- `edgeMovement t lo x y` uses the toll `cut`: it counts the subtrees separating $x$ from $y$, that is, the edges of the path between them, plus the incoming edge if only one endpoint is inside. The endpoints may lie outside `t`, which is what lets the movement of a global sequence be split among subtrees.
- `crossings lo hi p xs` counts the consecutive pairs of the sequence, from $x_0 = p$, that cross the boundary of $[lo, hi)$.

The basic facts are the three cases of a single move.

**Theorem (one move, by subtrees).** Let $T$ have keys $lo, \dots, lo + n - 1$. If neither $x$ nor $y$ is a key of $T$, the move uses no edge of $T$ and does not enter it. If $x$ is a key of $T$ and $y$ is not, it uses the path from $x$ to the root of $T$ and the edge above it, $\mathrm{depth}(x) + 1$ edges. If both are keys of $T$, it uses exactly $d_T(x, y)$ edges, and the whole tree's own range contributes nothing.

@decl RotationBST.LazyFinger.Edges.Results.outside RotationBST.LazyFinger.Edges.Results.entering RotationBST.LazyFinger.Edges.Results.distance

Summing over the moves of a sequence exchanges the two sums: the cost is the number of requests plus, for each subtree, the number of times the sequence crosses its range.

**Theorem (cost as crossings).** For every tree $T$, every key $p$ and every sequence $X$ of keys of $T$, $\;\mathrm{LF}_p(T, X) = m + \sum_{S} \mathrm{crossings}(S, p, X)$, where $S$ ranges over the key ranges of the nonempty subtrees of $T$, including $T$'s own.

@decl RotationBST.LazyFinger.Edges.Results.sequence

The root start fits the same form. Start the sequence instead at the key $n$, just outside the tree: the first move enters the tree through an imaginary edge above its root, so it costs exactly one more than starting at the root, and nothing else changes.

**Theorem (root start as crossings).** For every tree $T$ on $n$ keys and every sequence $X$ of its keys, $\;\mathtt{cost}(T, X) + [X \ne \varnothing] = m + \sum_S \mathrm{crossings}(S, n, X)$.

@decl RotationBST.LazyFinger.Edges.Results.initialization

The correction $[X \neq \varnothing]$ does not depend on the shape, so a tree that minimizes the right side also minimizes the root-start cost. This is how [Chapter 29](optimal-lazy-finger.html) computes [[LazyFinger.optimalCost]] with the same dynamic program as [[LazyFinger.optimalCostFrom]].

A rotation changes exactly one subtree: the two nodes it moves swap which of them is the parent, so one subtree range disappears and one new range appears, and all other subtree ranges stay the same. Hence a rotation changes the sum by at most one toll.

**Theorem (rotation sensitivity).** Let every toll be at most $C$. If $s$ rotates to $t$, then the interval cost of $t$ is at most that of $s$ plus $C$. In particular, if every range is crossed at most $C$ times by a sequence $X$ from $p$, then one rotation increases $\mathrm{LF}_p(\cdot, X)$ by at most $C$.

@decl RotationBST.LazyFinger.Edges.Results.rotation RotationBST.LazyFinger.Edges.Results.sequence_rotation

[[Rotate]] is a single rotation anywhere in the tree ([Chapter 2](rotations.html)). These two bounds say how sensitive the lazy-finger cost is to the shape: trees one rotation apart cost almost the same on a sequence that crosses every range only a few times. No other theorem of the reading interface uses them.

The crossings of a range depend on the sequence only through the number of times each ordered pair of keys occurs consecutively. The library makes this explicit:

@decl RotationBST.LazyFinger.frequency RotationBST.LazyFinger.frequencyToll

`frequency p xs a b` is the paper's $f_X(a, b)$: the number of indices $i$ with $x_{i-1} = a$ and $x_i = b$, counting the initial pair $(p, x_1)$. `frequencyToll n f lo hi` sums $f(a, b)$ over the pairs of keys $a, b < n$ that cross the boundary of $[lo, hi)$. Applied to the pair frequencies of a sequence of valid keys, it equals `crossings lo hi p xs`; the library proves this as the internal lemma `frequencyToll_eq_crossings`. So the optimal tree is a function of the $n \times n$ table of pair frequencies, as the paper observes. [Chapter 29](optimal-lazy-finger.html) computes the tolls from that table by prefix sums, and [Chapter 16](conditional-entropy.html) uses the same table for the conditional entropy.
