# Multiple trees

A request sequence often has more structure than its key frequencies show. If key $3$ is always followed by key $17$, the second request is predictable from the first, however rare $17$ is overall. The natural measure of this predictability is the empirical *conditional entropy* $H$ of each request given the previous one, and the natural benchmark is $m(1 + H)$ for $m$ requests: one unit per request, plus the information it carries given its predecessor. [Chapter 16](conditional-entropy.html) defines this benchmark and proves, following Lemma 7 of Bose, Douïeb, Iacono and Langerman [-@bose2016], that binary search trees cannot reach it: no execution of a BST, even one that rotates and knows the whole sequence in advance, stays within a constant factor of $m(1+H)$, plus a startup term depending only on $n$, on every sequence. A lazy finger can be simulated by rotations at a constant factor ([Chapter 15](lazy-finger-hierarchy.html)), so the optimal lazy-finger tree of [Chapter 29](optimal-lazy-finger.html), which adapts to where the previous search ended, cannot reach it either.

Theorem 9 of the same paper shows that the benchmark is reachable once the structure may hold several trees. Store, for every key $p$, a small search tree holding the keys that most often follow $p$, each with a pointer to its own small tree, and one shared balanced tree as a fallback. With $c$ successors per key, the structure has $O(nc)$ words, and each request costs about $\log(1/\Pr[x \mid p])$ when it hits and $O(\log n)$ when it misses. Misses are rare transitions, so the total is within a factor $\log n / \log c$ of $m(1 + H)$. With $c = n^\varepsilon$, this is a constant factor in polynomial space, the consequence the paper draws in its Section 7.

```headline multiple-trees
title: Multiple trees serve every sequence within $O(\log_c n)$ of the conditional-entropy bound in $O(nc)$ words
source: @bose2016
theorems: MultipleTrees.Results.sequence MultipleTrees.Results.polynomial_space

Let $n \ge 1$ and $1 \le c \le n$. Let $p$ be a key and $X = x_1, \dots, x_m$ a sequence of keys, all in $\{0, \dots, n-1\}$. Let $F_{ab}$ be the number of indices $j$ with $(x_{j-1}, x_j) = (a, b)$, where $x_0 = p$, let $R_a = \sum_b F_{ab}$, and let

$$I(X) \;=\; \sum_{a,b \,:\, F_{ab} > 0} F_{ab} \log_2 \frac{R_a}{F_{ab}}$$

be the empirical conditional information of $X$, so that $I = mH$. The multiple-tree store built from $F$ with capacity $c$ uses at most $10nc$ words, and serves $X$, starting from $p$, at total cost at most

$$6\,\bigl(m + I(X)\bigr)\, \frac{1 + \log_2 n}{1 + \log_2 c}.$$

Moreover, for every $\varepsilon > 0$ there is a capacity $c$, depending only on $n$ and $\varepsilon$, such that for every $p$ and $X$ the store built from $F$ uses at most $20\,n^{1+\varepsilon}$ words and serves $X$ at cost at most $\frac{6}{\min(\varepsilon, 1)}\, m\,(1 + H)$.

The cost is that of the linked-search model of [Chapter 11](linked-search.html): one unit per visited tree node and per pointer link followed. The store is built from the transition counts of the very sequence it serves, and the time to build it is not part of the bound; the counts themselves are not stored. In Lean, the execution is [[RotationBST.LinkedSearch.Execution]], the space [[RotationBST.LinkedSearch.Store.words]], the counts [[RotationBST.LazyFinger.frequency]], $m + I$ is [[RotationBST.ConditionalEntropy.cost]] and $H$ is [[RotationBST.ConditionalEntropy.entropy]].
```

The box is enough to confirm the result; its reading path consists of the linked-search model, the conditional-entropy definitions and the construction of this chapter. The rest of the chapter builds the structure and proves the bound. [Section 30.1](#offline-preprocessing-online-queries) explains the setting, [Section 30.2](#selecting-the-successors) and [Section 30.3](#local-trees) build the local trees, [Section 30.4](#the-store) assembles them, [Section 30.5](#serving-one-request) bounds a single request, and [Section 30.6](#the-tradeoff) states Theorem 9 and its Section 7 consequence in full.

The definitions are in `Algorithms/MultipleTrees/Definitions/Abstract.lean`, `Selection/Definitions/Abstract.lean` and `Cache/Definitions/Abstract.lean`; the theorems are in `Algorithms/MultipleTrees/Abstract.lean`, `Selection/Abstract.lean` and `Cache/Abstract.lean`.

## Offline preprocessing, online queries

The structure is static, like the optimal trees of [Chapter 29](optimal-lazy-finger.html): it is built once, from the transition counts of the sequence, and then serves the sequence without changing. Three conventions follow, and the theorems state each of them explicitly.

- **The counts are used for preprocessing only.** The store holds trees and pointers, nothing else: a query compares keys and follows pointers, and never consults a frequency. [[RotationBST.LinkedSearch.Store.words]] counts the store's words, and the transition matrix is not among them.
- **Preprocessing time is excluded.** The bounds concern the queries. No theorem bounds the time to compute the counts, sort them and build the trees, which is polynomial but not formalized.
- **The initial predecessor is explicit.** The first request is served from the local tree of a given key $p$, and the pair $(p, x_1)$ is a transition like any other.

The cost model is the linked-search model of [Chapter 11](linked-search.html). A [[RotationBST.LinkedSearch.Store]] is a directory of local trees, one per key, and a shared fallback tree. Each node stores a key, two children and a pointer to a local tree. A cursor holds the local tree of the previous request. [[RotationBST.LinkedSearch.Request]] serves a key $x$ by an ordinary comparison search in the cursor's local tree. If it finds $x$, it follows $x$'s stored pointer, at cost $1$. If not, it follows the fallback pointer, at cost $1$, searches the fallback tree, and follows the pointer found there, at cost $1$. Each visited node costs $1$. In both cases the cursor ends at $x$'s local tree. [[RotationBST.LinkedSearch.Execution]] chains requests, adding their costs.

Lazy finger and multiple trees are both ways of exploiting where the previous request was. A lazy finger walks from the previous key inside one tree, so all predecessors share one shape. Multiple trees give each predecessor its own shape, at the price of $n$ trees, which is why they can reach the conditional-entropy bound and a single tree cannot.

## Selecting the successors

For a fixed predecessor $p$, the local tree holds the $c$ keys that most often follow $p$, where $c$ is the *capacity*.

@decl RotationBST.MultipleTrees.ranking RotationBST.MultipleTrees.selected

`ranking n frequency` lists the keys $0, \dots, n-1$ by nonincreasing frequency, using a merge sort; how ties are ordered does not matter for the bounds. `selected n capacity frequency` keeps the first `capacity` of them. Here `frequency` is one row of the transition matrix, the counts $F_{pb}$ for a fixed $p$.

**Theorem (selection).** The selected list has $\min(c, n)$ entries, has no repetitions, and contains only keys less than $n$. Every selected key is at least as frequent as every omitted key.

@decl RotationBST.MultipleTrees.Selection.Results.size RotationBST.MultipleTrees.Selection.Results.distinct RotationBST.MultipleTrees.Selection.Results.valid RotationBST.MultipleTrees.Selection.Results.dominates

The point of the selection is that an omitted successor is rare. If $c \le n$ keys are kept and $y$ is not among them, then each of the $c$ kept keys is at least as frequent as $y$, so $c \cdot F_{py} \le R_p$, the row total.

**Theorem (misses are rare).** If $c \le n$ and $y < n$ is not selected, then $c \cdot F_{py} \le R_p$. If moreover $c \ge 1$ and $F_{py} > 0$, then $\log_2 c \le \log_2(R_p / F_{py})$.

@decl RotationBST.MultipleTrees.Selection.Results.miss RotationBST.MultipleTrees.Selection.Results.miss_information

The second form is the one the tradeoff uses: a miss costs $O(\log n)$, but it only happens on a transition whose information $\log_2(R_p/F_{py})$ is already at least $\log_2 c$.

## Local trees

@decl RotationBST.MultipleTrees.cacheKeys RotationBST.MultipleTrees.cacheTree

`cacheKeys` sorts the selected keys into increasing order, so that they can label a search tree. `cacheTree` builds a shape for them with [[RotationBST.WeightedSearch.balancedBuild]] of [Chapter 33](prefix-sums.html), weighted by their frequencies and mixed with a uniform baseline, and labels its nodes with the keys in inorder using [[RotationBST.Tree.labelWith]]. The baseline gives every stored key logarithmic depth, and the frequencies give frequent successors small depth.

**Theorem (local trees).** The local tree has $\min(c, n)$ nodes. Its inorder key list is the sorted selection, a permutation of the selected keys, and it is a valid search tree.

@decl RotationBST.MultipleTrees.Cache.Results.size RotationBST.MultipleTrees.Cache.Results.keys RotationBST.MultipleTrees.Cache.Results.ordered

**Theorem (search in a local tree).** An ordinary comparison search for a key $x$ in the local tree finds it exactly when $x$ is selected. If $c \ge 1$, then whether it succeeds or not, it visits at most $\log_2(2\min(c, n)) + 1$ nodes. If $x$ is selected and $F_{px} > 0$, it visits at most $\log_2(3R_p / F_{px}) + 1$ nodes.

@decl RotationBST.MultipleTrees.Cache.Results.membership RotationBST.MultipleTrees.Cache.Results.uniform RotationBST.MultipleTrees.Cache.Results.weighted

The search is [[RotationBST.LabelledTree.lookup]], which returns whether the key was found and the number of visited nodes; an unsuccessful search can visit nodes too. In the weighted bound, $R_p$ is the total of the whole row, not only of the selected keys, which is weaker but is the quantity that appears in the conditional information.

## The store

@decl RotationBST.MultipleTrees.rootAddress RotationBST.MultipleTrees.fallbackTree RotationBST.MultipleTrees.build

`build n capacity positive frequency` is the whole structure, for a universe of $n \ge 1$ keys and a full transition matrix `frequency`. The local tree of $p$ is `cacheTree` for row $p$. The fallback is a local tree with capacity $n$ and all frequencies zero: it holds every key, in a balanced shape. [[RotationBST.LinkedSearch.attach]] fills in the successor pointers during preprocessing: a node holding key $y$ points to the local tree of $y$. Local trees are addressed by `Fin n`, and `rootAddress` converts a key to its address; the reduction modulo $n$ only makes the function total, since every stored key is already less than $n$. The matrix is an argument of `build`, not a field of the store.

**Theorem (space).** The store has exactly $n \min(c, n) + n$ nodes and $4(n\min(c, n) + n) + n + 1$ words. For $c \ge 1$, that is at most $10nc$ words.

@decl RotationBST.MultipleTrees.Results.nodes RotationBST.MultipleTrees.Results.words RotationBST.MultipleTrees.Results.space

Each node has four words: its key, its successor pointer and two children. The directory has one word per local tree, and one more word points to the fallback.

## Serving one request

**Theorem (query semantics).** Starting from the local tree of any key $p$, the executable query for any key $x$ is a legal request in the linked-search model, ending at $x$'s local tree, at the cost it reports.

@decl RotationBST.MultipleTrees.Results.query

[[RotationBST.LinkedSearch.request]] is the executable query and [[RotationBST.LinkedSearch.Request]] the relational semantics of [Chapter 11](linked-search.html); the theorem says they agree on this store, and that the cursor reaches $x$, so the next request can start from there.

**Theorem (worst case).** For $c \ge 1$, every request, whatever its frequency, costs at most $\log_2(2\min(c, n)) + \log_2(2n) + 4$.

@decl RotationBST.MultipleTrees.Results.uniform

This is the cost of a failed local search, the fallback link, a full search of the balanced fallback and the final successor link. It is the bound for transitions that the preprocessing never saw.

**Theorem (one transition).** If $1 \le c \le n$ and the transition $p \to x$ has $F_{px} > 0$, the request for $x$ from $p$ costs at most

$$6\,\Bigl(1 + \log_2 \frac{R_p}{F_{px}}\Bigr)\,\frac{1 + \log_2 n}{1 + \log_2 c}.$$

@decl RotationBST.MultipleTrees.Results.tradeoff

Here $R_p$ is [[RotationBST.ConditionalEntropy.rowTotal]]. The proof has two cases. On a hit, the cost is a weighted search in the local tree plus a link, $O(1 + \log_2(R_p/F_{px}))$, and the factor $(1 + \log_2 n)/(1 + \log_2 c)$ is at least $1$. On a miss, the cost is $O(1 + \log_2 n)$, but by the selection theorem $\log_2 c \le \log_2(R_p / F_{px})$, so $(1 + \log_2(R_p/F_{px}))/(1 + \log_2 c) \ge 1$. The constant $6$ covers both cases. The normalization by $1 + \log$ instead of $\log$ keeps the statement meaningful for $c = 1$ and for deterministic transitions, where $R_p = F_{px}$.

## The tradeoff

Summing the one-transition bound over the sequence gives Theorem 9. The store is built from the sequence's own transition matrix, so every transition actually performed has positive count. And the sum of $1 + \log_2(R_{x_{j-1}} / F_{x_{j-1} x_j})$ over all requests is $m + I(X)$, because the transition $a \to b$ occurs $F_{ab}$ times.

**Theorem 9 (space/query tradeoff).** Let $n \ge 1$, $1 \le c \le n$, $p < n$, and let $X$ be a sequence of keys less than $n$. The store built with capacity $c$ from the transition counts of $X$, starting from $p$, serves $X$ from $p$ at cost at most $6\,(m + I(X))\,(1 + \log_2 n)/(1 + \log_2 c)$, and uses at most $10nc$ words.

@decl RotationBST.MultipleTrees.Results.sequence

The sequence is a list of `Fin n`, so its validity is part of its type; `xs.map Fin.val` is the same list of natural numbers. The theorem asserts an execution of the store, with some final cursor `q` and cost `k`, not just a number: every request in it is a legal linked search.

Two capacities are worth spelling out. With $c = n$, every observed successor is stored, the store has $O(n^2)$ words and the cost is at most $6(m + I)$, within a constant of the benchmark. With $c = 1$, the store has $O(n)$ words and the cost is $O((m + I)\log n)$. In between, the factor is $(1 + \log_2 n)/(1 + \log_2 c) \approx \log_c n$.

**Theorem (polynomial space, Section 7).** Let $n \ge 1$ and $\varepsilon > 0$. There is a capacity $c$ with $1 \le c \le n$, depending only on $n$ and $\varepsilon$, such that for every start $p$ and every sequence $X$, the store built with capacity $c$ from the transition counts of $X$ serves $X$ from $p$ at cost at most $\frac{6}{\min(\varepsilon,1)}\, m\,(1 + H)$, and uses at most $20\, n^{1+\varepsilon}$ words.

@decl RotationBST.MultipleTrees.Results.polynomial_space

The proof takes the capacity $\lceil n^{\min(\varepsilon, 1)} \rceil$, so $\log_2 c \ge \min(\varepsilon, 1) \log_2 n$ and the ratio of logarithms is at most $1 / \min(\varepsilon, 1)$. The cap at $1$ reflects that a capacity of $n$ already stores every successor: for $\varepsilon > 1$, the space bound $20\,n^{1+\varepsilon}$ is valid but weaker than the $O(n^2)$ actually used. The cost is written with the average conditional entropy $H = I/m$, which [[RotationBST.ConditionalEntropy.entropy]] totalizes to $0$ for the empty sequence, so $m(1 + H) = m + I$.

::: check
- The capacity is chosen before the sequence is known, but the trees are not: they are built from the transition counts of $X$ itself, as in the paper. Both theorems are offline statements about a structure tuned to the sequence it serves, like the optimal static trees of [Chapter 29](optimal-lazy-finger.html).
- The cost counts node visits and pointer links in the linked-search model. Building the store is not counted, and the transition matrix is not part of the space.
- The benchmark is normalized as $m + I = m(1 + H)$, with one unit per request, so a deterministic sequence, with $H = 0$, still costs $\Theta(m)$.
:::
