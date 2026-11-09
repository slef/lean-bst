# Beyond single accesses

The theorems of [Chapter 14](analysis.html) are about one algorithm serving accesses to a fixed set of keys. Splay trees do more. Sleator and Tarjan show that insertion, deletion, split and join also cost $O(\log n)$ amortized, so a splay tree is a complete dictionary with the same guarantee. Their paper also analyses a variant that splays only along long paths, and the expected shape of the tree under random requests (the *snapshot*). Tarjan [-@tarjan1985] later proved the *scanning theorem*: accessing every key once, in increasing order, costs $O(n)$ from any initial tree. The library proves versions of all four. The two headline results are the dictionary bound and the scanning theorem:

```headline splay-updates
title: Splay trees support updates in $O(\log n)$ amortized time
source: @sleator1985
key: yes
theorems: Splay.Updates.Results.balance

Consider any sequence of $m$ operations on a collection of splay trees (a *forest*). Each operation is an access, an insertion, a deletion, a split of one tree into two, or a join of two trees, and is charged one unit plus its rotations. Suppose the forest never holds more than $N$ keys, and initially holds $s$ keys. Then the total cost is at most

$$m\,\bigl(5\log_2(N+1) + 3\bigr) + s\log_2(s+1).$$

In Lean, the operations are [[RotationBST.Splay.Updates.split]], [[RotationBST.Splay.Updates.join]], [[RotationBST.Splay.Updates.insert]] and [[RotationBST.Splay.Updates.delete]], built on [[RotationBST.Splay.run]]. A run of operations is an [[RotationBST.Splay.Updates.Execution]] made of [[RotationBST.Splay.Updates.Step]]s, and `balance` is the bound. Insertions and deletions name their position by rank; the search that finds that rank from a key is not modelled ([Section 15.1](beyond.html#updates)).
```

```headline splay-scanning
title: Sequential access in splay trees takes linear time
source: @tarjan1985
key: yes
theorems: Splay.Results.scanning

For every initial tree on $n$ keys, accessing the keys $0, 1, \dots, n-1$ in increasing order by splaying costs at most $14n$ in total, counting one unit per request plus one per rotation. The first access alone may take $n-1$ rotations, so the bound is about the whole scan, not about each access.

In Lean, the scan is `List.range t.size`, and `scanning` bounds `totalCost` of [[RotationBST.Splay.algorithm]].
```

Each of these results comes with modelling choices that are easy to misread, so this section spends more time on the definitions than on the bounds.

## Updates

### The four operations on shapes

Updates change the key set, so ranks must change too. The library keeps the shape view: every tree uses its own inorder ranks $0, \dots, n-1$, and an operation's effect on keys is a statement about how ranks are renumbered. A *gap* $k \in \{0, \dots, n\}$ is the position between ranks $k-1$ and $k$, as in [Chapter 1](shapes.html#implicit-keys).

@decl RotationBST.Splay.Updates.SplitResult RotationBST.Splay.Updates.split

`split t k` cuts `t` into the first `k` keys and the rest. For `k = 0` there is nothing to do: the left part is empty and the cost is zero. Otherwise it splays the predecessor of the gap, rank $k-1$, to the root, and cuts the edge to its right child. The root, with its left subtree, becomes the left tree, and the former right subtree becomes the right tree. Both keep their local ranks, so key $k$ of `t` becomes rank $0$ of the right tree. The `.nil` branch of the `match` is unreachable for valid gaps, since splaying an existing rank never yields an empty tree. It only makes the function total.

@decl RotationBST.Splay.Updates.join

`join l r` concatenates two key sets, all of `l` before all of `r`. On shapes this needs no hypothesis: the joined tree's inorder is `l`'s keys followed by `r`'s, by construction. It splays the maximum of `l`, rank `l.size - 1`, which leaves a root with an empty right subtree, and hangs `r` there. The pattern `.node a _` discards that right subtree, which is `.nil` after splaying the maximum (`Updates.run_max` proves this).

@decl RotationBST.Splay.Updates.insert RotationBST.Splay.Updates.delete

`insert t k` puts a new key into gap `k`: split there and make the new key the root over the two halves. Its rank is `k`, and every old rank at or after `k` increases by one. `delete t x` splays `x`, removes the root, and joins its subtrees, so every rank after `x` decreases by one. The counts returned are rotations only. The unit charge for the operation itself is added by the execution model below.

::: check
- The insertion position is a *rank* supplied by the caller. Finding that rank from a new comparison key, by searching for it, is not formalized. Neither is a pointer machine with node allocation; the README lists both as remaining work.
- Out-of-range arguments (`k > t.size` for `split`, `x ≥ t.size` for `delete`) are outside every theorem below, which all assume validity.
:::

The size lemmas confirm the renumbering.

**Theorem (sizes).** For valid arguments on a tree with $n$ keys, splitting at gap $k$ gives trees with $k$ and $n - k$ keys, joining gives $|l| + |r|$ keys, insertion adds one key and deletion removes one. A split at $k > 0$ is a certified splay access to rank $k - 1$, followed by cutting the root's right edge (`split_spec`).

@decl RotationBST.Splay.Updates.Results.split_sizes RotationBST.Splay.Updates.Results.split_spec RotationBST.Splay.Updates.Results.join_size RotationBST.Splay.Updates.Results.insert_size RotationBST.Splay.Updates.Results.delete_size

### Forests and charged operations

Splits create several trees and joins consume them, so the state of an execution is a list of trees, a *forest*.

@decl RotationBST.Splay.Updates.forestSize RotationBST.Splay.Updates.Step

`Step s t c n` is one successful operation: forest `s` becomes forest `t` at cost `c`, and `n` is the number of keys taking part. The five operation constructors act on a forest with exactly the involved trees. The cost is always the rotation count plus one, and `n` is the size of the involved tree, or `l.size + r.size` for a join. Validity hypotheses are part of the constructors: `k ≤ t.size` for insert and split, `x < t.size` for access and delete.

The last two constructors are structural:

- `frame` carries an unrelated tree `a` along unchanged, without changing the cost or `n`. Repeated use lets an operation act on any trees of a larger forest while the rest is untouched, and those untouched trees contribute nothing to `n`.
- `rearrange` lets the forest be permuted before and after an operation, for free. The list is just a collection of tree handles; its order means nothing.

`join` takes the first two trees *in that order*: the left one's keys come first. Combined with `rearrange`, any two trees can be joined in either order, which is legitimate because each tree has its own local ranks. Nothing in the model records a global key universe. Joining two trees means only that one key set is declared to precede the other.

@decl RotationBST.Splay.Updates.Execution RotationBST.Splay.Updates.LocalExecution

`Execution N s m t c` is a sequence of `m` operations with total cost `c`, during which the forest never holds more than `N` keys. The `bound` hypothesis is checked at every boundary, including the final forest. `LocalExecution s ns t c` drops the global bound and instead records the list `ns` of participating key counts, one per operation.

### Balance with updates

**Theorem (balance with updates).** Consider an execution of $m$ operations during which the forest never holds more than $N$ keys, starting from a forest with $s$ keys in total. Its total cost is at most $m\,(5\log_2(N+1) + 3) + s\log_2(s+1)$. If the forest starts empty, the total cost is at most $\sum_j \bigl(5\log_2(n_j + 1) + 3\bigr)$, where $n_j$ is the number of keys in the trees that operation $j$ involves.

@decl RotationBST.Splay.Updates.Results.balance RotationBST.Splay.Updates.Results.balance_initially_empty

The first theorem is the analogue of the balance theorem for arbitrary initial forests, with a startup term for the initial forest. The second is the paper's version, in which an operation pays only for the keys of the trees it touches: a small tree is cheap to operate on even when the forest is large.

::: details Proof sketch
The potential is the unit-weight splay potential ([Chapter 9](analysis.html)), summed over the trees of the forest; permuting the forest leaves it unchanged. Each operation is bounded separately using the access lemma with unit weights, i.e. $R + \Delta\Phi \le 3\log_2 n + 1$:
splitting adds nothing beyond the access, because cutting the root's right edge only lowers the root's subtree size.
Joining is an access to the maximum of $l$, after which the root's rank grows from $\log_2|l|$ to $\log_2(|l|+|r|)$, giving $3\log_2(|l|+|r|)+1$ in total.
Insertion is a split plus a new root, giving $4\log_2(n+1)+1$.
Deletion is an access plus a join, giving $5\log_2 n + 2$. With the unit charge, every case is at most $5\log_2(n+1)+3$. The initial potential is at most $|s|\log_2(|s|+1)$ and the final potential is nonnegative. See `Algorithms/Splay/Updates/Potential.lean` and `Balance.lean`.
:::

@viz updates {}

## Long splays

Section 5 of the paper considers splaying less often. A conditional splay searches for $x$ as usual, but restructures only if the search path is long. The library fixes positive weights $w$ and the threshold that makes the access lemma pay for itself:

@decl RotationBST.Splay.conditionalStep RotationBST.Splay.conditionalRun

`conditionalStep w t x` splays exactly when the depth of `x`, which is `(run t x).2` ([Chapter 8](splay.html)), is at least $6(\log_2 W - \log_2 w(x)) + 2$, twice the amortized bound of the access lemma, with $W$ = `mass w t 0`. Otherwise it returns the tree unchanged at cost zero. `conditionalRun` sums these costs over a request sequence.

::: check
- The weights are part of the *algorithm* here, unlike everywhere else in this chapter, where they are ghost data of the analysis. Comparing reals is not computable, so the definition is `noncomputable` and decides the threshold classically.
- $W$ is the total weight of the current tree. Weights are indexed by rank and rotations preserve ranks, so $W$ is the same for every tree reached.
- The returned number counts **restructuring rotations only**. A short search that does not splay still walks to $x$; it is not a zero-cost root access, and the conditional variant is not an [[RotationBST.Algorithm]] in the sense of [Chapter 6](online.html), because the tree it leaves need not have $x$ at the root. Its search cost is accounted for separately in the pointer model: `Splay.conditionalStep_pointer` shows that each conditional step is served by a pointer search of cost at most $1 + 3 \cdot \text{depth}$.
:::

**Theorem (long splays).** Fix positive weights $w$, and let $W$ be the total weight of the $n$ keys. For every initial tree and every sequence of valid requests, conditional splaying performs at most $2\sum_{i<n} \log_2(W/w(i))$ restructuring rotations in total. With unit weights, this is at most $2n\log_2 n$.

@decl RotationBST.Splay.Results.long_splay RotationBST.Splay.Results.long_splay_unit

The bound is independent of the length of `xs`: once the tree is shaped so that every key is shallow relative to its weight, conditional splaying stops restructuring altogether. It says nothing about the total search cost, which still grows with the number of requests.

::: details Proof sketch
When a splay is performed, the depth $R$ is at least twice the access lemma's charge $3(\log_2 W - \log_2 w(x)) + 1$, so $R + \Delta\Phi \le R/2$, i.e. $R \le 2(\Phi_{\text{before}} - \Phi_{\text{after}})$. When no splay happens, both sides are zero. Summing telescopes to $2(\Phi_0 - \Phi_{\text{final}})$. Every subtree's mass lies between the weight of its root and $W$, so the total drop is at most $\sum_i (\log_2 W - \log_2 w(i))$.
:::

## The snapshot theorem

Suppose requests are independent and key $x$ is requested with probability $p(x)$. Stop the splay tree at a random moment and freeze it as a static search tree. The snapshot theorem says that the frozen tree is, in expectation, nearly entropy-optimal. The library models this with explicit finite sums, without measure theory:

@decl RotationBST.Splay.meanSearch RotationBST.Splay.snapshotAt RotationBST.Splay.snapshotMean RotationBST.Splay.probabilityEntropy

- `meanSearch n p t` is the expected cost of one static search in `t`: one unit for the request plus the depth of the requested key. It uses `(run t x).2`, the splay rotation count, which equals the depth ([Chapter 8](splay.html)). The leading `1` is the expectation of one unit only when the probabilities sum to one, which the theorem assumes.
- `snapshotAt n p t j` is the expected `meanSearch` of the tree after `j` independent splay accesses from `t`. The recursion conditions on the first request: with probability `p x` it is `x`, and the remaining `j` accesses start from `(run t x).1`. This is the expectation over all $n^j$ request sequences, written as an iterated finite sum.
- `snapshotMean n p t m` averages `snapshotAt` over $j = 0, \dots, m-1$. The stopping time is uniform: the snapshot is taken just before one of the first `m` accesses, each with probability $1/m$.
- `probabilityEntropy` is Shannon entropy in bits.

::: check
Two division-by-zero conventions matter here. In Lean, $1/0 = 0$ and Mathlib's $\log_2 0 = 0$. So a zero-probability key contributes $0 \cdot \log_2(1/0) = 0$ to the entropy, the usual convention $0 \log 0 = 0$. And `snapshotMean … 0` would be $0/0 = 0$; the theorem excludes this with `0 < m`. Probabilities are only read at ranks below `n`; values of `p` beyond the tree are irrelevant except for the hypothesis `nonnegative`, which quantifies over all indices.
:::

**Theorem (snapshot).** Let $p$ be a probability distribution on the $n$ keys of a tree $t$, and let $m > 0$. Starting from $t$, perform independent splay accesses drawn from $p$, and freeze the tree just before one of the first $m$ accesses, chosen uniformly at random. In the frozen tree, the expected cost of one static search drawn from $p$ is at most $5 + 3H(p) + n(1 + \log_2 n)/m$, where $H(p)$ is the entropy of $p$ in bits.

@decl RotationBST.Splay.Results.snapshot

The last term is the cost of an arbitrary starting tree, amortized over the window of `m` accesses. Keys of probability zero are allowed. The statement's reading base contains no potential function: only the model, the splay algorithm and the finite-sum definitions above.

::: details Proof sketch
The analysis uses the weights $w(x) = p(x) + 1/n$, which are positive even where $p$ vanishes, and total $W = 2$. Averaging the weighted access lemma over one random request gives
$\mathbb E[\text{depth} + 1] + \mathbb E[\Phi'] \le 2 + 3\sum_x p(x)(\log_2 W - \log_2 w(x)) + \Phi$.
Iterating this over $j < m$ telescopes the potential, which lies between $n\log_2(1/n)$ and $n \log_2 W = n$. This gives the $n(1+\log_2 n)/m$ term. Finally $w(x) \ge p(x)$, so $\sum_x p(x)(1 - \log_2 w(x)) \le 1 + H(p)$, and $2 + 3(1 + H) = 5 + 3H$. See `Algorithms/Splay/Snapshot.lean`.
:::

## Sequential access

Accessing $0, 1, \dots, n-1$ in order costs $O(n)$ by the scanning theorem, from *any* initial shape. The statement uses only the splay algorithm and the cost of [Chapter 6](online.html):

**Theorem (sequential access).** For every initial tree on $n$ keys, accessing the keys $0, 1, \dots, n-1$ in order by splaying has total cost at most $14n$. On the pointer machine of [Chapter 6](pointer.html), the same scan, ending in exactly the splay tree, costs at most $40n$.

@decl RotationBST.Splay.Results.scanning RotationBST.Splay.Results.pointer_scanning

The scan `List.range t.size` is every key once, in increasing order. The constants are deliberately generous. The README notes that the sharper $5.5n$ of Kakimura and Terai [-@kakimura2026] is not claimed.

### The ghost marking

The proof needs bookkeeping that the algorithm never sees. During the scan, each tree has a simple global form: the current root (the last key accessed), with everything before it on its left, and a *right spine* of not-yet-accessed nodes. Each spine node has a left subtree that is partly restructured. The analysis marks those left subtrees:

@decl RotationBST.Splay.Scanning.Marked RotationBST.Splay.Scanning.Marked.tree RotationBST.Splay.Scanning.Marked.rank RotationBST.Splay.Scanning.Marked.Valid

A `Marked` value is a tree in which a top part of red nodes (`node`) has been touched, and everything below the red part is an untouched subtree (`hole`). `tree` forgets the marks. `rank` is the number of red nodes on the right spine of a marked tree. `Valid` requires, at every red node, that the left child's rank is at most the right child's plus one.

@decl RotationBST.Splay.Scanning.Marked.alpha RotationBST.Splay.Scanning.Marked.credit RotationBST.Splay.Scanning.Marked.potential

The potential gives each red node a credit $h^2 + 2\alpha(g-h)$, where $h$ is its left child's rank and $g$ its own rank. The correction $\alpha(v)$ is $5$ for $v = 0$ and $3 - v$ otherwise; Lean's truncated subtraction makes it $2, 1, 0, 0, \dots$ for $v = 1, 2, 3, \dots$. A hole holding $s$ untouched nodes carries $18s$: a prepaid budget for marking those nodes red when the scan first reaches them. The docstring describes the total as *twice* the red-node potential plus this budget. The analysis doubles it so that every quantity stays a natural number, and the proof bounds $2R$.

::: details Proof sketch
Accessing rank 0 first costs fewer than $n$ rotations ([[RotationBST.Splay.Results.correct]]) and leaves a root with an empty left subtree. From then on, the next key is always the minimum of the right subtree. If the first spine node has an empty left subtree, the access is one rotation. Otherwise the left spine of that left subtree is painted red, paid from the hole budget. The red ancestors of the minimum are then consumed in pairs, which are the zig-zig steps, and the last one or two steps involve the spine node and the old root (`consume_splay` proves that this ghost pairing has exactly the shape `splayAt` produces). Each access satisfies $2k + \Phi' \le \Phi + 6$. Each middle pair pays for its two rotations out of the quadratic credit, by the arithmetic lemma `pair_credit`. Summing over the remaining $n-1$ accesses, starting from an initial potential of at most $18n$, gives at most $12n$ rotations after the first access, hence $R \le 13n$ and $m + R \le 14n$. The pointer bound is $m + 3R \le n + 39n$. See `Algorithms/Splay/Scanning/`.
:::

::: check
None of `Marked`, `rank`, `credit` or `potential` appears in the statement of `scanning`. Its reading base, checked by `#check_bst_abstract`, lists only the model, online algorithms, the pointer machine and the splay algorithm. To trust the theorem you do not need to understand the potential at all; it lives entirely in the proof.
:::

@viz experiment {"theorem": "scanning", "n": 63, "shape": "left-path"}

The figure scans all keys from a chosen starting shape and plots the cumulative total cost against $14n$. Starting from a left path, the first access alone costs $n-1$ rotations, but the rest of the scan is cheap.
