# The optimal lazy-finger tree

A static binary search tree with a *lazy finger* serves each request by walking, along tree edges, from the previously requested key to the new one; the first search starts at the root. [Chapter 14](lazy-finger.html) introduced this model and its cost, and characterized the optimal cost up to constant factors. That characterization is not an algorithm. This chapter gives one: Theorem 8 of Bose, Douïeb, Iacono and Langerman computes an optimal lazy-finger tree exactly, by a dynamic program over key intervals that runs in cubic time once the request sequence has been summarized.

The library proves two things about this algorithm. It returns a tree whose lazy-finger cost equals the optimum over all shapes. And, in an explicit, annotated cost model for a random-access machine, its work is at most $4m + 64(n+1)^3$ for $m$ requests on $n$ keys.

```headline optimal-lazy-finger
title: An optimal lazy-finger tree can be computed with $4m + 64(n+1)^3$ work
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
key: yes
theorems: OptimalLazyFinger.Work.Results.root_start OptimalLazyFinger.Work.Results.specified_start

Let $X = x_1, \dots, x_m$ be a sequence of keys from $\{0, \dots, n-1\}$. A static BST $T$ on these keys serves $X$ with a lazy finger at cost

$$\mathrm{cost}_T(X) \;=\; \sum_{j=1}^{m} \bigl(1 + d_T(x_{j-1}, x_j)\bigr),$$

where $d_T(x, y)$ is the number of edges on the path between $x$ and $y$ in $T$, and $x_0$ is the root of $T$: one unit per request, plus the edges the finger walks. There is an explicit algorithm that, given $n$ and $X$, returns a tree $T^\ast$ with $n$ nodes such that

$$\mathrm{cost}_{T^\ast}(X) \;=\; \min_{T \text{ with } n \text{ nodes}} \mathrm{cost}_T(X),$$

and whose work, counted in an explicit unit-cost RAM model, is at most $4m + 64(n+1)^3$. The bound holds for every $n$, including $n = 0$, with no hidden constants. The same holds when the first search starts from a specified key $p < n$ instead of the root, that is, with $x_0 = p$.

In Lean, the algorithms are `Work.tree n xs` and `Work.treeFrom n p xs`, computations in the cost model [[OptimalLazyFinger.Work.Computation]]: `.ret` is the returned tree and `.time` the counted work. The costs are [[RotationBST.LazyFinger.cost]] and [[RotationBST.LazyFinger.costFrom]], and the optima [[RotationBST.LazyFinger.optimalCost]] and [[RotationBST.LazyFinger.optimalCostFrom]], defined as infima over all shapes with $n$ nodes; the theorems show that the returned tree attains them. The work is the sum of the charges declared in the model's program text, not a measurement of Lean's own running time.
```

To confirm the result, the box is enough, but its reading path is longer than usual: besides the lazy-finger cost of [Chapter 14](lazy-finger.html), it contains the whole annotated program, because a work bound is only as meaningful as the charges it adds up. [Section 29.7](#a-cost-model-for-the-work) and [Section 29.8](#the-counted-optimizer) explain what is charged and why. The rest of the chapter explains why the algorithm is correct. [Section 29.1](#the-plan) gives the plan. [Section 29.2](#boundary-tolls) rewrites the lazy-finger cost as a sum over subtrees, [Section 29.3](#bellman-s-recurrence) and [Section 29.4](#filling-the-table) solve the resulting interval problem, [Section 29.5](#counting-transitions) computes its inputs from the sequence, and [Section 29.6](#the-optimizer) assembles the optimizer and proves it exact. [Section 29.9](#the-work-bound) states the work theorems.

The definitions are in `Algorithms/OptimalLazyFinger/Definitions/Abstract.lean`, `Preprocessing/Definitions/Abstract.lean`, `Work/Model/Abstract.lean` and `Work/Definitions/Abstract.lean`; the theorems are in `Algorithms/OptimalLazyFinger/Abstract.lean` and `Work/Abstract.lean`.

## The plan

The optimal *root-finger* tree, where every search starts at the root, has a classical dynamic program: the cost of a tree is a sum, over its subtrees, of a quantity that depends only on the subtree's key interval, so the best tree on an interval is obtained by trying every root and combining the best trees on the two sides. The lazy-finger cost has the same structure, once it is written the right way.

1. **Edges as boundary crossings.** The edge from a subtree to its parent is walked exactly when the finger moves from a key inside the subtree to a key outside it, or back. So the walking part of the lazy-finger cost is the sum, over all subtrees, of the number of consecutive request pairs that cross the subtree's boundary. That number, the *boundary toll* of the subtree's key interval, depends on the interval only, not on the shape.
2. **Interval dynamic programming.** For any toll $w(lo, hi)$ on half-open intervals, the shape minimizing $\sum_{\text{subtrees}} w(\text{interval})$ satisfies Bellman's recurrence over intervals. A table indexed by interval length and start computes it with $O(n)$ choices for each of $O(n^2)$ intervals: $O(n^3)$.
3. **Tolls in constant time.** The toll of $[lo, hi)$ is a sum of the transition counts $F[a][b]$, the number of times the request sequence moves from key $a$ to key $b$, over four rectangles of the matrix $F$. After one pass over the sequence to fill $F$, in $O(m)$, and two-dimensional prefix sums, in $O(n^2)$, each toll costs four rectangle queries.
4. **Root start.** A virtual extra key $n$, outside every subtree, plays the previous request of $x_1$. It makes the first search cost one edge more than a walk from the root, whatever the shape, so it does not change which tree is optimal.

The library proves each step exactly, then annotates the same program with explicit operation counts and bounds their sum.

## Boundary tolls

The edge decomposition is part of [Chapter 14](lazy-finger.html). It uses the two definitions [[RotationBST.LazyFinger.cut]], which is $1$ when exactly one of two keys lies in a half-open interval $[lo, hi)$, and [[RotationBST.LazyFinger.crossings]], which sums `cut lo hi` over the consecutive pairs $(x_{j-1}, x_j)$ of a sequence with an explicit initial key $x_0$. The cost of a shape is then [[RotationBST.LazyFinger.intervalCost]]` w t lo`: the sum of $w(lo', hi')$ over the key intervals $[lo', hi')$ of all nonempty subtrees of `t`, including `t` itself, when `t`'s keys are numbered from `lo`.

Two theorems of that chapter connect this to the lazy-finger cost. For a specified start $p$ inside the tree, [[RotationBST.LazyFinger.Edges.Results.sequence]] says

$$\mathrm{costFrom}_T(p, X) \;=\; m + \mathrm{intervalCost}\bigl(\mathrm{crossings}(\cdot, \cdot, p, X),\, T\bigr).$$

The whole tree's interval contains every key, so its toll is $0$ and only proper subtrees, that is edges, contribute. For the root start, [[RotationBST.LazyFinger.Edges.Results.initialization]] takes the virtual initial key $n = |T|$, which lies outside every subtree. The first transition $n \to x_1$ then crosses the boundary of every subtree that contains $x_1$, which is $\mathrm{depth}(x_1) + 1$ subtrees, while the root-start search for $x_1$ walks $\mathrm{depth}(x_1)$ edges. So

$$\mathrm{cost}_T(X) + [X \neq \varepsilon] \;=\; m + \mathrm{intervalCost}\bigl(\mathrm{crossings}(\cdot, \cdot, n, X),\, T\bigr),$$

where $[X \ne \varepsilon]$ is $1$ for a nonempty sequence. In both cases, the lazy-finger cost and the interval cost differ by a quantity that does not depend on $T$. A shape minimizing one minimizes the other.

## Bellman's recurrence

The interval problem is: given a toll $w : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$, find a shape with $n$ nodes minimizing `intervalCost w t 0`. The definition of [[RotationBST.LazyFinger.intervalCost]] splits at the root: a tree `node l r` on keys starting at `lo` pays $w(lo, lo + |l| + |r| + 1)$ for its own interval, plus the interval cost of `l` on keys from `lo` and of `r` on keys from `lo + |l| + 1`. The two subproblems are independent, so, writing $\mathrm{OPT}(k, lo)$ for the optimum on the $k$ keys $lo, \dots, lo + k - 1$,

$$\mathrm{OPT}(0, lo) = 0, \qquad \mathrm{OPT}(k + 1, lo) \;=\; w(lo,\, lo + k + 1) + \min_{0 \le r \le k} \bigl(\mathrm{OPT}(r, lo) + \mathrm{OPT}(k - r,\, lo + r + 1)\bigr),$$

where $r$ is the number of keys in the left subtree, so the root is key $lo + r$.

@decl RotationBST.OptimalLazyFinger.Entry RotationBST.OptimalLazyFinger.choose RotationBST.OptimalLazyFinger.minimum

An `Entry` is a candidate solution: a shape together with its cost. `choose` keeps the cheaper of two entries and, on a tie, the first; `minimum initial candidates` folds `choose` from the right over the list, ending with `initial`. A fold needs a starting value, which is why `minimum` takes one; the optimizer passes the first candidate, which is also in the list, so it changes nothing. With this fold and tie rule, the earliest minimizing candidate in the list wins.

@decl RotationBST.OptimalLazyFinger.solve

`solve w n lo` is the recurrence verbatim, returning both the cost and a minimizing shape. Its arguments are the interval length `n` and the first key `lo`. Each candidate `k` builds the node whose left subtree is the solution on the first `k` keys and whose right subtree is the solution on the remaining `n - k`, and its cost is the toll of the whole interval plus the two sub-costs. The candidates are listed by increasing `k`, so ties go to the smallest left subtree. As its docstring says, `solve` is a specification: it recomputes shared subproblems and takes exponential time. Its role is to fix, once and for all, *which* optimal shape the efficient algorithm returns.

## Filling the table

The efficient evaluation stores every subproblem in a table with one row per interval length.

@decl RotationBST.OptimalLazyFinger.lookup RotationBST.OptimalLazyFinger.tabulate RotationBST.OptimalLazyFinger.optimize

`tabulate w univSize stages` builds rows $0, 1, \dots, \mathit{stages}$. Row $n$ has one entry for every start $lo \in \{0, \dots, \mathit{univSize}\}$; the entry is the solution on the interval $[lo, lo + n)$ if that interval fits in the universe, and the placeholder `(.nil, 0)` otherwise. Row $0$ is all empty trees. Row $n + 1$ is computed from the rows already built, by the same candidates as in `solve`, with `lookup` in place of the recursive calls. `lookup` is a total read: it returns `(.nil, 0)` outside the table, a value that the theorems never use. `optimize w n` builds the table for a universe of $n$ keys and reads the entry for the whole interval $[0, n)$.

**Theorem (cached recurrence).** For every toll $w$, every valid interval, of length $n$ at most the number of rows built and with $lo + n \le \mathit{univSize}$, the table entry is exactly the recursive solution, including the shape chosen among ties.

@decl RotationBST.OptimalLazyFinger.Results.cached_recurrence

**Theorem (the interval optimizer).** For every toll $w$ and every $n$, `optimize w n` returns a shape with $n$ nodes, its reported cost is the shape's interval cost, and no shape with $n$ nodes has a smaller interval cost.

@decl RotationBST.OptimalLazyFinger.Results.boundary_optimal

The toll is arbitrary here: any function of the interval endpoints. This is the general form of the classical optimal-BST recurrence. For instance, with $w(lo, hi)$ the total access frequency of the keys in $[lo, hi)$, each key is charged once for every subtree that contains it, that is, its depth plus one, and the optimizer computes an optimal root-finger tree.

## Counting transitions

The lazy-finger toll of an interval is the number of consecutive request pairs that cross its boundary. Computing it naively from the sequence costs $O(m)$ for each of the $O(n^2)$ intervals. Instead, the optimizer summarizes the sequence once, in the $n \times n$ matrix of directed transition counts $F[a][b] = \#\{j : x_{j-1} = a,\ x_j = b\}$, with the initial key as $x_0$. A pair crosses the boundary of $[lo, hi)$ exactly when one endpoint is inside and the other is outside, to the left or to the right, so

$$w(lo, hi) \;=\; F\bigl([lo,hi) \times [0,lo)\bigr) + F\bigl([lo,hi) \times [hi,n)\bigr) + F\bigl([0,lo) \times [lo,hi)\bigr) + F\bigl([hi,n) \times [lo,hi)\bigr),$$

where $F(A \times B)$ is the sum of the entries with row in $A$ and column in $B$. These are the moves from inside to the left, from inside to the right, from the left to inside, and from the right to inside. With two-dimensional prefix sums of $F$, each rectangle sum takes four table reads. The prefix-sum table and its rectangle query are in [Chapter 33](prefix-sums.html).

@decl RotationBST.OptimalLazyFinger.Preprocessing.Square RotationBST.OptimalLazyFinger.Preprocessing.increment RotationBST.OptimalLazyFinger.Preprocessing.fill RotationBST.OptimalLazyFinger.Preprocessing.frequencies

The matrix is a [[RotationBST.PrefixSum.Table]], an array of rows. `frequencies n p xs` starts from the $n \times n$ zero matrix and makes one pass over the sequence, incrementing entry $(x_{j-1}, x_j)$ for each request, starting from $x_0 = p$. `increment` uses `Array.modify`, which leaves the table unchanged at an index out of range. `Square t n` says that `t` has $n$ rows of length $n$; the proofs use it as the invariant of the pass.

**Theorem (transition counts).** For all keys $a, b < n$, entry $(a, b)$ of the accumulated matrix is the directed adjacent-pair count [[RotationBST.LazyFinger.frequency]]` p xs a b` of [Chapter 14](lazy-finger.html), which includes the pair $(p, x_1)$.

@decl RotationBST.OptimalLazyFinger.Results.pair_frequencies

No hypothesis on $p$ or on the requests is needed: pairs with an endpoint outside $\{0, \dots, n-1\}$ are never stored, and the theorem only reads entries inside the matrix.

@decl RotationBST.OptimalLazyFinger.Preprocessing.prepare RotationBST.OptimalLazyFinger.Preprocessing.toll

`prepare n p xs` replaces the counts by their two-dimensional prefix sums, a table of $(n + 1) \times (n + 1)$ entries. `toll` computes the four rectangle sums above with [[RotationBST.PrefixSum.rectangle]]. The argument `n` of `toll` is the universe size, which gives the outer edges of the rectangles.

**Theorem (prepared tolls).** If the initial key $p$ and all requests are less than $n$, then for every interval $[lo, hi)$ with $lo \le hi \le n$, the prepared toll is the number of boundary crossings [[RotationBST.LazyFinger.crossings]]` lo hi p xs`.

@decl RotationBST.OptimalLazyFinger.Results.prepared_boundary

## The optimizer

@decl RotationBST.OptimalLazyFinger.treeFrom RotationBST.OptimalLazyFinger.tree

`treeFrom n p xs` prepares the transition table on a universe of $n + 1$ keys, one more than the tree, and runs the interval optimizer on $n$ keys with the prepared tolls. The extra key $n$ never appears in a request. It is there for `tree n xs`, the root-start variant, which uses it as the virtual initial key of [Section 29.2](#boundary-tolls). For a specified start $p < n$, the extra key has no transitions and changes no toll.

**Theorem (specified start).** If $p < n$ and every request is less than $n$, then `treeFrom n p xs` has $n$ nodes, and its lazy-finger cost from $p$ is the optimum over all shapes with $n$ nodes.

@decl RotationBST.OptimalLazyFinger.Results.specified_start

**Theorem (root start).** If every request is less than $n$, then `tree n xs` has $n$ nodes, and its lazy-finger cost, with the first search from the root, is the optimum over all shapes with $n$ nodes.

@decl RotationBST.OptimalLazyFinger.Results.root_start

Both proofs combine the previous theorems. Within the interval $[0, n+1)$ the prepared tolls are the boundary crossings, so the interval cost the optimizer minimizes is the lazy-finger cost minus a constant, by the two identities of [Section 29.2](#boundary-tolls). Hence the returned tree is at most as costly as every shape of size $n$, in particular as a shape attaining the infimum, which exists by [[RotationBST.LazyFinger.Results.optimal_attained]] and [[RotationBST.LazyFinger.Results.optimal_from_attained]].

::: check
- The optimum is over shapes with exactly $n$ nodes, the keys $0, \dots, n-1$, and both costs charge one unit per request, as everywhere in [Chapter 14](lazy-finger.html). The equality is exact: no additive or multiplicative slack.
- The root start is the paper's model. The theorem covers $n = 0$, where the only valid sequence is empty, and repeated requests, which cost one unit each.
- The cost that `optimize` reports alongside the tree is the interval cost, not the lazy-finger cost; the two differ by $m$, or by $m - 1$ for the root start on a nonempty sequence. The theorems only use the tree.
:::

## A cost model for the work

Lean definitions have no running time of their own. A statement such as "the optimizer runs in $O(m + n^3)$ time" needs a model of computation, and the library makes it explicit: the counted optimizer is a second program, written in a monad that pairs each value with a natural-number count of the operations spent computing it.

@decl RotationBST.OptimalLazyFinger.Work.Computation RotationBST.OptimalLazyFinger.Work.charge

`Computation α` is `TimeM Nat α` from the CSLib library: a value `ret` together with a count `time`. Sequencing two computations adds their counts, and `pure` costs nothing. Counts are introduced only by `charge steps value`, which returns `value` at a cost of `steps`. The model is a unit-cost random-access machine:

- a scalar addition, subtraction or comparison, an indexed array read or update, an amortized array append, and the allocation of a tree node each cost one;
- values are mathematical natural numbers, each held in one machine word, so this is not a bit-complexity bound;
- loops are counted recursions, and every step of a list traversal is charged.

@decl RotationBST.OptimalLazyFinger.Work.mapList RotationBST.OptimalLazyFinger.Work.arrayOfFn RotationBST.OptimalLazyFinger.Work.replicate

These are the counted versions of the library primitives the optimizer uses. `mapList f` charges one unit per list cell, plus the counts of the callbacks. `arrayOfFn n f` charges $n + 1$ to enumerate the indices, then the callbacks and the traversal through `mapList`, then $n + 1$ to turn the list into an array. `replicate n value` charges $n + 1$ to allocate and initialize an array of length $n$.

::: caveat
The charges are part of the model: they are written by hand in the program text, and the theorems bound their sum. Two things are proved about them. First, the counted program computes the same tree as the verified one (`same_tree`, in [Section 29.9](#the-work-bound)), so the counts describe the right computation. Second, the sum of the charges satisfies the stated bound. Whether each charge is a fair price for its operation is a judgement about the model, which the reader checks by reading the definitions in this section and the next. The theorems say nothing about the running time of the compiled Lean code. For example, Lean's arrays are persistent, and an update that is charged one unit here may copy the array if it is shared.
:::

## The counted optimizer

The counted program mirrors the definitions of [Section 29.3](#bellman-s-recurrence) to [Section 29.6](#the-optimizer) step by step, with a charge on each primitive. It is a separate definition, so that the verified algorithm stays free of annotations.

@decl RotationBST.OptimalLazyFinger.Work.matrixGet RotationBST.OptimalLazyFinger.Work.increment RotationBST.OptimalLazyFinger.Work.fill RotationBST.OptimalLazyFinger.Work.frequencies

**Accumulating transitions.** A matrix read is two indexed reads, one per level of the array of rows. An increment is two indexed updates and an addition. The pass over the requests charges one more step per request for the traversal, so it costs $4m + 1$ in all; this is the $4m$ of the bound. Allocating the zero matrix costs $O(n^2)$.

@decl RotationBST.OptimalLazyFinger.Work.row RotationBST.OptimalLazyFinger.Work.build RotationBST.OptimalLazyFinger.Work.prepare

**Prefix sums.** `row` computes the prefix sums of one row, charging $4$ per entry for the read of the previous prefix, the addition and the append, plus the reads of the input. `build` adds each row's prefixes to those of the previous row, at $4$ per entry plus the array construction. Here the input entries are themselves counted matrix reads: `prepare` passes `matrixGet` of the transition matrix.

@decl RotationBST.OptimalLazyFinger.Work.rectangle RotationBST.OptimalLazyFinger.Work.toll

**Tolls.** A rectangle query is four two-level reads and three arithmetic operations, $11$ units; a toll is four rectangle queries and three additions, $47$ units, whatever the interval.

@decl RotationBST.OptimalLazyFinger.Work.minimum RotationBST.OptimalLazyFinger.Work.candidate RotationBST.OptimalLazyFinger.Work.cell RotationBST.OptimalLazyFinger.Work.tabulate RotationBST.OptimalLazyFinger.Work.optimize

**The table.** The counted `minimum` charges a comparison and a step per candidate. `candidate` computes the toll, which may itself be a counted computation, and charges $12$ for the index arithmetic, the two table lookups, the two additions and the allocation of one tree node. The node shares its two subtrees with the table, as a pointer machine would, so building a candidate tree costs one allocation, not a copy. `cell` charges $3$ to test whether the interval fits in the universe. A valid cell evaluates the first candidate as the fold's initial value, enumerates the $n+1$ root choices, evaluates each candidate and folds. An invalid cell stops after the test. `tabulate` and `optimize` mirror their uncounted versions. Every row has $N + 1$ cells, so there are $O(N^2)$ cells, each with $O(N)$ candidates at constant cost: the $64(n+1)^3$ of the bound.

@decl RotationBST.OptimalLazyFinger.Work.treeFrom RotationBST.OptimalLazyFinger.Work.tree

`Work.treeFrom` and `Work.tree` are the whole counted optimizer, including the preprocessing on $n + 1$ keys and the virtual initial key. Their `time` is the end-to-end work.

## The work bound

**Theorem (erasure).** Forgetting the counts, the counted optimizer returns exactly the tree of the verified optimizer, for every input.

@decl RotationBST.OptimalLazyFinger.Work.Results.same_tree

**Theorem (preprocessing).** Accumulating the transitions and computing the prefix sums on a universe of $n$ keys costs at most $4m + 14n^2 + 18n + 7$.

@decl RotationBST.OptimalLazyFinger.Work.Results.preprocessing

The optimizer calls the preprocessing on $n + 1$ keys, with the virtual key. No hypothesis on the requests is needed: the counts do not depend on the values of the requests, only on their number.

**Theorem 8 (exact optimizer, root start).** If every request is less than $n$, the counted root-start optimizer returns a tree with $n$ nodes, its lazy-finger cost is the optimum over all shapes with $n$ nodes, and its work is at most $4m + 64(n+1)^3$.

@decl RotationBST.OptimalLazyFinger.Work.Results.root_start

**Theorem (specified start).** If $p < n$ and every request is less than $n$, the counted optimizer from $p$ returns a tree with $n$ nodes whose lazy-finger cost from $p$ is optimal, with work at most $4m + 64(n+1)^3$.

@decl RotationBST.OptimalLazyFinger.Work.Results.specified_start

The correctness parts are the theorems of [Section 29.6](#the-optimizer), transported through the erasure theorem. The work part adds the preprocessing bound to the cost of the table: $n$ rows of $n + 1$ cells, each evaluating at most $n + 2$ candidates (the $n + 1$ root choices and the fold's initial value) at $47 + 12$ units each, plus constant overhead.

**Theorem (the usual form).** On a nonempty universe, the work is at most $4m + 512\,n^3$, that is, $O(m + n^3)$.

@decl RotationBST.OptimalLazyFinger.Work.Results.nonempty_bound

This is the previous bound with $(n+1)^3 \le 8n^3$ for $n \ge 1$. Like the preprocessing bound, it holds for every input, valid or not.

::: note Where the cubic term comes from
The table evaluates every pair (length, start), $(N + 1)^2$ cells per stage, although only about half of them are valid intervals, and the invalid ones cost only their validity test. The constant $64$ is therefore not tight; the bound is meant to be simple, explicit and end-to-end, including preprocessing, initialization and the empty universe.
:::
