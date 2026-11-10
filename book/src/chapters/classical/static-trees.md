# Static search trees

A static tree never changes. It is built once, and then serves every request by an ordinary search from the root. Serving key $x$ costs one unit plus the depth of $x$: this is [[StaticTree.cost]], and [Chapter 13](bounds.html#comparison-with-a-fixed-tree) shows that it is exactly the cost of a pointer-machine execution that never rotates.

A static tree can know two things in advance: the number of keys, or how often each key will be requested. The first gives the balanced tree, which has the best possible worst-case guarantee. The second gives entropy trees and optimal trees, which are the benchmark behind static optimality. The two headline results are the worst-case baseline and the optimal tree:

```headline static-baseline
title: A balanced tree pays at most $1 + \lfloor\log_2 n\rfloor$ per search, and no static tree does better in the worst case
theorems: Classical.Static.Results.balanced_cost Classical.Static.Results.exists_expensive

The balanced tree on $n$ keys serves every sequence of $m$ searches at cost at most $m(1 + \lfloor\log_2 n\rfloor)$, counting one unit per search plus the depth of the requested key. Conversely, every tree on $n \ge 1$ keys has a key $x$ such that searching $x$ $m$ times costs at least $m(1 + \lfloor\log_2 n\rfloor)$.

In Lean, the balanced tree is [[RotationBST.Tree.balanced]] and the cost is [[RotationBST.StaticTree.cost]]. The repeated sequence is `List.replicate m x`.
```

```headline static-optimal
title: The cost of an optimal static tree can be computed in $O(n^2)$ steps
source: @knuth1971; @yao1980
theorems: Classical.Static.Optimal.Results.optTree_static Classical.Static.Optimal.Results.optCost_le_static Classical.Static.Optimal.Results.knuth_optCost Classical.Static.Optimal.Results.knuth_steps_le

For every sequence $X$ of requests to $n$ keys, the dynamic program builds a tree on the $n$ keys whose search cost for $X$ is at most that of every other tree on the same keys. Knuth's algorithm computes this optimal cost while examining at most $2n^2$ candidate roots; the library proves that it returns the cost, not that a tree built from its root table is optimal.

In Lean, the weights are the request counts [[RotationBST.Classical.Static.counts]], the optimal tree and cost are [[RotationBST.Classical.Static.optTree]] and [[RotationBST.Classical.Static.optCost]], and Knuth's algorithm is [[RotationBST.Classical.Static.Optimal.knuth]], which returns the cost and the number of roots it examined.
```

## Balanced trees

The library builds one balanced tree for every number of keys. The root takes the middle rank, and the larger half goes to the left:

@decl RotationBST.Tree.balanced

`termination_by n => n` tells Lean that the recursion terminates because both halves, `(n + 1) / 2` and `n / 2`, are smaller than `n + 1`. The two subtree sizes differ by at most one. When $n = 2^h - 1$ the balanced tree is the perfect tree [[Tango.perfect]] with $h$ levels, as one can check by unfolding the definitions (no theorem states it); Tango uses both as reference trees ([Section 25.1](preferred-paths.html)).

**Theorem (balanced trees).** The balanced tree on $n$ keys has $n$ keys, and every key lies at depth at most $\lfloor\log_2 n\rfloor$. For $n \ge 1$ its height, in nodes, is exactly $\lfloor\log_2 n\rfloor + 1$.

@decl RotationBST.Classical.Static.Results.balanced_size RotationBST.Classical.Static.Results.balanced_depth RotationBST.Classical.Static.Results.balanced_height_eq

No tree does better. A tree whose height is $h$ nodes holds at most $2^h - 1$ keys, so:

**Theorem (minimum height).** Every tree on $n \ge 1$ keys has height at least $\lfloor\log_2 n\rfloor + 1$, and a key at depth at least $\lfloor\log_2 n\rfloor$.

@decl RotationBST.Classical.Static.Results.log2_add_one_le_height RotationBST.Classical.Static.Results.exists_deep

Searching costs one plus the depth, which gives the two halves of the headline result, and the comparison with the logarithmic baseline [[Bounds.logCost]] of [Chapter 13](bounds.html#the-logarithmic-baseline):

**Theorem (the baseline).** Searching the balanced tree costs at most $m(1 + \lfloor\log_2 n\rfloor)$, hence at most $m(1 + \log_2 n)$. Every nonempty tree has a key whose $m$-fold repetition costs at least $m(1 + \lfloor\log_2 n\rfloor)$.

@decl RotationBST.Classical.Static.Results.balanced_cost RotationBST.Classical.Static.Results.balanced_cost_le_logCost RotationBST.Classical.Static.Results.exists_expensive

## Entropy trees

Suppose that key $x$ is requested $q_x$ times among $m$ requests. A tree in which $x$ has depth about $\log_2(m / q_x)$ serves the requests at cost about the entropy bound [[Bounds.staticCost]]. Both directions are formalized ([Chapter 13](bounds.html#comparison-with-a-fixed-tree)):

- **Lower bound.** Every static tree costs at least a third of the entropy bound ([[StaticTree.Results.entropy_lower_bound]]).
- **Upper bound.** Some static tree costs at most the entropy bound ([[StaticTree.Results.entropy_upper_bound]]).

The tree of the upper bound is built by a rule close to that of @mehlhorn1975: put the weighted median at the root and recurse on both sides. This is the weighted search tree of [Chapter 33](prefix-sums.html#weighted-search-trees), where every key of weight $w_x$ lands at depth at most $\log_2(W/w_x)$. With weights on the keys only, the library's bound is already the entropy plus one unit per request, with no constant factor. Mehlhorn's analyses [@mehlhorn1975; @mehlhorn1977] also allow weights on the gaps between keys, for unsuccessful searches; they are not formalized.

## Optimal static trees

The entropy tree is within a constant factor of the best static tree. The best static tree itself can be computed exactly, by dynamic programming over intervals of keys. The library writes intervals half-open: $[i, j)$ holds the keys $i \le x < j$. Let $W(i, j)$ be the weight of the interval. A tree on $[i, j)$ puts some key $r$ at its root, and every search in the interval passes through the root. So the cheapest tree uses the cheapest trees on both sides:

$$C(i, j) \;=\; W(i, j) + \min_{i \le r < j} \bigl( C(i, r) + C(r + 1, j) \bigr), \qquad C(i, i) = 0 .$$

Computed directly this takes $O(n^3)$ time; @gilbert1959 used the same recurrence when only the gaps carry weight. @knuth1971 observed that the optimal roots are monotone: some optimal root of $[i, j)$ lies between optimal roots of $[i, j - 1)$ and of $[i + 1, j)$. Restricting the minimum to that window makes the total work $O(n^2)$. @yao1980 explained why: whenever the weight satisfies the *quadrangle inequality* and is monotone on nested intervals, the cost $C$ satisfies the quadrangle inequality too, and that makes the optimal roots monotone.

The library follows Yao. Everything is stated for an abstract interval weight `W`, and key weights are one instance. Weights on the gaps between keys, for unsuccessful searches, would be another additive instance; it is not stated separately, because in the models of this book every request is a key.

### The recurrence

@decl RotationBST.Classical.Static.Optimal.cost RotationBST.Classical.Static.Optimal.candidate RotationBST.Classical.Static.Optimal.root RotationBST.Classical.Static.Optimal.tree

`cost W i j` is the recurrence, with the minimum written as a fold over the roots `i + r` for `r < j - i`. `root W i j` is Knuth's $R(i, j)$, the *largest* optimal root, found by `Nat.findGreatest`; any consistent choice would do, and the largest one makes the monotonicity statements below hold as written. `tree W i j` builds the tree from these roots.

The cost of an arbitrary tree is the weight of the interval of every subtree, summed over all subtrees. This is [[LazyFinger.intervalCost]] of [Chapter 14](lazy-finger.html), the same sum that the optimal lazy-finger tree uses. With key weights it is the weighted depth $\sum_x w_x(\mathrm{depth}(x) + 1)$, as shown below.

**Theorem (the recurrence is optimal).** `tree W i j` has the $j - i$ keys of the interval, its cost is `cost W i j`, and no tree on those keys costs less.

@decl RotationBST.Classical.Static.Optimal.Results.tree_size RotationBST.Classical.Static.Optimal.Results.tree_cost RotationBST.Classical.Static.Optimal.Results.cost_le_intervalCost

### Yao's quadrangle inequality

@decl RotationBST.Classical.Static.Optimal.Quadrangle RotationBST.Classical.Static.Optimal.InclusionMonotone

**Theorem (Yao; Knuth's inequalities).** If the weight satisfies the quadrangle inequality and is monotone under inclusion, then the optimal cost satisfies the quadrangle inequality too, and the largest optimal roots are monotone: $R(i, j) \le R(i, j + 1)$ and $R(i, j) \le R(i + 1, j)$.

@decl RotationBST.Classical.Static.Optimal.Results.cost_quadrangle RotationBST.Classical.Static.Optimal.Results.root_le_root_right RotationBST.Classical.Static.Optimal.Results.root_le_root_left

### Knuth's algorithm

Knuth's algorithm fills the table of costs and roots by increasing interval length. For an interval of length at least two it examines only the roots between $R(i, j - 1)$ and $R(i + 1, j)$. Along each diagonal of the table these windows overlap only at their ends, so a whole diagonal examines $O(n)$ roots, and the whole table $O(n^2)$.

@decl RotationBST.Classical.Static.Optimal.scan RotationBST.Classical.Static.Optimal.knuthEntry RotationBST.Classical.Static.Optimal.knuthTables RotationBST.Classical.Static.Optimal.knuth

**Theorem (Knuth).** Under the same two hypotheses, Knuth's algorithm returns the optimal cost of $[0, n)$ and examines at most $2n^2$ candidate roots.

@decl RotationBST.Classical.Static.Optimal.Results.knuth_cost RotationBST.Classical.Static.Optimal.Results.knuth_steps

::: caveat What the step count measures
`knuth` returns a count of the candidate roots it examines, not a running time in a machine model. Each examination is a constant number of table lookups and additions, so the count is the usual measure of the algorithm's work. The tables are functions in Lean, not arrays, so the Lean evaluation itself is not quadratic.
:::

### Key weights and request sequences

For key weights $w_0, \dots, w_{n-1}$, the interval weight is the sum of the weights in the interval:

@decl RotationBST.Classical.Static.weightedCost RotationBST.Classical.Static.rangeWeight RotationBST.Classical.Static.optCost RotationBST.Classical.Static.optTree RotationBST.Classical.Static.counts

**Theorem (key weights).** Interval sums satisfy the quadrangle inequality (in fact with equality) and are monotone under inclusion. The interval cost of a tree is its weighted depth. The optimal tree has $n$ keys and costs `optCost w`, no tree costs less, and Knuth's algorithm computes this cost with at most $2n^2$ steps.

@decl RotationBST.Classical.Static.Optimal.Results.rangeWeight_quadrangle RotationBST.Classical.Static.Optimal.Results.rangeWeight_monotone RotationBST.Classical.Static.Optimal.Results.weightedCost_eq_intervalCost RotationBST.Classical.Static.Optimal.Results.optTree_size RotationBST.Classical.Static.Optimal.Results.optTree_cost RotationBST.Classical.Static.Optimal.Results.optCost_le RotationBST.Classical.Static.Optimal.Results.knuth_optCost RotationBST.Classical.Static.Optimal.Results.knuth_steps_le

With the request counts of a sequence as weights, the weighted cost is the static search cost. So `optCost (counts n xs)` is $\mathrm{RF}^*$, the cost of the best static tree in the [map of the bounds](part-bounds.html#a-map-of-the-bounds), and it lies between a third of the entropy bound and the entropy bound:

**Theorem (the best static tree for a sequence).** Searching a tree costs its weighted cost under the request counts. The optimal tree for the counts serves the sequence at cost `optCost`, and every tree on the same keys costs at least that much. This optimum is between a third of the entropy bound and the entropy bound, and at most $m(1 + \lfloor\log_2 n\rfloor)$.

@decl RotationBST.Classical.Static.Optimal.Results.staticCost_eq_weightedCost RotationBST.Classical.Static.Optimal.Results.optTree_static RotationBST.Classical.Static.Optimal.Results.optCost_le_static RotationBST.Classical.Static.Optimal.Results.optCost_entropy RotationBST.Classical.Static.Optimal.Results.optCost_le_balanced

The Isabelle Archive of Formal Proofs has a formalization of the same three steps, the recurrence, Yao's inequality and Knuth's algorithm [@nipkow2018].

## Further results

When only the gaps carry weight, the searches all end at leaves, and the problem becomes that of optimal *alphabetic* codes. The algorithms of @hu1971 and @garsia1977 solve it in $O(n \log n)$ time. They are listed as a stretch goal in the roadmap ([S3](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#s3-optimal-alphabetic-trees)).
