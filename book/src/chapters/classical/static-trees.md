# Static search trees

A static tree never changes. It is built once, and then serves every request by an ordinary search from the root. Serving key $x$ costs one unit plus the depth of $x$: this is [[StaticTree.cost]], and [Chapter 13](bounds.html#comparison-with-a-fixed-tree) shows that it is exactly the cost of a pointer-machine execution that never rotates.

A static tree can know two things in advance: the number of keys, or how often each key will be requested. The first gives the perfect tree, which is the best possible worst-case guarantee. The second gives entropy trees and optimal trees, which are the benchmark behind static optimality.

## Perfect trees

The library defines the perfect tree [[Tango.perfect]] of height $h$, and the balanced tree [[Tango.balanced]] on any number $n$ of keys, which splits the keys evenly at every node ([Section 25.1](preferred-paths.html)).

::: todo
- The balanced tree on $n$ keys has height $\lfloor \log_2 n \rfloor$, so it serves $m$ requests at cost at most $m(1 + \lfloor \log_2 n \rfloor)$.
- Every tree on $n$ keys has a key at depth at least $\lfloor \log_2 n \rfloor$. So no static tree has a better worst-case guarantee.
- The static finger sum is at most $m(1 + \log_2 n)$, for every finger. This places $m(1 + \log_2 n)$ at the bottom of the [map of the bounds](part-bounds.html#a-map-of-the-bounds).

Roadmap [entry 4](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#4-perfect-trees-and-the-logarithmic-baseline).
:::

## Entropy trees

Suppose that key $x$ is requested $q_x$ times among $m$ requests. A tree in which $x$ has depth about $\log_2(m / q_x)$ serves the requests at cost about the entropy bound [[Bounds.staticCost]]. Both directions are formalized ([Chapter 13](bounds.html#comparison-with-a-fixed-tree)):

- **Lower bound.** Every static tree costs at least a third of the entropy bound ([[StaticTree.Results.entropy_lower_bound]]).
- **Upper bound.** Some static tree costs at most the entropy bound ([[StaticTree.Results.entropy_upper_bound]]).

The tree of the upper bound is built by a rule close to that of @mehlhorn1975: put the weighted median at the root and recurse on both sides. This is the weighted search tree of [Chapter 33](prefix-sums.html#weighted-search-trees), where every key of weight $w_x$ lands at depth at most $\log_2(W/w_x)$. Mehlhorn's sharper analysis, which bounds the cost by the entropy plus a small additive constant per request, is not formalized. The constant factor of the library's bound is enough for every use in this book.

## Optimal static trees

The entropy tree is within a constant factor of the best static tree. The best static tree itself can be computed exactly by dynamic programming. Let $W(i, j)$ be the total weight of keys $i$ to $j$. The cheapest tree on these keys puts some key $r$ at the root, and then uses the cheapest trees on both sides:

$$C(i, j) \;=\; W(i, j) + \min_{i \le r \le j} \bigl( C(i, r - 1) + C(r + 1, j) \bigr), \qquad C(i, i - 1) = 0 .$$

Computed directly this takes $O(n^3)$ time [@gilbert1959]. @knuth1971 observed that the optimal roots are monotone: some optimal root of keys $i..j$ lies between optimal roots of $i..j-1$ and of $i+1..j$. Restricting the minimum to that window makes the total work $O(n^2)$. @yao1980 explained why. Whenever the weight function satisfies the *quadrangle inequality* and is monotone on nested intervals, so does the cost $C$, and then the optimal roots are monotone. The interval weight $W$ satisfies the quadrangle inequality with equality, and it is monotone because weights are nonnegative.

The book will present Yao's theorem as the general statement and Knuth's algorithm as its instance. The classical problem also gives weights to the gaps between keys, for unsuccessful searches. The same recurrence and the same theorem cover that case. In the models of this book, every request is a key, so the gap weights are zero.

::: todo
- The cubic recurrence computes the cost of an optimal static tree, and builds one. That cost is $\mathrm{RF}^*$, the best static tree of the [map of the bounds](part-bounds.html#a-map-of-the-bounds).
- Yao's theorem: the quadrangle inequality for the weights implies monotone optimal roots.
- Knuth's $O(n^2)$ algorithm computes the same cost.

Roadmap [entry 5](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#5-optimal-static-trees). The Isabelle Archive of Formal Proofs has a formalization of the same three steps [@nipkow2018].
:::

## Further results

When only the gaps carry weight, the searches all end at leaves, and the problem becomes that of optimal *alphabetic* codes. The algorithms of @hu1971 and @garsia1977 solve it in $O(n \log n)$ time. They are listed as a stretch goal in the roadmap ([S3](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#s3-optimal-alphabetic-trees)).
