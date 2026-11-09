# Prefix sums and weighted search trees

This chapter collects two small data structures that algorithms of [Part IV](part-algorithms.html) use as building blocks.

- **Two-dimensional prefix sums** answer a rectangle-sum query on a fixed matrix with four table reads. The optimal lazy-finger tree of [Chapter 29](optimal-lazy-finger.html) uses them to compute, in constant time, how many request transitions cross the boundary of a key interval.
- **Weighted search trees** are static BSTs built by recursive weighted-median splitting, in which a key of weight $w_x$ out of a total $W$ has depth at most $\log_2(W/w_x)$. The multiple-tree structure of [Chapter 30](multiple-trees.html) builds each of its local trees this way, from the successor frequencies of one key, mixed with a uniform baseline so that every key also has depth $O(\log n)$.

Both are standard, and a reader who trusts them can skip this chapter: the theorems of [Chapter 29](optimal-lazy-finger.html) and [Chapter 30](multiple-trees.html) restate what they need. The chapter is here for the reader who checks a reading path, which goes through these definitions, or who wants to see the exact constants.

```headline prefix-sums-weighted-depth
title: Weighted-median trees have entropy depth, even with a uniform baseline
theorems: WeightedSearch.Results.mass WeightedSearch.Results.depth WeightedSearch.Results.balanced_depth

Let $w_0, \dots, w_{n-1}$ be natural-number weights with total $W$. The tree built by recursive weighted-median splitting has the keys $0, \dots, n-1$ in order, and every key $x$ satisfies $2^{\mathrm{depth}(x)}\, w_x \le W$, so $\mathrm{depth}(x) \le \log_2(W / w_x)$ when $w_x > 0$. Building instead from the regularized weights $n\,w_x + W + 1$ gives a tree in which every key with $w_x > 0$ satisfies both

$$\mathrm{depth}(x) \;\le\; \log_2 \frac{3W}{w_x} \qquad\text{and}\qquad \mathrm{depth}(x) \;\le\; \log_2(2n).$$

Depth counts edges from the root, as [[RotationBST.Tree.depth]]. The uniform bound $2^{\mathrm{depth}(x)} \le 2n$ holds for every key, including those of weight zero.
```

The definitions are in `Structures/PrefixSum/Definitions/Abstract.lean` and `Structures/WeightedSearch/Definitions/Abstract.lean`, the theorems in `Structures/PrefixSum/Abstract.lean` and `Structures/WeightedSearch/Abstract.lean`.

## Two-dimensional prefix sums

Given a matrix $f$, store $P[a][b] = \sum_{i < a} \sum_{j < b} f(i, j)$ for all $a, b$. Then the sum over any half-open rectangle $[a, b) \times [c, d)$ follows by inclusion and exclusion:

$$\sum_{i \in [a,b)} \sum_{j \in [c,d)} f(i, j) \;=\; P[b][d] - P[a][d] - P[b][c] + P[a][c].$$

The table has $(h + 1)(w + 1)$ entries for an $h \times w$ matrix and is built row by row in $O(hw)$ time.

@decl RotationBST.PrefixSum.Table RotationBST.PrefixSum.get RotationBST.PrefixSum.sumPrefix

A `Table` is an array of rows of natural numbers. `get t a b` reads entry $(a, b)$, and returns $0$ outside the stored rows and columns, so reads are total. `sumPrefix f a b` is the mathematical quantity that the table is meant to store, the sum over $[0, a) \times [0, b)$.

@decl RotationBST.PrefixSum.row RotationBST.PrefixSum.build

`row f n` is the array of the $n + 1$ prefix sums $0, f(0), f(0) + f(1), \dots$ of one row. `build f width height` builds the $(\mathit{height} + 1) \times (\mathit{width} + 1)$ table: its row $0$ is all zeros, and each further row adds the horizontal prefix sums of the next input row to the previous table row. The input is a function, not a matrix, so a caller can pass any way of reading its data; the optimizer of [Chapter 29](optimal-lazy-finger.html) passes `get` of its transition-count matrix.

@decl RotationBST.PrefixSum.rectangle

`rectangle t a b c d` is the inclusion–exclusion formula. Subtraction on natural numbers truncates at $0$, so the definition adds the two positive terms before subtracting the two negative ones: since the true value is nonnegative, the result is exact whenever the table holds genuine prefix sums.

**Theorem (prefix sums).** Every stored entry, within the built rectangle, is the prefix sum it is meant to be.

@decl RotationBST.PrefixSum.Results.cached_prefix

**Theorem (rectangle queries).** For all $a \le b \le \mathit{height}$ and $c \le d \le \mathit{width}$, the rectangle query on the built table is the sum of $f$ over $[a, b) \times [c, d)$.

@decl RotationBST.PrefixSum.Results.rectangular_sum

The rectangles may be empty or touch any edge of the matrix. This is what lets the optimizer's toll, a sum of four such rectangles around a key interval, be exact for every interval, including those at the ends of the universe.

## Weighted search trees

Given weights $w_0, \dots, w_{n-1}$ with total $W$, put at the root the *weighted median*: the key in which the cumulative weight reaches half of the total. The keys to its left then have total weight at most $W/2$, and so do the keys to its right. Recursing on both sides halves the weight at each level, so a key of weight $w_x$ is at depth at most $\log_2(W/w_x)$. This is the classical guarantee of weight-balanced static trees.

@decl RotationBST.WeightedSearch.locate RotationBST.WeightedSearch.pivot

Weights are lists of natural numbers, and positions in the list are the key ranks. `locate ws target` returns the position of the key whose block of weight contains unit number `target`, when the weights are laid end to end; keys of weight zero have empty blocks and are skipped. `pivot ws` locates unit $\lfloor W/2 \rfloor$. When all weights are zero there is no such unit, and `pivot` takes the first key; the depth bounds below concern keys of positive weight and do not depend on this choice.

@decl RotationBST.WeightedSearch.buildFuel RotationBST.WeightedSearch.build

`build ws` puts the pivot at the root, then builds the left subtree from the weights before the pivot and the right subtree from those after it. The recursion is on a fuel argument, so that Lean accepts it as terminating; `build` supplies the list's length, which is enough to place every key, including keys of weight zero. The result is a [[RotationBST.Tree]], a shape whose inorder ranks are the positions in the list.

**Theorem (weighted median).** For a nonempty weight list, the pivot is a valid position, and the weights strictly before it and strictly after it each total at most half of $W$.

@decl RotationBST.WeightedSearch.Results.median

**Theorem (size, mass and depth).** The tree has one node per weight. Every key $x$ satisfies $2^{\mathrm{depth}(x)} w_x \le W$; hence, if $w_x > 0$, $\mathrm{depth}(x) \le \log_2(W/w_x)$.

@decl RotationBST.WeightedSearch.Results.size RotationBST.WeightedSearch.Results.mass RotationBST.WeightedSearch.Results.depth

`mass` is the exact integer statement, with no logarithm and no case split; it holds trivially for keys of weight zero. `depth` is the logarithmic form, in which depth is [[RotationBST.Tree.depth]], the number of edges from the root.

### A uniform baseline

Built from observed frequencies, a weighted tree can put an unobserved key, of weight zero, arbitrarily deep, up to depth $n - 1$. When such keys can still be requested, as in the multiple-tree structure, the weights are first mixed with a uniform baseline.

@decl RotationBST.WeightedSearch.regularize RotationBST.WeightedSearch.balancedBuild

`regularize` replaces each weight $w_x$ by $n\,w_x + W + 1$, where $n$ is the number of keys and $W$ the original total. The new total is $n(2W + 1)$. Every new weight is at least $W + 1$, which is roughly a $1/(2n)$ fraction of the new total, so every key gets logarithmic depth. And a key's new weight is at least $n\,w_x$, roughly a $w_x / (2W)$ fraction of the new total, so the frequency-based depth bound survives, within a factor of three in mass. The extra $+1$ keeps every weight positive, even when all original weights are zero. `balancedBuild` is `build` on the regularized weights.

**Theorem (regularized trees).** The regularized tree has one node per weight. Every key satisfies $2^{\mathrm{depth}(x)} \le 2n$ and $2^{\mathrm{depth}(x)} w_x \le 3W$. For a key of positive weight, in logarithmic form, $\mathrm{depth}(x) \le \log_2(3W/w_x)$ and $\mathrm{depth}(x) \le \log_2(2n)$.

@decl RotationBST.WeightedSearch.Results.balanced_size RotationBST.WeightedSearch.Results.balanced_capacity RotationBST.WeightedSearch.Results.balanced_mass RotationBST.WeightedSearch.Results.balanced_depth

**Theorem (pointer searches).** In the pointer machine of [Chapter 6](pointer.html), a search for a key $x$ of positive weight in the regularized tree, which walks down to $x$ and back to the root, leaves the tree unchanged and costs at most $1 + 2\log_2(3W/w_x)$ and at most $1 + 2\log_2(2n)$.

@decl RotationBST.WeightedSearch.Results.query

The cost is that of [[RotationBST.Pointer.Serves]]: one unit for the request, plus one per pointer move, down to $x$ and back up, since the next search there starts at the root again. This is a statement about the queries only; no theorem bounds the time to build the tree. The multiple-tree structure of [Chapter 30](multiple-trees.html) does not use this theorem: it searches its local trees in the linked-search model of [Chapter 11](linked-search.html), with its own lookup. It relies on the depth bounds above, for regularized trees whose nodes are labelled with actual keys by [[RotationBST.Tree.labelWith]].
