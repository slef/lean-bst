# GreedyASS

In 1988 Joan Lucas proposed an offline BST algorithm now called *Greedy Future*, and Ian Munro rediscovered it in 2000. To serve a request, touch its search path, then rearrange the path so that the keys on it that will be requested soonest are nearest the top. The rule is simple and locally sensible, it performs very well in experiments, and it is conjectured to be within a constant factor of the offline optimum.

Demaine, Harmon, Iacono, Kane and Pătraşcu (2009) found that in the geometric view of [Chapter 8](geometry.html), Greedy Future no longer needs the future. Its touched points are produced by a sweep that looks only at the past. When request $x$ arrives at time $t$, add the point $(x, t)$, and for every old point whose rectangle with $(x, t)$ contains no other old point, add its projection onto row $t$. Every rectangle that would otherwise be empty receives the cheapest possible repair. Combined with their simulation theorem, which turns any online geometric algorithm into an online BST algorithm at a constant-factor cost ([Chapter 17](simulation.html)), this makes Greedy an *online* BST algorithm. Greedy and splay trees are the two main candidates for a dynamically optimal BST algorithm.

This chapter defines the sweep, proves that it is a legal online geometric algorithm, and proves that each row it adds is the unique smallest legal row. The definitions are in `Algorithms/GreedyASS/Algorithm/Abstract.lean` and the theorems in `Algorithms/GreedyASS/Abstract.lean`.

## The sweep

@decl RotationBST.Geometric.Visible

An old point `q` is visible from the request `(request, time)` when it is in a different column and no other old point lies in the closed rectangle spanned by `q` and the request. Only the old set `P` is consulted, so all visible points are found at once, before the new row is built.

::: check
- Old points in the request's own column are never visible. Their projection would be the request, which is added anyway.
- "No other point" includes the boundary: an old point on the edge of the rectangle, or at its far corner, hides `q`.
- Only the latest point in a column can be visible, because any earlier point in that column has the later one inside its rectangle with the request.
:::

@decl RotationBST.Geometric.instDecidableVisible

Visibility is decidable because `P` is finite, so the sweep is an executable filter:

@decl RotationBST.Geometric.greedySweep

`greedySweep time request P` is the set of keys of the new row: the request, together with the keys of all visible old points. Its arguments are exactly those of an online step in the sense of [[Geometric.OnlineAlgorithm]]: the time, the request and the past points.

The figure runs the sweep. At each step the shaded rectangles are the empty ones, between the new request and each visible old point, and the dashed lines are the projections that fill them.

@viz geometric {"mode": "greedy", "n": 8, "requests": [0, 4, 2, 6, 1, 5, 3, 7], "title": "GreedyASS on the bit-reversal sequence"}

On the bit-reversal sequence $0, 4, 2, 6, 1, 5, 3, 7$ GreedyASS adds $21$ points. On the sequential sequence $0, 1, \dots, 7$, typed into the figure, each row is the request and its predecessor, $2m - 1 = 15$ points in total: a linear cost for a sequential scan, as for splay trees ([Section 15.4](beyond.html#sequential-access)).

## A legal online algorithm

The sweep always produces a legal row:

@decl RotationBST.Geometric.GreedyASS.Results.greedy_step

From any bounded, arborally satisfied history and any valid request, the sweep's row contains the request, uses only valid keys, and keeps the point set arborally satisfied. The proof checks every new rectangle, between an old point and a new point, by cases on where the request lies relative to it. The visible points are exactly what is needed to fill the rectangles that the request alone would leave empty.

So the sweep is an online geometric algorithm, with this theorem as its certificate:

@decl RotationBST.Geometric.GreedyASS.Results.greedyASS

::: check
`greedyASS` is a definition, placed in the `Results` namespace next to the theorem it packages. Its `step` sees only the time, the request and the past points, so it is online by construction, exactly as GreedyASS should be. The certificate holds for every satisfied history, not only for histories produced by GreedyASS itself.
:::

## Each row is the smallest possible

Every legal row must contain the sweep's row:

@decl RotationBST.Geometric.GreedyASS.Results.greedy_required

The argument is short. Suppose `q` = $(x, t')$ is visible from the request $(r, t)$ but the legal row omits $x$. The row contains $r$, so among the new points between $x$ and $r$, take the one closest to $x$, say $(y, t)$. The rectangle of `q` and $(y, t)$ lies inside the rectangle of `q` and the request, so it contains no other old point by visibility, and no other new point by the choice of $y$. Since $y \ne x$ and $t' < t$, it is nondegenerate, so the completed set is not arborally satisfied, a contradiction. The theorem needs only the `History` hypothesis, which makes old points strictly earlier than the new row.

Together with `greedy_step`, the sweep's row is a legal row contained in every legal row. It is therefore the unique legal row of minimum size, which is the specification [[Geometric.GreedyRow]] of [Chapter 8](geometry.html):

@decl RotationBST.Geometric.GreedyASS.Results.greedy_minimum

::: caveat Minimal rows, not minimal totals
`greedy_minimum` is a statement about one row, given the past. It does not say that the whole GreedyASS solution has minimum size among offline solutions ([[Geometric.Results.optimal_exists]]); adding more points early can make later rows cheaper. The library does not claim that GreedyASS is optimal, or within a constant factor of optimal. That is the conjecture.
:::

## A brute-force version of the specification

`GreedyRow` can also be computed directly from its definition, by trying all subsets of keys:

@decl RotationBST.Geometric.smaller RotationBST.Geometric.subsets RotationBST.Geometric.greedy

`subsets n` lists all $2^n$ subsets of $\{0, \dots, n-1\}$, `greedy` keeps those that are legal completions (decidable thanks to the instances of [Chapter 8](geometry.html)), and the fold returns a smallest one, starting from the full key set. This is exponential and only meant for small cases. The library's tests evaluate it by `decide`, for instance

```lean
example : greedy 4 2 2 {(1, 0), (1, 1), (3, 1)} = {1, 2, 3} := by decide
```

The sweep is the efficient implementation, and `greedy_minimum` says that the two agree whenever the history is satisfied. The figure's JavaScript port of the sweep is tested against the Lean sweep, and also against a port of `greedy` on all small cases.

## From points to a search tree

GreedyASS produces points, not rotations. [Chapter 17](simulation.html) turns any online geometric algorithm into one online BST algorithm, fixed before the request sequence, whose cost is at most a constant times the number of points plus a term linear in $n$ ([[Geometric.Simulation.Results.uniform_simulation]]). Applied to [[Geometric.GreedyASS.Results.greedyASS]], it gives an online BST algorithm whose total cost is $O(\text{GreedyASS points} + n)$. Any future bound on the number of GreedyASS points, such as the conjectured comparison with the offline optimum, would therefore transfer to binary search trees.

::: note Known results
Fox (2011) proved that GreedyASS satisfies an access lemma analogous to that of splay trees, which gives it the logarithmic amortized bound. Many further adaptive properties have since been established for it. None of these are formalized in the library.
:::
