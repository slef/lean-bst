# GreedyASS and the finger bounds

A static BST searched with a *lazy finger* starts each search where the previous one ended, instead of at the root ([Chapter 14](lazy-finger.html)). Its cost on a request sequence is the total length of the walks between consecutive requests, and the best static tree for a given sequence is a strong benchmark. It is at least as good as the best root-finger tree, up to a factor two, and it adapts to locality as well. Bose, Douïeb, Iacono and Langerman [-@bose2016] showed that it is equivalent, up to constant factors, to a *weighted dynamic finger* bound: assign each key $k$ a positive weight $w_k$, and charge a move from $x$ to $y$ the logarithm of the total weight between them, divided by the smaller weight of the two endpoints.

Iacono and Langerman [-@iacono2016] proved that GreedyASS ([Chapter 21](greedy.html)) meets this benchmark. On every sequence it costs at most a constant times the cost of the best lazy-finger tree for that sequence, plus $O(n)$. This is a "static optimality" theorem with respect to a much stronger static benchmark, and it implies the dynamic finger bound by taking all weights equal. Since GreedyASS is an online BST algorithm through the simulation of [Chapter 22](simulation.html), the bounds hold for an online BST. The library formalizes the paper's Theorem 3.1, its leaf-oriented core, and the consequences Theorem 4.1, Theorem 4.2 and Corollary 1. This section states those consequences. Theorem 3.1 is the subject of [Chapter 26](greedy-amortized.html), and [Chapter 24](reference-forest.html) and [Chapter 25](greedy-potential.html) prepare it.

In all three results below, $n$ is the number of keys, $X = x_1, \dots, x_m$ is a sequence of keys in $\{0, \dots, n-1\}$, and $P_G(X)$ is the number of points that GreedyASS adds on $X$, starting from an empty history: its geometric cost, one unit per point, which includes one point per request.

```headline greedy-lazy-finger
title: GreedyASS is competitive with the best lazy-finger tree
source: @iacono2016
key: yes
theorems: Geometric.GreedyASS.Performance.Results.lazy_optimal Geometric.GreedyASS.Performance.Results.bst
skip: Geometric.instDecidableVisible | A decidability instance, together with the one for rectangles it uses, only lets Lean compute the filter in `greedySweep`. Any two instances for the same proposition agree, so they cannot change which keys the sweep keeps.

This is Theorem 4.1 of the paper. Let $\mathrm{LF}^*(X)$ be the least lazy-finger cost of $X$ over all BSTs on $n$ keys, where the first search starts at the root and each request costs one plus the number of edges walked from the previous request. Then

$$P_G(X) \;\le\; 120\,\mathrm{LF}^*(X) + 15\,n .$$

As a BST: there is a single online BST algorithm, depending only on $n$, such that for every initial tree on $n$ keys and every $X$, its total cost (rotations plus one per request) is at most

$$722280\,\mathrm{LF}^*(X) + 96303\,n .$$

In Lean, $P_G(X)$ is [[Geometric.rowCost]]` greedySweep 0 ∅ X` for the sweep [[Geometric.greedySweep]], $\mathrm{LF}^*$ is [[LazyFinger.optimalCost]] (a minimum, which is attained), and the BST algorithm is an [[RotationBST.Algorithm]] with cost [[RotationBST.Algorithm.totalCost]]. The second conjunct of `bst` also gives the weighted bound of the next box.
```

```headline greedy-weighted-finger
title: GreedyASS has the weighted dynamic finger property
source: @iacono2016
key: yes
theorems: Geometric.GreedyASS.Performance.Results.weighted_optimal Geometric.GreedyASS.Performance.Results.weighted Geometric.GreedyASS.Performance.Results.bst_weighted
skip: Geometric.instDecidableVisible | A decidability instance, together with the one for rectangles it uses, only lets Lean compute the filter in `greedySweep`. Any two instances for the same proposition agree, so they cannot change which keys the sweep keeps.

This is Theorem 4.2 of the paper. For positive weights $w_0, \dots, w_{n-1}$ and keys $x, y$, let $W[x, y] = \sum_{\min(x,y) \le k \le \max(x,y)} w_k$, both endpoints included, and

$$\mathrm{WF}_w(p, X) \;=\; \sum_{j=1}^{m} \Bigl(1 + \log_2 \frac{W[x_{j-1}, x_j]}{\min(w_{x_{j-1}}, w_{x_j})}\Bigr), \qquad x_0 = p,$$

where the start key $p < n$ is arbitrary. Then for every such $w$ and $p$,

$$P_G(X) \;\le\; 480\,\mathrm{WF}_w(p, X) + 15\,n,$$

and the same holds with $\mathrm{WF}_w(p, X)$ replaced by its infimum over all positive weightings. As a BST: there is a single online BST algorithm, depending only on $n$, such that for every initial tree on $n$ keys, every $p < n$, every positive weighting $w$ and every $X$, its total cost is at most

$$2889120\,\mathrm{WF}_w(p, X) + 96303\,n .$$

The weights appear only in the bound: neither GreedyASS nor the BST algorithm knows them. In Lean, $\mathrm{WF}_w(p, X)$ is [[WeightedFinger.costFrom]]` w p X` and the infimum is [[WeightedFinger.optimalCostFrom]], which need not be attained.
```

```headline greedy-dynamic-finger
title: GreedyASS has the dynamic finger property
source: @iacono2016
key: yes
theorems: Geometric.GreedyASS.Performance.Results.dynamic Geometric.GreedyASS.Performance.Results.bst_dynamic
skip: Geometric.instDecidableVisible | A decidability instance, together with the one for rectangles it uses, only lets Lean compute the filter in `greedySweep`. Any two instances for the same proposition agree, so they cannot change which keys the sweep keeps.

This is Corollary 1 of the paper, the case of unit weights. For every start key $p < n$, with $x_0 = p$,

$$P_G(X) \;\le\; 480 \sum_{j=1}^{m} \Bigl(1 + \log_2\bigl(|x_j - x_{j-1}| + 1\bigr)\Bigr) + 15\,n .$$

As a BST: there is a single online BST algorithm, depending only on $n$, whose total cost from every initial tree on $n$ keys, for every $p < n$ and every $X$, is at most $2889120$ times the same sum, plus $96303\,n$.

In Lean, the sum is [[Bounds.dynamicFingerCostFrom]]` p X`.
```

The three boxes are enough to confirm the results: their statements use only the benchmarks of [Chapter 14](lazy-finger.html), the GreedyASS sweep of [Chapter 21](greedy.html), and the online algorithms of [Part I](part-models.html). The rest of this section has three parts. [Section 23.1](#reading-the-statements) explains the conventions and the two forms of each statement, geometric and BST. [Section 23.2](#the-geometric-bounds) to [Section 23.4](#on-the-pointer-machine) state every theorem of `Algorithms/GreedyASS/Performance/Abstract.lean`, in English and in Lean. [Section 23.5](#from-theorem-3-1-to-the-finger-bounds) derives them from Theorem 3.1, and [Section 23.6](#a-map-of-the-proof-of-theorem-3-1) gives a map of the proof of Theorem 3.1 across the next three sections.

## Reading the statements

### Geometric bounds and their realizations

Each result comes in two forms.

- **The geometric form** is about GreedyASS itself. Its left side is [[Geometric.rowCost]]` greedySweep 0 ∅ xs`, the number of points that the sweep adds when run from an empty history at time $0$. It bounds an explicit, executable function of the request sequence, and says nothing about trees, rotations or initial trees. These are the theorems `lazy_tree`, `lazy_from`, `lazy_optimal`, `lazy_optimal_from`, `weighted`, `weighted_optimal` and `dynamic`.
- **The realizations** are about binary search trees. `bst`, `bst_weighted` and `bst_dynamic` assert that there is an online algorithm in the rotation model of [Chapter 5](online.html), and bound its total cost from every initial tree. `pointer` and `pointer_weighted` assert the same for an actual execution on the pointer machine of [Chapter 6](pointer.html), where navigation is charged too.

The realizations are proved by feeding [[Geometric.greedyASS]] to the simulation theorems of [Chapter 22](simulation.html), which turn $P$ points into a BST execution of cost at most $6019\,P + 6018\,n$ ([[Geometric.Simulation.Results.normalized_simulation]]), or into a pointer execution of cost at most $192593\,P + 192576\,n$ ([[Geometric.Simulation.Results.pointer_simulation]]). Their constants are the geometric constants multiplied through by these. They are not meant to be sharp.

::: caveat What the realizations say
The statements of `bst`, `bst_weighted`, `bst_dynamic`, `pointer` and `pointer_weighted` begin with `∃ algorithm : Algorithm`. They assert that *some* online BST algorithm has the bound, and do not name it. The algorithm built in the proof is the simulation of GreedyASS, chosen with `Classical.choose`, but a reader who only checks the statements learns that an online BST achieving the lazy-finger and weighted dynamic finger bounds exists, not that the BST obtained from GreedyASS is that algorithm. The geometric theorems are the ones about GreedyASS by name.
:::

### One causal policy, chosen first

The order of the quantifiers in the realizations matters. In `bst_weighted` it is

$$\exists\, \mathit{algorithm}\ \ \forall\, \mathit{initial}\ \ \forall\, p\ \ \forall\, w\ \ \forall\, X .$$

The algorithm is chosen knowing only $n$: before the initial tree, before the start key $p$ and the weights $w$ of the benchmark, and before the requests. It is *causal*: as an [[RotationBST.Algorithm]], each step sees only the past requests, the current tree and the current request ([Chapter 5](online.html)). So one online algorithm satisfies the bound for all weightings at once, exactly as splaying satisfies the static optimality bound for the frequencies it never sees ([Chapter 19](analysis.html)). In `bst`, likewise, the same algorithm satisfies both the lazy-finger bound and the weighted bound for every $p$.

These are not dynamic optimality claims. The benchmarks are static: the best *fixed* tree with a lazy finger, or the best *fixed* weighting. Whether GreedyASS is within a constant factor of the offline optimum is open, and the library does not claim it ([Chapter 21](greedy.html)).

### Conventions

The library makes several normalizations explicit that the paper leaves to the $O(\cdot)$.

- **A unit per request.** Every benchmark charges at least one per request: [[LazyFinger.costFrom]] charges $1$ plus the edge distance, the weighted charge [[WeightedFinger.charge]] is $1 + \log_2(\cdot)$, and the dynamic finger charge is $1 + \log_2(|x_j - x_{j-1}| + 1)$. The paper's weighted formula is a sum of logarithms alone, which is $0$ on a sequence that repeats one key, while GreedyASS pays one point per request. The unit makes the inequalities true as stated, with no hidden term in $m$.
- **The first request.** The paper's sums start from an unspecified $s_0$. The library fixes it in each benchmark. [[LazyFinger.cost]] starts the finger at the root of the tree. [[LazyFinger.costFrom]], [[WeightedFinger.costFrom]] and [[Bounds.dynamicFingerCostFrom]] take an explicit start key $p$, and the theorems hold for *every* valid $p$. Choosing $p = x_1$ makes the first charge exactly $1$ ([[WeightedFinger.Results.repeated_key]]), which recovers the paper's sums from $j = 2$, plus the unit per request.
- **Minimum and infimum.** [[LazyFinger.optimalCost]] and [[LazyFinger.optimalCostFrom]] are infima of natural numbers over the trees on $n$ keys. They are attained ([[LazyFinger.Results.optimal_attained]]), so they are minima, as in the paper. [[WeightedFinger.optimalCostFrom]] is an infimum of real numbers over positive weightings, and no optimal weighting is assumed to exist. A bound in terms of an infimum is the stronger statement: it implies the bound for each weighting, which is how `weighted` follows from `weighted_optimal`.
- **Startup.** The additive term is explicit and linear: $15\,n$ in the geometric form, which pays for the initial credits of the potential and for the first access to each column ([Section 23.6](#a-map-of-the-proof-of-theorem-3-1)). In the realizations it also absorbs the simulation's startup, which rotates an arbitrary initial tree into a fixed shape.
- **Valid keys.** All requests, and the start key $p$, must be less than $n$. The weights need only be positive on $\{0, \dots, n-1\}$; values outside are never read, because masses are sums over intervals between valid keys.

## The geometric bounds

Theorem 4.1 is the lazy-finger bound. It comes in four variants: against one fixed tree or against the best tree, and with the finger starting at the root or at a given key. The basic one is against a fixed tree with a given start key.

**Theorem (one tree, any start).** Let $t$ be a BST on $n$ keys, $p < n$, and $X$ a sequence of keys of $t$. Then $P_G(X) \le 120\,\mathrm{LF}_t(p, X) + 15\,n$, where $\mathrm{LF}_t(p, X)$ is the lazy-finger cost of $X$ in $t$ with the finger starting at $p$.

@decl Geometric.GreedyASS.Performance.Results.lazy_from

Neither $t$ nor $p$ is an input of the sweep: the same point count is bounded by the cost of every tree with every start key.

**Theorem (one tree, root start).** For every BST $t$ on $n$ keys and every sequence $X$ of its keys, $P_G(X) \le 120\,\mathrm{LF}_t(X) + 15\,n$, where the finger starts at the root.

@decl Geometric.GreedyASS.Performance.Results.lazy_tree

For the empty tree there are no valid requests, and both sides are $0$.

**Theorem (Theorem 4.1).** For every $n$ and every sequence $X$ of keys less than $n$, $P_G(X) \le 120\,\mathrm{LF}^*(X) + 15\,n$, where $\mathrm{LF}^*(X)$ is the least root-start lazy-finger cost of $X$ over all BSTs on $n$ keys.

@decl Geometric.GreedyASS.Performance.Results.lazy_optimal

**Theorem (Theorem 4.1, any start).** For every $p < n$, $P_G(X) \le 120\,\mathrm{LF}^*(p, X) + 15\,n$, where $\mathrm{LF}^*(p, X)$ is the least lazy-finger cost over all BSTs on $n$ keys with the finger starting at $p$.

@decl Geometric.GreedyASS.Performance.Results.lazy_optimal_from

Theorem 4.2 is the weighted dynamic finger bound, first against the best weighting and then against each one.

**Theorem (Theorem 4.2).** For every $p < n$ and every sequence $X$ of keys less than $n$, $P_G(X) \le 480\,\mathrm{WF}^*(p, X) + 15\,n$, where $\mathrm{WF}^*(p, X)$ is the infimum of $\mathrm{WF}_w(p, X)$ over all weightings $w$ that are positive on the keys.

@decl Geometric.GreedyASS.Performance.Results.weighted_optimal

**Theorem (Theorem 4.2, each weighting).** For every weighting $w$ positive on the keys, every $p < n$ and every $X$, $P_G(X) \le 480\,\mathrm{WF}_w(p, X) + 15\,n$.

@decl Geometric.GreedyASS.Performance.Results.weighted

With unit weights, $W[x, y] = |x - y| + 1$ and the minimum weight is $1$, so the weighted charge becomes the dynamic finger charge ([[LazyFinger.Consequences.Results.unit_weights]]).

**Theorem (Corollary 1).** For every $p < n$ and every sequence $X$ of keys less than $n$, $P_G(X) \le 480 \sum_j \bigl(1 + \log_2(|x_j - x_{j-1}| + 1)\bigr) + 15\,n$, with $x_0 = p$.

@decl Geometric.GreedyASS.Performance.Results.dynamic

::: note Further consequences
The best lazy-finger tree is within a factor two of the best root-finger tree ([[LazyFinger.Results.optimal_root_finger]], [Chapter 14](lazy-finger.html)), so `lazy_optimal` also bounds $P_G(X)$ by a constant times the cost of the optimal static tree, plus $O(n)$. The library does not state this combination as a separate theorem about GreedyASS; it is a one-line consequence of the two statements.
:::

## One online BST algorithm

The realizations in the rotation model come in three statements. The first carries both Theorem 4.1 and Theorem 4.2, against the best tree and the best weighting.

**Theorem (Theorems 4.1 and 4.2 for a BST).** For every $n$ there is an online BST algorithm such that, for every initial tree on $n$ keys and every sequence $X$ of keys less than $n$, its total cost is at most $722280\,\mathrm{LF}^*(X) + 96303\,n$, and also at most $2889120\,\mathrm{WF}^*(p, X) + 96303\,n$ for every $p < n$.

@decl Geometric.GreedyASS.Performance.Results.bst

The constants are those of the geometric theorems pushed through the simulation $T \le 6019\,P + 6018\,n$:

$$6019 \cdot 120 = 722280, \qquad 6019 \cdot 480 = 2889120, \qquad 6019 \cdot 15 + 6018 = 96303 .$$

**Theorem (Theorem 4.2 for a BST, each weighting).** For every $n$ there is an online BST algorithm such that, for every initial tree on $n$ keys, every $p < n$, every weighting $w$ positive on the keys and every $X$, its total cost is at most $2889120\,\mathrm{WF}_w(p, X) + 96303\,n$.

@decl Geometric.GreedyASS.Performance.Results.bst_weighted

**Theorem (Corollary 1 for a BST).** For every $n$ there is an online BST algorithm such that, for every initial tree on $n$ keys, every $p < n$ and every $X$, its total cost is at most $2889120 \sum_j \bigl(1 + \log_2(|x_j - x_{j-1}| + 1)\bigr) + 96303\,n$, with $x_0 = p$.

@decl Geometric.GreedyASS.Performance.Results.bst_dynamic

::: check
- **Total cost.** [[RotationBST.Algorithm.totalCost]] is rotations plus one per request, the conventional cost of [Chapter 5](online.html#two-cost-measures). Each step is certified to perform a legal [[RotationBST.Access]] of the request.
- **Every initial tree.** The bound holds from every tree of size $n$, not only from a tree chosen by the algorithm.
- **Uncharged planning.** As everywhere in the rotation model, the computation that decides which rotations to perform is free. The algorithm built in the proof replays the geometric history, and is not executable.
- **The algorithms may differ.** The three theorems are separate existence statements. Their witnesses are built the same way in the proofs, but the statements do not say that they are one algorithm. Within `bst`, the two bounds are for the same algorithm.
:::

## On the pointer machine

The rotation model charges only rotations. The pointer machine of [Chapter 6](pointer.html) charges every pointer move as well. The causal transformer [[Pointer.Lazy.Online.run]] runs a rotation-model algorithm on the pointer machine, starting from [[Pointer.Lazy.Online.initial]], and the simulation bounds its cost by $192593\,P + 192576\,n$ ([Chapter 22](simulation.html)).

**Theorem (Theorems 4.1 and 4.2 on the pointer machine).** For every $n$ there is a BST algorithm whose pointer-machine run, from every initial tree on $n$ keys and on every sequence $X$ of keys less than $n$, is a legal pointer execution serving $X$, with at most $23111160\,\mathrm{LF}^*(X) + 3081471\,n$ pointer instructions, and at most $92444640\,\mathrm{WF}^*(p, X) + 3081471\,n$ for every $p < n$.

@decl Geometric.GreedyASS.Performance.Results.pointer

**Theorem (Theorem 4.2 on the pointer machine, each weighting).** The same, with $92444640\,\mathrm{WF}_w(p, X) + 3081471\,n$ for every $p < n$ and every weighting $w$ positive on the keys.

@decl Geometric.GreedyASS.Performance.Results.pointer_weighted

The first conjunct says that the instructions form a [[Pointer.Execution]] that serves $X$ from the initial tree. The constants are $192593 \cdot 120 = 23111160$, $192593 \cdot 480 = 92444640$ and $192593 \cdot 15 + 192576 = 3081471$. The library has no pointer version of Corollary 1, but `pointer_weighted` with unit weights gives it, by [[LazyFinger.Consequences.Results.unit_weights]].

## From Theorem 3.1 to the finger bounds

All the theorems above rest on one inequality, the paper's Theorem 3.1. It compares GreedyASS with a lazy finger on a *leaf-oriented* reference tree, whose keys are its leaves ([Chapter 24](reference-forest.html)):

$$P_G(X) \;\le\; 24\,\mathrm{RC}_T(X) + 15\,\mathrm{leaves}(T),$$

for every leaf-oriented tree $T$ whose leaves include the requests ([[Amortized.Results.cost]], [Chapter 26](greedy-amortized.html)). The benchmark [[Amortized.referenceCost]] $\mathrm{RC}_T(X)$ charges one unit per request plus the number of reference edges between consecutive requests, and nothing for reaching the first request. The derivation of the finger bounds has four steps.

1. **From ordinary trees to leaf-oriented ones.** An ordinary BST $t$ on $n$ keys converts into a leaf-oriented tree $\mathtt{convert}\ t$ with exactly $n$ leaves, one per key, in the same order ([[Conversion.Results.population]]). The conversion at most doubles distances, up to an additive constant ([[Conversion.Results.distance]]), and the benchmark comparison [[Conversion.Results.cost_from]] gives $\mathrm{RC}_{\mathtt{convert}\,t}(X) \le 5\,\mathrm{LF}_t(p, X)$ for every valid $p$. Theorem 3.1 then gives `lazy_from` with constant $24 \cdot 5 = 120$, and $15\,\mathrm{leaves} = 15\,n$. The paper's Lemma 4.1 plays this role.
2. **From one tree to the best tree.** `lazy_tree` takes $p$ to be the root. Since the minimum over trees is attained ([[LazyFinger.Results.optimal_attained]] and [[LazyFinger.Results.optimal_from_attained]]), applying the one-tree bound to a minimizing tree gives `lazy_optimal` and `lazy_optimal_from`.
3. **From trees to weights.** The characterization theorem of the lazy-finger paper ([[LazyFinger.Results.characterization_from]], [Chapter 14](lazy-finger.html)) says that the best tree and the best weighting agree up to constants: $\mathrm{LF}^*(p, X) \le 4\,\mathrm{WF}^*(p, X)$. Combined with `lazy_optimal_from`, this is `weighted_optimal`, with constant $120 \cdot 4 = 480$. The infimum is below every weighting's cost ([[WeightedFinger.Results.optimal_le]]), which gives `weighted`. Unit weights give `dynamic`.
4. **From points to trees.** The simulation theorems of [Chapter 22](simulation.html), applied to [[Geometric.greedyASS]], give the realizations.

Only the first step uses anything specific to this paper. The other three are short proofs in `Performance/Geometric.lean`, `Performance/Simulation.lean` and `Performance/Corollaries.lean`, from theorems of other chapters.

## A map of the proof of Theorem 3.1

Theorem 3.1 is proved by a potential function, which the next three sections build. Fix a leaf-oriented reference tree $T$. GreedyASS knows nothing about $T$: the tree exists only in the analysis.

**The reference forest** ([Chapter 24](reference-forest.html)). After the search for $x_i$, delete from $T$ the path from the root to the leaf $x_i$. The remaining subtrees form the forest $F_i$. Between consecutive searches, $F_{i-1}$ becomes $F_i$ by merges up to the lowest common ancestor of $x_{i-1}$ and $x_i$, and then splits down to $x_i$: exactly one event per reference edge between the two leaves ([[Transitions.Results.transition]]). This is how the lazy-finger cost enters the argument.

**Items, colors and potential** ([Chapter 25](greedy-potential.html)). Every key accessed so far is an *item*. Its most recent access point is classified by its position in the GreedyASS point set (external, glancing or internal), and it receives a color (red, green, blue or purple) and a value. The values are node counts in the reference tree, from the item's leaf up to the root of its forest component, or up to the lowest common ancestor of its neighbors in the point set. In addition, every *virgin* root of the forest, one whose range has not been accessed since it became a root, carries a credit of $12$. The potential is the sum of all item values and all virgin credits.

**Paying for each row** ([Chapter 26](greedy-amortized.html)). Each request is served in two phases. In Phase I the forest changes from $F_{i-1}$ to $F_i$ while the points stay fixed. Each merge may raise the item potential by at most $12$, and each new root brings at most $12$ of virgin credit, so the $e$ events of the transition cost at most $24e$ in total, by the budget identity [[Transitions.Results.birth_budget]] (the paper's Lemma 3.3). In Phase II GreedyASS adds its row while the forest stays fixed. The new points are paid by a decrease of the potential: the values of the accessed items fall and the touched virgin roots lose their credit. The exceptions are few; for instance, a row touches at most two non-virgin roots (the paper's Lemma 3.7). The result is the paper's Lemma 3.19 ([[Amortized.Results.step]]): each row costs, amortized, at most $24$ per reference edge between consecutive searches, plus $24$, plus $3$ for each key accessed for the first time.

Summing over the requests ([[Amortized.Results.stream]]), the potential telescopes. It is never negative, and its initial value is at most $12$ per leaf. Every column is accessed for the first time at most once, which costs at most $3$ per leaf. Together these give the startup term $12 + 3 = 15$ per leaf, and the $24$ per edge and per request give $24\,\mathrm{RC}_T(X)$.

::: caveat Compared with the paper
- **Formalized.** Theorem 3.1, Theorem 4.1, Theorem 4.2 and Corollary 1, each with explicit constants, in the geometric model and as BST and pointer-machine executions.
- **Formalized later in the book.** Theorem 4.3, which combines the weighted bound with $O(\log\log n)$-competitiveness and $O(\log n)$ worst-case time per search, is the subject of [Chapter 38](combined-finger.html). It needs Tango with a linear startup term ([Chapter 30](tango-linear.html)), the ComboBST combination ([Chapter 33](combination.html)) and the deamortization ([Chapter 37](deamortization.html)); the result is an abstract BST-operation counterpart, without the paper's storage clauses.
- **Normalizations.** The unit per request, the explicit first finger, the explicit linear startup and the infimum over weightings are described in [Section 23.1](#conventions). The constants are explicit and not optimized.
:::
