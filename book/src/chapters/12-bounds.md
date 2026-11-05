# Adaptive bounds

Part I fixed what a BST execution is and what it costs. Part II asks how much a request sequence *must* or *may* cost, independently of any algorithm. Two kinds of statements live here. **Upper-bound benchmarks** are explicit functions of the sequence, such as the entropy of its access frequencies, that a good algorithm should match; this chapter defines them and proves the implications between them. **Lower bounds** hold for every execution, hence for the offline optimum; [Chapter 11](wilber.html) proves Wilber's interleave bound, the tool behind the $O(\log\log n)$-competitive Tango trees. Algorithms enter only in Part III, where each is measured against both.

Dynamic optimality is a comparison with an unknown optimum. The classical results about splay trees instead compare an algorithm with explicit functions of the request sequence. Each function measures one kind of locality: recency (working set), frequency (static optimality) and spatial proximity to a fixed key (static finger). This chapter defines these functions and the corresponding properties of an [`Algorithm`](online.html#online-algorithms). It also proves the implications between them, which hold for every algorithm. Whether splaying has these properties is the subject of [Chapter 14](analysis.html).

The chapter has two main results. The first is that the working-set bound is the strongest of the three: an algorithm that has it also has the other two, and therefore competes with every fixed BST. The second is the classical entropy lower bound for fixed trees, which makes "static optimality" mean what its name says.

```headline working-set-implies
title: The working-set bound implies static optimality and the static finger bound
source: Sleator and Tarjan, *Self-adjusting binary search trees* (1985); Iacono (2001)
theorems: Bounds.workingSet_implies_staticOptimality Bounds.staticOptimality_implies_staticFinger Bounds.workingSet_implies_staticFinger StaticTree.Results.workingSet_competes

Let $A$ be any online BST algorithm. Suppose there are constants $C, D$ such that, from every initial tree on $n$ keys and for every sequence $X$ of $m$ valid requests, $A$ performs at most $C \sum_j \bigl(1 + \lfloor\log_2 w_j\rfloor\bigr) + D\,n(1 + \lfloor\log_2 n\rfloor)$ rotations, where the working-set number $w_j$ is one plus the number of distinct keys requested since the previous request for $x_j$, or $n$ if $x_j$ has not been requested before (the working-set bound). Then, for new constants $C', D'$, the total cost of $A$ (rotations plus $m$) is at most

- $C' \bigl(m + \sum_x q_x \log_2(m/q_x)\bigr) + D'\,n(1 + \lfloor\log_2 n\rfloor)$, where $q_x$ is the number of requests for $x$ (static optimality);
- $C' \sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr) + D'\,n(1 + \lfloor\log_2 n\rfloor)$, for every finger $f$ at once (static finger);
- $C' \cdot \mathrm{cost}_u(X) + D'\,n(1 + \lfloor\log_2 n\rfloor)$, where $\mathrm{cost}_u(X)$ is the cost of serving $X$ in *any* fixed BST $u$ on the same keys, one unit per request plus the depth of the requested key.

In Lean, the three bounds are the properties [[RotationBST.HasWorkingSetBound]], [[RotationBST.HasStaticOptimalityBound]] and [[RotationBST.HasStaticFingerBound]] of an [[RotationBST.Algorithm]], and the fixed-tree cost is [[RotationBST.StaticTree.cost]]. Nothing about any specific algorithm is involved.
```

```headline static-entropy
title: Every fixed BST pays at least a third of the entropy bound
source: Mehlhorn, *Nearly optimal binary search trees* (1975)
theorems: StaticTree.Results.entropy_lower_bound

For every binary search tree $t$ on $n$ keys and every sequence $X$ of $m$ requests to its keys, let $q_x$ be the number of requests for $x$. Serving $X$ in $t$ without restructuring, at one unit per request plus the depth of the requested key, costs at least a third of the entropy bound:

$$m + \sum_x q_x \log_2 \frac{m}{q_x} \;\le\; 3\,\Bigl(m + \sum_j \mathrm{depth}_t(x_j)\Bigr).$$

In Lean, the left side is [[RotationBST.Bounds.staticCost]] and the right side is [[RotationBST.StaticTree.cost]].
```

## A map of the bounds

This chapter defines the classical benchmarks, and Part II and later chapters add more. The figure collects every relation between them that the library proves. Each benchmark is a function of the request sequence $X$ of length $m$ on $n$ keys:

- $\mathrm{IB}$, Wilber's interleave quantity for a reference tree, [[RotationBST.Wilber.interleave]] ([Chapter 13](wilber.html));
- $\mathrm{OPT}$, the least cost of an [[RotationBST.Execution]] serving $X$, the offline optimum of [Chapter 5](online.html) (the pointer-machine optimum is the same up to constant factors, by [Chapter 9](equivalence.html));
- $m(1+H)$, the conditional-entropy benchmark [[ConditionalEntropy.cost]] ([Chapter 16](conditional-entropy.html));
- $\mathrm{LF}^*$, the cost of the best static tree searched with a lazy finger, [[LazyFinger.optimalCost]] ([Chapter 14](lazy-finger.html));
- $\mathrm{WDF}^*$, the best weighted dynamic finger bound, [[WeightedFinger.optimalCostFrom]] ([Chapter 14](lazy-finger.html));
- $\mathrm{RF}^*$, the cost of the best static tree searched from the root, the minimum of [[StaticTree.cost]] over trees;
- $\mathrm{SO}$, the entropy bound [[Bounds.staticCost]]; $\mathrm{WS}$, the working-set sum [[workingSetSum]]; $\mathrm{SF}$, the static finger sum [[Bounds.fingerCost]]; and $\mathrm{DF}$, the dynamic finger sum [[Bounds.dynamicFingerCostFrom]].

An arrow $A \to B$ means that a cost bound in terms of $A$ implies one in terms of $B$. For most arrows this is an inequality $A \le c\,B + O(n)$ between the benchmarks themselves. The two arrows out of $\mathrm{WS}$ and $\mathrm{SO}$ are instead implications between properties of algorithms, with the startup allowance $D\,n(1 + \lfloor\log_2 n\rfloor)$ of this chapter. The violet tags name algorithms that meet a bound; they link to the chapters that prove it.

@viz boundsmap {}

| Relation | What is proved | Lean |
|---|---|---|
| $\mathrm{IB} \to \mathrm{OPT}$ | Every execution with $r$ rotations has $\mathrm{IB} \le 4r + 2m$, for every reference tree. | [[Wilber.Results.rotation_lower_bound\|rotation_lower_bound]] |
| $\mathrm{OPT} \to \mathrm{LF}^*$, strict | From every initial tree, some pointer execution costs at most $464\,\mathrm{LF}^* + 16n$. Some families have $\mathrm{OPT} = o(\mathrm{LF}^*)$. | [[LazyFinger.Dynamic.Results.optimal\|Dynamic.optimal]], [[LazyFinger.Separation.Results.family\|Separation.family]] |
| $\mathrm{OPT} \not\to m(1+H)$ | No execution bound $C\,m(1+H) + a(n)$ holds, whatever $C$ and $a$. | [[ConditionalEntropy.Results.obstruction\|obstruction]] |
| $\mathrm{LF}^* \leftrightarrow \mathrm{WDF}^*$ | $\mathrm{LF}^* + n \le 4(\mathrm{WDF}^* + n)$ and $\mathrm{WDF}^* + n \le 4(\mathrm{LF}^* + n)$. | [[LazyFinger.Results.characterization\|characterization]] |
| $\mathrm{LF}^* \to \mathrm{RF}^*$, strict | $\mathrm{LF}^* \le 2\,\mathrm{RF}_t$ for every tree $t$. Some families have $\mathrm{LF}^* = o(\mathrm{RF}^*)$. | [[LazyFinger.Results.optimal_root_finger\|optimal_root_finger]], [[LazyFinger.Sequential.Results.family\|Sequential.family]] |
| $\mathrm{LF}^* \to \mathrm{DF}$ | $\mathrm{LF}^* \le n + 4\,\mathrm{DF}$, from any start key. | [[LazyFinger.Consequences.Results.dynamic_finger\|dynamic_finger]] |
| $\mathrm{RF}^* \leftrightarrow \mathrm{SO}$ | $\mathrm{SO} \le 3\,\mathrm{RF}_t$ for every tree $t$, and $\mathrm{RF}_t \le \mathrm{SO}$ for some $t$. | [[StaticTree.Results.entropy_lower_bound\|entropy_lower_bound]], [[StaticTree.Results.entropy_upper_bound\|entropy_upper_bound]] |
| $\mathrm{WS} \to \mathrm{SO}$ | The working-set property implies static optimality. | [[Bounds.workingSet_implies_staticOptimality\|workingSet_implies_staticOptimality]] |
| $\mathrm{SO} \to \mathrm{SF}$ | Static optimality implies the static finger property, for every finger. | [[Bounds.staticOptimality_implies_staticFinger\|staticOptimality_implies_staticFinger]] |

Some composite relations are also stated directly, as inequalities between benchmarks: $\mathrm{LF}^* \le 2\,\mathrm{SO}$ and $\mathrm{LF}^* \le 6\,\mathrm{SF}$ ([[LazyFinger.Consequences.Results.static_optimality]], [[LazyFinger.Consequences.Results.static_finger]]), and a working-set algorithm competes with every fixed tree ([[StaticTree.Results.workingSet_competes]]).

The map shows only what is proved. Algorithms give further relations: splaying is a BST algorithm with the working-set bound, so $\mathrm{OPT}$ is at most a constant times $\mathrm{WS}$ plus startup; but the library states this only as a property of splaying, not as an arrow between benchmarks. Several classical facts are not formalized at all. Dynamic finger implies static finger, and the working-set and dynamic finger bounds are incomparable. Neither is in the library, so $\mathrm{DF}$ and $\mathrm{WS}$ have no arrows between them or towards $\mathrm{SF}$. The unified charge of [Section 12.5](bounds.html#the-unified-charge) is absent from the map for the same reason.

## Conventions

All logarithms are base 2. The sequence functions use `Nat.log2` (the floor of $\log_2$, with `Nat.log2 0 = 0`) where the original definitions are natural-number valued, and `Real.logb 2` (with $\log 0 = 0$) where they are real-valued. Every property has the same shape:

$$\exists\, C, D \in \mathbb N.\ \forall t, xs \text{ valid}.\quad \mathrm{cost}(a, t, xs) \;\le\; C \cdot f(xs) \;+\; D \cdot n\,(1 + \lfloor \log_2 n \rfloor),$$

where $n$ = `t.size`. The second term is a **startup allowance**: it pays for an arbitrary initial tree, and it plays the role of the $O(n \log n)$ term in Sleator and Tarjan's theorems.

## The working-set bound

The working-set number of a request measures how recently its key was last requested, counted in distinct keys:

@decl RotationBST.workingSetNumber

For a request `x` with history `past` (oldest first):

- If `x` has not been requested before, its number is `n`, the number of keys in the tree.
- Otherwise, `past.reverse.takeWhile (· != x)` is the list of requests made since the most recent request for `x`, most recent first. `eraseDups` removes repetitions, so its length is the number of **distinct** keys requested since then. The working-set number is one more than that.

An immediately repeated request therefore has number $1$, and in general the number is at most $n$.

::: check
- `!=` is the Boolean inequality given by `BEq Nat`, which agrees with `≠` on natural numbers. `takeWhile` stops at the most recent occurrence of `x` and does not include it.
- The $+1$ counts `x` itself. With it the number equals Sleator and Tarjan's $t(j) + 1$, where $t(j)$ is the number of distinct keys accessed since the last access of $x_j$. Iacono's convention, the size of the working set including $x_j$, is the same quantity.
- **First accesses.** Sleator and Tarjan let $t(j)$ be the number of distinct keys accessed before $j$ when $x_j$ is new; the library uses $n$ instead. This charges at most $1 + \lfloor\log_2 n\rfloor$ for each of at most $n$ first accesses, a total that the startup allowance $D\,n(1+\lfloor\log_2 n\rfloor)$ already absorbs. The two conventions give the same property.
:::

@decl RotationBST.workingSetSum

The working-set sum charges each request $1 + \lfloor \log_2 w \rfloor$, where $w$ is its working-set number. The $1+$ is needed: an immediate repeat has $\log_2 1 = 0$ but still costs a comparison. The floor is harmless, since $1 + \lfloor\log_2 w\rfloor$ and $\log_2(w+1)$ are within a factor of $2$ of each other for $w \ge 1$. Like `runFrom`, the recursion appends each request to the history after charging it.

@viz workingset {"n": 8, "finger": 3, "requests": [3, 5, 3, 1, 5, 5, 0, 3, 7, 3]}

The property:

@decl RotationBST.HasWorkingSetBound

Read: there are natural constants $C, D$ such that for every initial tree and every valid sequence, the **rotation count** of the algorithm is at most $C \cdot{}$`workingSetSum` plus the startup allowance. This is Theorem 4 of Sleator and Tarjan (the working-set theorem) as a property of an arbitrary algorithm, with the constants left existential.

::: check
- The cost is `a.cost` (rotations), not `a.totalCost`. Since every request contributes at least $1$ to `workingSetSum`, the two versions are equivalent; see the next theorem.
- The constants are uniform over all initial trees, sizes and sequences. The working-set sum is computed with the size of the initial tree, `t.size`, which never changes.
- Validity `∀ x ∈ xs, x < t.size` is a hypothesis, so the property says nothing about invalid requests.
:::

Adding the request count does not change which algorithms have the property.

**Theorem (rotations or total cost).** An algorithm has the working-set bound if and only if there are constants $C, D$ such that its total cost, rotations plus one per request, is at most $C \cdot \mathtt{workingSetSum} + D\,n(1 + \lfloor\log_2 n\rfloor)$ for every initial tree and every valid sequence.

@decl RotationBST.workingSet_totalCost_iff

The proof uses `xs.length ≤ workingSetSum n past xs`, which holds because every term of the sum is at least $1$. Going from rotations to total cost changes $C$ to $C+1$; the other direction keeps the constants. In contrast with [dynamic optimality](online.html#dynamic-optimality), the normalization is harmless here because the benchmark already charges every request.

## Static optimality

Let $q_x$ be the number of times key $x$ occurs in a sequence of length $m$. A static tree in which $x$ has depth about $\log_2(m/q_x)$ serves the sequence in time proportional to $m$ plus the empirical entropy of the access frequencies. The library defines this benchmark directly:

@decl RotationBST.Bounds.staticCost

$$\mathtt{staticCost}(n, xs) \;=\; m + \sum_{x < n} q_x \log_2 \frac{m}{q_x}.$$

::: check
**Zero frequencies.** For a key that never occurs, `xs.count x = 0`, so the term is `0 * Real.logb 2 (m / 0)`. In Lean, `m / 0 = 0` and `Real.logb 2 0 = 0`, and the term is $0$ either way. This matches the usual convention $0 \log(1/0) = 0$, as the docstring says. The sum ranges over all $n$ keys, but only keys that occur contribute.
:::

@decl RotationBST.HasStaticOptimalityBound

The property bounds the **total cost** $T = m + R$, with the same startup allowance as the working-set property. The statement is in $\mathbb R$; the natural-number constants and `t.size.log2` are cast.

::: caveat Compared with the paper
Sleator and Tarjan's Theorem 2 assumes that every key is accessed at least once, and has no startup term: $T = O(m + \sum_x q_x \log(m/q_x))$. The property above allows unused keys, and pays for them, and for the initial tree, with the startup allowance. For splay, [Chapter 9](analysis.html) proves both this property and the paper's form without startup, the latter under the explicit hypothesis that every key occurs.
:::

## Static finger

Fix a key $f$, the finger. Requests close to $f$ in rank should be cheap:

@decl RotationBST.Bounds.fingerCost RotationBST.HasStaticFingerBound

Each request costs $1 + \log_2(|x - f| + 1)$, where `Nat.dist x f` is $|x - f|$ on natural numbers. Distance is **rank distance**, the number of keys between $x$ and $f$, not a difference of key values. With the implicit-key model this is the only meaningful choice, and it is the distance used in Sleator and Tarjan's Theorem 3, where items are numbered $1, \dots, n$ in symmetric order.

::: check
The quantifier order matters. The constants $C, D$ come first, and then the bound holds for every finger `f < t.size`. A single algorithm with fixed constants competes with **every** finger simultaneously, as in the paper. The algorithm itself never learns `f`.
:::

## Dynamic finger

The dynamic finger bound replaces the fixed finger by the *previous* request: a request is cheap when it is close in rank to the one before it. The library defines the benchmark as a sequence function:

@decl RotationBST.Bounds.dynamicFingerCostFrom

`dynamicFingerCostFrom p xs` charges each request $x_i$ the amount $1 + \log_2(|x_i - x_{i-1}| + 1)$, with a real base-two logarithm, where $x_0 = p$ is an explicitly supplied predecessor of the first request. The unit makes an immediately repeated request cost $1$, as in every other benchmark of this chapter. The bound was proved for splay trees by Cole, Mishra, Schmidt and Siegel (2000); that proof is not in the library, and there is no `Has…Bound` property for this benchmark. The library proves it instead for GreedyASS ([Chapter 23](greedy-finger.html)), and for the optimal lazy-finger tree ([Chapter 15](lazy-finger-hierarchy.html)), where it is the unit-weight case of the weighted dynamic finger bound of [Chapter 14](lazy-finger.html).

## The unified charge

Sleator and Tarjan's Theorem 5 combines the three localities: each access is charged the *smallest* of its three logarithmic costs. The library defines this benchmark in `Bounds/Unified/Abstract.lean`, next to the others, so that the bound is a property of a sequence and not of splaying:

@decl RotationBST.Bounds.unifiedCharge RotationBST.Bounds.unifiedSum

For a request $x$ with history `past`, `unifiedCharge` is
$$1 + \min\Bigl(\log_2 \texttt{workingSetNumber},\; \log_2\frac{m}{q_x},\; \log_2(|x - f| + 1)\Bigr).$$
Frequencies come from the **whole** sequence `original`, so $m$ is its length and $q_x$ the number of occurrences of $x$ in it. Recency comes from the prefix `past`, which `unifiedSum` extends one request at a time while keeping `original` fixed. This mixes offline information (frequencies) with online information (recency), as the paper's bound does. An algorithm measured against it still sees only the past; the frequencies are used by the analysis alone.

::: check
- These logarithms are real: `Real.logb 2 (workingSetNumber …)` is not the floor used in `workingSetSum`.
- If $x$ did not occur in `original`, then $q_x = 0$, `m / 0 = 0` in Lean, and `logb 2 0 = 0`, so the minimum could collapse to $0$. Theorems apply it as `unifiedSum n f xs [] xs`, so `original` is the very sequence being summed over, and every $x$ occurs in it.
- Since the minimum is taken per access, `unifiedSum` is at most each of the three earlier sums up to constants, and can be much smaller than all of them: a sequence that alternates between a hot spot near $f$ and a small working set far away is cheap for one charge on one half and for another on the other half.
:::

Splaying satisfies this bound ([[RotationBST.Splay.Results.unified]], [Chapter 14](analysis.html#the-unified-theorem-theorem-5)). The library defines no `Has…Bound` property for it, because no implication involving it is proved.

## Comparison with a fixed tree

Static optimality is usually explained as "as good as the best fixed BST for the access frequencies". The library makes the comparison literal. First, a fixed tree's search cost:

@decl RotationBST.StaticTree.cost

`cost` charges each request one unit plus its depth, the number of edges from the root to the requested rank ([[RotationBST.Tree.depth]], defined in [Chapter 1](shapes.html#depth)).

This benchmark is exactly the cost of an actual pointer-machine execution that never restructures.

**Theorem (a fixed tree is a pointer execution).** For every tree `t` and every valid sequence `xs`, there is a pointer-machine execution that serves `xs` from `t`, ends in `t`, and costs exactly `StaticTree.cost t xs`.

@decl RotationBST.StaticTree.Results.pointer_execution

Each request is served by walking down `depth t x` edges, visiting `x`, and stopping. That is `Pointer.Serves t t x (depth t x + 1)` in the [pointer model](pointer.html), with the unit request charge. The next search starts again at the root, and returning there is free in that model. The final tree is `t` itself.

Entropy is a lower bound on the cost of every fixed tree, up to a factor of $3$.

**Theorem (entropy lower bound).** For every tree `t` and every valid sequence `xs`, $\mathtt{staticCost}(n, xs) \le 3 \cdot \mathtt{cost}(t, xs)$, where $n$ is the size of `t`.

@decl RotationBST.StaticTree.Results.entropy_lower_bound

The proof is the prefix-code argument. Give key $x$ the weight $4^{-(\mathrm{depth}(x)+1)}$, two bits for each comparison step, including the final one. These weights sum to at most $1$ in every shape. Gibbs' inequality bounds the entropy by $\sum_x q_x \log_2(1/w_x) = 2 \cdot \mathtt{cost}$, so $\mathtt{staticCost} \le m + 2\,\mathtt{cost} \le 3\,\mathtt{cost}$.

The bound is tight up to that factor: some fixed tree achieves the entropy bound itself.

**Theorem (entropy upper bound).** For every $n$ and every sequence `xs` of requests less than $n$, there is a tree `t` on $n$ keys with $\mathtt{cost}(t, xs) \le \mathtt{staticCost}(n, xs)$.

@decl RotationBST.StaticTree.Results.entropy_upper_bound

The constant is one, and there is no additive term. The tree has all $n$ keys, including those never requested, and the statement includes $n = 0$ and the empty sequence, where both sides are $0$. Combined with the lower bound, the best fixed tree for `xs` costs between $\tfrac13\,\mathtt{staticCost}$ and $\mathtt{staticCost}$, which is the classical statement that optimal static trees cost $\Theta(m + \sum_x q_x \log_2(m/q_x))$.

Consequently, a working-set algorithm competes with every fixed BST.

**Theorem (working set beats every fixed tree).** If an algorithm has the working-set bound, then there are constants $C, D$ such that, for every initial tree `t`, every tree `u` of the same size and every valid sequence `xs`, the algorithm's total cost from `t` is at most $C \cdot \mathtt{StaticTree.cost}(u, xs) + D\,n(1 + \lfloor\log_2 n\rfloor)$.

@decl RotationBST.StaticTree.Results.workingSet_competes

Here `t` is the algorithm's initial tree and `u` is any comparison tree of the same size; they need not be equal. The constants are uniform over `t`, `u` and `xs`. The proof goes through static optimality (below) and `entropy_lower_bound`, which turns $C$ into $3C$.

## Implications between the bounds

The following implications hold for every algorithm and use nothing about splaying. They are inequalities between sequence functions, lifted to properties.

**Theorem (implications).** For every algorithm, the working-set bound implies static optimality, and static optimality implies the static finger bound. Hence the working-set bound implies the static finger bound.

@decl RotationBST.Bounds.workingSet_implies_staticOptimality RotationBST.Bounds.staticOptimality_implies_staticFinger RotationBST.Bounds.workingSet_implies_staticFinger

- **Working set ⇒ static optimality.** The key inequality is
  $$\mathtt{workingSetSum}(n, [], xs) \;\le\; \mathtt{staticCost}(n, xs) + n\,(1 + \lfloor\log_2 n\rfloor).$$
  The proof groups the charges by key. Between consecutive accesses to $x$, the working-set number is at most the time elapsed (the gap). The gaps of key $x$ sum to at most $m$, and a finite Jensen inequality bounds $\sum \log_2(\text{gap})$ by $q_x \log_2(m/q_x)$. First accesses are charged to the startup term. The constants become $(C + 1, C + D)$.
- **Static optimality ⇒ static finger.** Apply the weighted entropy inequality with weights $1/(|x-f|+1)^2$, which sum to at most $4$ on both sides of $f$ together. This gives $\mathtt{staticCost} \le 3\,\mathtt{fingerCost}(f)$ for every $f$, and the constants become $(3C, D)$.
- **Working set ⇒ static finger** is the composition.

::: note Why these are separate theorems
In Sleator and Tarjan's paper, Theorems 2 and 3 are proved directly from the access lemma, with suitably chosen weights. The library instead proves the working-set theorem for splay once and derives static optimality and static finger through these algorithm-independent implications. The splay-specific sharper forms, without startup when every key occurs, are proved separately in [Chapter 9](analysis.html).
:::

## Transfer to the pointer machine

Working-set guarantees proved in the rotation model also hold for the causal pointer simulation of [Section 6.6](pointer.html#running-an-online-algorithm-on-the-pointer-machine).

**Theorem (working set on the pointer machine).** If an algorithm has the working-set bound in the rotation model, then there are constants $C, D$ such that its online pointer-machine implementation costs at most $C \cdot \mathtt{workingSetSum} + D\,n(1 + \lfloor\log_2 n\rfloor)$, for every initial tree and every valid sequence.

@decl RotationBST.Pointer.Lazy.Online.Results.workingSet

The left-hand side is the cost of the online pointer implementation of `a`, including requests and every pointer instruction. Postponed rotations are not executed at the end, and they need not be: the pointer execution serves every request without them. The proof combines `simulation` ($\text{pointer cost} \le 32R + 17m$) with the hypothesis on $R$ and with $m \le \mathtt{workingSetSum}$, giving constants $(32C + 17, 32D)$. The constants hold for every algorithm, independently of $n$. For splaying specifically, [Chapter 8](splay.html) gives a more direct pointer implementation with better constants.

## What is not formalized

Two well-known results are absent. The **dynamic finger** theorem for splay trees (Cole, Mishra, Schmidt and Siegel, 2000) is not in the library: its proof is long. The benchmark itself is defined above, and other structures are proved to meet it. **Iacono's unified bound** replaces the fixed finger by the distance to recently accessed keys; it is open whether splay trees satisfy it. Both are mentioned here only to place the formalized bounds. The lower-bound side of Part II is [Chapter 11](wilber.html).

