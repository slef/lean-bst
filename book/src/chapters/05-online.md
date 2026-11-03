# Online algorithms and cost

An [`Execution`](accesses.html#executions) describes every legal way to serve a sequence: it is an offline object that knows the whole sequence in advance. A BST *algorithm* must decide what to do with each request when that request arrives. This chapter defines online algorithms in the rotation model, their two cost measures, and dynamic optimality. [Chapter 6](pointer.html#running-an-online-algorithm-on-the-pointer-machine) shows that any such algorithm can be run online on a conventional pointer machine, with constant overhead.

## Online algorithms

@decl RotationBST.Algorithm

An `Algorithm` is a function together with a certificate.

- `step past t x` receives the requests served so far (`past`, oldest first), the current tree `t` and the current request `x`. It returns the next tree and a rotation count. It receives nothing about future requests, and this is the only sense in which the algorithm is *online*.
- `correct` certifies that whenever `x` is an existing rank, the returned pair is a legal [root access](accesses.html#root-accesses): `x` ends at the root, and the returned count is the exact length of some rotation sequence from `t` to the new tree.

::: check
- **The cost cannot be under-reported.** `Access` requires a rotation sequence of exactly the returned length, so the count is at least the rotation distance between the two trees. An algorithm could report more than it needs to (rotating back and forth), but never less.
- **No persistent state except the tree, but full history.** There is no separate memory field. Any auxiliary state an algorithm might keep, such as counters, preferred children or timestamps, is a function of the request history, which `step` receives in full. Recomputing it costs nothing, since **computation is uncharged**: only rotations count. The interface is therefore more permissive than a pointer machine with $O(1)$ words per node, which is the right direction for lower bounds and for definitions of optimality. Splaying ([Chapter 8](splay.html)) ignores `past` entirely.
- **Invalid requests are outside the contract.** For `x ≥ t.size`, `step` may return anything and `correct` says nothing. Every theorem about runs carries the hypothesis `∀ x ∈ xs, x < t.size`.
:::

Running an algorithm threads the tree through the sequence and adds the counts:

@decl RotationBST.Algorithm.runFrom RotationBST.Algorithm.cost

`runFrom past t xs` serves `xs` starting from history `past`. Each request is appended to the history after it is served (`past ++ [x]`), so the step for the $j$-th request sees exactly the requests before it. `cost` starts with an empty history and keeps only the total number of rotations.

The simplest instance is [[RotationBST.moveToRootAlgorithm]]: it ignores the history and rotates the requested key up one level at a time, the witness used in [Chapter 3](accesses.html#which-requests-can-be-served). It opens Part III in [Chapter 12](move-to-root.html). Splaying ([Chapter 13](splay.html)) is the main example.

A run of an algorithm on valid requests is one of the executions of [Chapter 3](accesses.html#executions). Online algorithms are therefore a special case of offline executions, and their cost is at least the offline optimum:

@decl RotationBST.Algorithm.execution

The proof is an induction on `xs` that applies `correct` at every step. Sizes are preserved, so validity with respect to the initial tree remains validity at every later step.

## Two cost measures

`Algorithm.cost` counts rotations only. The conventional cost of a BST algorithm charges each request at least one unit, for the comparison at the node that holds the key:

@decl RotationBST.Algorithm.totalCost

We write $R$ for `a.cost t xs`, $m$ for `xs.length` and $T = m + R$ for `a.totalCost t xs`. The two measures differ in an essential way. A request for the current root costs $0$ rotations, so a sequence of $m$ such requests has $R = 0$ and $T = m$. A bound of the form $R \le C \cdot f + D$ therefore cannot be obtained from a bound on $T$ when $f$ can be smaller than $m$. The bounds in [Chapter 7](bounds.html) charge every request at least one unit, so for them the two measures are interchangeable ([[RotationBST.workingSet_totalCost_iff]]).

## Dynamic optimality

Sleator and Tarjan conjectured that splay trees are *dynamically optimal*: on every sequence, their cost is within a constant factor of the best offline BST algorithm, up to an additive term that depends only on $n$. The library states both versions of this property, one for each cost measure.

@decl RotationBST.DynamicallyOptimal RotationBST.TotallyDynamicallyOptimal

Read the quantifiers in order. There exist constants $C, D$; then for every initial tree `t`, every sequence `xs` and every offline execution of `xs` from `t` with any cost `k`, the algorithm's cost on `xs` from `t` is at most $C\,k + D\,n$, where $n$ = `t.size`.

::: check
- **Comparison against every execution, hence against the optimum.** Quantifying over all executions `Execution t xs u k` is equivalent to comparing with the least such `k`, so the definition never needs to compute the offline optimum. The final tree `u` of the offline strategy is unconstrained.
- **Same initial tree.** The offline strategy starts from the same `t` as the algorithm. The additive term is linear in $n$, as in the usual statement of the conjecture. By [[RotationBST.Geometry.reset]], allowing the offline strategy to choose its own initial tree would change its cost by at most $2n$, so this choice does not matter.
- **Uniform constants.** $C$ and $D$ are fixed before the tree and the sequence are chosen. In particular, they cannot depend on $n$.
- **Invalid sequences are vacuous.** If some request is out of range there is no `Execution` at all ([[RotationBST.execution_exists_iff]]), so the condition holds trivially.
- `DynamicallyOptimal` compares rotation counts $R \le C\,k + D\,n$, while `TotallyDynamicallyOptimal` compares total costs $T \le C(m + k) + D\,n$. The total-cost version is the conventional notion of dynamic optimality, and it is the one that transfers to the pointer machine ([Section 6.5](pointer.html#running-an-online-algorithm-on-the-pointer-machine)).
:::

The rotation-only notion implies the conventional one:

@decl RotationBST.DynamicallyOptimal.total

The proof takes the constants $(C+1, D)$: add $m$ to both sides. The converse is deliberately not claimed. It holds only if no totally dynamically optimal algorithm exists, which is the open question itself. Suppose `a` is totally dynamically optimal, and let `a'` behave like `a` but, on every request, first rotate a child of the root up and back down. Then `a'` costs at most $T + 2m \le 3T$, so it is still totally dynamically optimal. But on $m$ requests for the root of a tree with at least two nodes, `a'` performs at least $2m$ rotations, while the offline execution that does nothing performs $0$. No bound $2m \le C \cdot 0 + D\,n$ holds for all $m$, so `a'` is not `DynamicallyOptimal`.

::: caveat Not claimed for splay
Neither `DynamicallyOptimal` nor `TotallyDynamicallyOptimal` is proved for any algorithm in the library. The dynamic optimality conjecture is open. The theorems that mention it, such as the pointer-machine transfer of [Section 6.5](pointer.html#running-an-online-algorithm-on-the-pointer-machine), are conditional: *if* an algorithm satisfies the property, *then* some consequence follows. [Chapter 11](wilber.html) proves Wilber's lower bound on the offline optimum, and [Chapter 19](tango.html) uses it to show that Tango trees are $O(\log \log n)$-competitive, the best ratio known.
:::
