# Online algorithms and cost

An [`Execution`](accesses.html#executions) describes every legal way to serve a sequence: it is an offline object that knows the whole sequence in advance. A BST *algorithm* must decide what to do with each request when that request arrives. This chapter defines online algorithms in the rotation model, their two cost measures, and dynamic optimality. Its last section shows that any such algorithm can be run on the [pointer machine](pointer.html) online, with constant overhead.

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

The baseline [[RotationBST.moveToRoot]] from [Chapter 3](accesses.html#which-requests-can-be-served) is an algorithm. It ignores the history, and its certificate is the correctness lemma `moveToRoot_correct`:

@decl RotationBST.moveToRootAlgorithm

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
- `DynamicallyOptimal` compares rotation counts $R \le C\,k + D\,n$, while `TotallyDynamicallyOptimal` compares total costs $T \le C(m + k) + D\,n$. The total-cost version is the conventional notion of dynamic optimality, and it is the one that transfers to the pointer machine (below).
:::

The rotation-only notion implies the conventional one:

@decl RotationBST.DynamicallyOptimal.total

The proof takes the constants $(C+1, D)$: add $m$ to both sides. The converse is deliberately not claimed. It holds only if no totally dynamically optimal algorithm exists, which is the open question itself. Suppose `a` is totally dynamically optimal, and let `a'` behave like `a` but, on every request, first rotate a child of the root up and back down. Then `a'` costs at most $T + 2m \le 3T$, so it is still totally dynamically optimal. But on $m$ requests for the root of a tree with at least two nodes, `a'` performs at least $2m$ rotations, while the offline execution that does nothing performs $0$. No bound $2m \le C \cdot 0 + D\,n$ holds for all $m$, so `a'` is not `DynamicallyOptimal`.

::: caveat Not claimed for splay
Neither `DynamicallyOptimal` nor `TotallyDynamicallyOptimal` is proved for any algorithm in the library. The dynamic optimality conjecture is open. The theorems below and in [Chapter 7](bounds.html) are conditional: *if* an algorithm satisfies the property, *then* some consequence follows.
:::

## Running an online algorithm on the pointer machine

[Chapter 5](pointer.html) shows that a rotation execution with $R$ rotations and $m$ requests can be simulated by a pointer execution whose cost $C$ and final deferred suffix $d$ satisfy $C + 32d \le 32R + 17m$. The lazy simulation behind this bound reorders rotations and postpones those that the current request does not need. That is an offline construction: it takes a whole execution as input. This section shows that the simulation can also be run *online*: each pointer step depends only on the past, the current request and a simulation state. Every online rotation-model algorithm therefore yields an online pointer algorithm with constant overhead.

The simulator maintains two trees:

@decl RotationBST.Pointer.Lazy.Online.State RotationBST.Pointer.Lazy.Online.initial

`virtual` is the tree that the rotation-model algorithm believes it has. `current` is the tree actually present in the pointer machine. The `pending` rotations that the pointer machine has not yet performed separate them, and `certificate` proves this (`Rotations current virtual pending`). Initially both trees are the input tree and nothing is pending. The state contains no future requests.

One step of the simulation is specified as a relation:

@decl RotationBST.Pointer.Lazy.Online.Transition

Given state `s` and request `x`, a result `(s', c)` is a valid transition when:

1. the pointer machine serves `x` from `s.current`, ending at `s'.current` and paying `c` ([[RotationBST.Pointer.Serves]], which includes the unit request charge);
2. the new virtual tree is exactly what the algorithm's own step produces from the old virtual tree, so the algorithm runs unmodified on its own view; and
3. an amortized bound holds with potential $32 \cdot{}$`pending`: the actual cost plus the new potential is at most $32$ times the old pending work plus the algorithm's rotations, plus $17$.

Every valid request admits such a transition. This is the per-request form of the lazy simulation of [Chapter 5](pointer.html):

@decl RotationBST.Pointer.Lazy.Online.advance_exists

The simulator *chooses* one transition:

@decl RotationBST.Pointer.Lazy.Online.advance RotationBST.Pointer.Lazy.Online.run

`advance` picks a transition with `Classical.choose`, so it is `noncomputable`. It is a mathematical function of `(a, past, s, x)`, not an executable program. An invalid request leaves the state unchanged at cost $0$; it is never reached by the theorems below, which assume validity. `run` threads the state through the sequence and appends each request to the history, exactly like [[RotationBST.Algorithm.runFrom]].

::: caveat Uncharged planning
Choosing the pointer instructions requires knowing a valid transition, and finding one involves the lazy-simulation construction on the current pending rotations. As in the rotation model, this planning is not charged. The cost bound counts pointer instructions and requests only. The library's README states this explicitly.
:::

The main theorem, from the initial state:

@decl RotationBST.Pointer.Lazy.Online.Results.simulation

The three conjuncts say:

1. **Legality.** The chosen instructions form a pointer execution serving `xs` from `t`, with final pointer tree `(run …).1.current` and cost `(run …).2`.
2. **Agreement up to the deferred suffix.** The final pointer tree reaches the final tree of the rotation-model algorithm by exactly `pending` rotations. The two executions end in the same place, except for work that has been postponed and not yet paid for.
3. **Cost.** Pointer cost plus $32$ times the pending suffix is at most $32R + 17m$, where $R$ is the algorithm's rotation count. In particular the pointer cost alone is $O(R + m) = O(T)$, with constants independent of $n$.

Causality is visible in the types (`advance` never receives the future), and the library also states it as a theorem:

@decl RotationBST.Pointer.Lazy.Online.Results.prefix_composition

Running on `xs ++ ys` is the same as running on `xs`, then continuing from the resulting state with history `past ++ xs`. The state and cost after the prefix `xs` are therefore the same for every continuation `ys`. Nothing computed for the first requests can depend on later ones, so there is no lookahead.

Finally, the property this transfer was built for:

@decl RotationBST.Pointer.Lazy.Online.Results.dynamicOptimality

If an algorithm is dynamically optimal in the normalized rotation model, then its causal pointer implementation competes, with uniform constants, against **every offline pointer execution** `Pointer.Execution t xs u k`. Both sides of this comparison are in the pointer model. The proof composes three bounds: an offline pointer execution of cost $k$ yields a rotation execution of total cost at most $3k$ ([[RotationBST.Pointer.Results.to_rotations]]); total dynamic optimality bounds the algorithm by that execution; and `simulation` bounds the pointer cost by the algorithm's rotation-model cost. The resulting constants are $(96C, 32D)$.

::: check
Conventional dynamic optimality is a statement about pointer-model algorithms competing with pointer-model optima. This theorem says that a proof of `TotallyDynamicallyOptimal` for any rotation-model algorithm would give exactly that: an online pointer algorithm that is dynamically optimal in the conventional sense. The hypothesis is the total-cost notion. The rotation-only `DynamicallyOptimal` is stronger, and is never needed.
:::

The working-set transfer [[RotationBST.Pointer.Lazy.Online.Results.workingSet]] has the same shape. It is stated in [Chapter 7](bounds.html#transfer-to-the-pointer-machine), after the working-set bound is defined.
