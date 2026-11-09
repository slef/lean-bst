# The combination theorem

Different BST algorithms are good on different sequences. Splay trees have the working-set and dynamic-finger bounds, Tango trees are $O(\log\log n)$-competitive, GreedyASS is competitive with the best lazy-finger tree, and no single analysis gives all of these at once. Demaine, Iacono, Langerman and Özkan [-@demaine2013] showed that this is no obstacle: given two online BSTs $A_0$ and $A_1$, one online BST costs, on every sequence and in fact on every contiguous window of every sequence, at most a constant times the cheaper of the two, plus an additive overhead. Their construction, *ComboBST*, runs the two algorithms in alternating rounds of fixed length, each round starting again from a saved copy of the initial tree, and it simulates the extra fingers it needs inside a single-finger BST.

This section is the entry point to the formalization of that paper. It states the abstract counterpart of the paper's Theorem 3 and its extension to finite families, explains the hypotheses carefully, and develops the part of the proof that is pure accounting: well-behaved charges, the counting of rounds, and the window bounds. The machinery that makes the combination a real pointer-machine execution is in the next three sections and in [Chapter 50](tree-state.html), in [Part V](part-structures.html).

```headline combo-two
title: One online BST is as good as the better of two, on every window
source: @demaine2013
key: yes
theorems: Combo.Online.Results.window_policy

This is the abstract BST-operation counterpart of Theorem 3 of the paper. Fix a nonempty initial tree $S$ with $n$ keys. Let $A_0$ and $A_1$ be two interruptible online algorithms starting from $S$, each with a pointer-machine interpretation and a request-correctness contract, and let $\tau_0$, $\tau_1$ be nonnegative amortized charges, where $\tau_s(X, i)$ is the charge of the $i$-th request of the whole sequence $X$. Assume that both charges are **well-behaved** for their algorithms with a common overhead $F$ and constants $C_0, C_1$, and that

$$n \le F.$$

Then there is one online pointer policy, chosen before any request is known, such that for every sequence $X = x_0, \dots, x_{m-1}$ of keys in $\{0, \dots, n-1\}$ its run from $S$ is a legal pointer execution serving $X$, and for every window $0 \le lo \le hi \le m$ the run splits exactly into the part before $lo$, the window, and the part after $hi$, with additive costs. The window part is a legal pointer execution of $x_{lo}, \dots, x_{hi-1}$ between the trees the run actually reaches, and its cost is at most

$$8384\,(C_1 + 58)\Bigl(2\,C_0^2 \min\Bigl(\sum_{lo \le i < hi} \tau_0(X, i),\ \sum_{lo \le i < hi} \tau_1(X, i)\Bigr) + (2\,C_0 C_1 + 73)\,F\Bigr).$$

The charges in the bound are those of the original sequence, at the original indices, with its whole history: the window is not rerun from $S$. Costs are pointer-machine costs, one per request plus one per instruction, so they include rotations and moves. Preparation of the saved snapshot is paid once, on the first request, and is absorbed in the overhead; the window $lo = 0$, $hi = m$ is the whole run.

In Lean, the algorithms are one [[Combo.Controller.Worker]] with a side bit, its interpretation is a [[Combo.Refinement.WorkerModel]] with [[Combo.Refinement.Visits.Correct]], well-behavedness is [[Combo.Analysis.WellBehaved]], the window charge is [[Combo.Analysis.mass]], the policy is an [[Combo.Online.Prepared]] run by [[Combo.Online.execute]], and legality is [[RotationBST.Pointer.Execution]].
```

```headline combo-family
title: One online BST is as good as the best of a finite family, on every window
source: @demaine2013
theorems: Combo.Family.Physical.Results.finite_policy

The paper combines $k$ algorithms two at a time in a balanced binary tree (Section 1.2). Fix a nonempty initial tree $S$ with $n$ keys and a nonempty finite family $A_1, \dots, A_k$ of interruptible algorithms on $S$, possibly with different state types, each with a pointer interpretation and request correctness, and each well-behaved for its own charge $\tau_j$, with common $F \ge n$, $C_0$ and $C_1$. Let $d = \lceil \log_2 k \rceil$. Then there is one online pointer policy such that for every valid sequence $X$ its run from $S$ is legal, its total cost is at most $\alpha \min_j \sum_i \tau_j(X, i) + \beta F$, and for every window $[lo, hi)$ the run splits additively as in the box above and the window costs at most

$$\alpha \, \min_{j} \sum_{lo \le i < hi} \tau_j(X, i) \;+\; \beta\, F,$$

with $\alpha = 8384\,(C_1 + d + 58)\cdot 2C_0^2\cdot S_d$ and $\beta = 8384\,(C_1 + d + 58)\,(2C_0(C_1 + d) + 73)\cdot O_d$. The scales start at $S_0 = O_0 = 1$ and grow by one factor per level of the combination tree, $S_{j+1} = 33536\,C_0\,(C_1 + j + 58)\,S_j$ and $O_{j+1} = \bigl(33536\,C_0\,(C_1 + j + 58) + 16768\,(5(C_1 + j) + 301) + 1\bigr)\,O_j$. For fixed $k$, $C_0$ and $C_1$ these are constants, as in the paper; they are not the paper's sharper $O(k)$.

In Lean, the family is a function into [[Combo.Family.Algorithm]], the scales are [[Combo.Family.chargeScale]] and [[Combo.Family.overheadScale]], and the guarantee is [[Combo.Family.Physical.Bounded]].
```

The section has two layers. To confirm the results, the boxes are enough, together with the reading list on the [checking page](checking.html). Be aware that much of what the statements mention is a *hypothesis* about the input algorithms, not something the theorems prove: [Section 33.2](#what-is-assumed-and-what-is-proved) lists precisely what a caller has to supply. To see why the results hold, read on. [Section 33.1](#the-construction-at-a-glance) is a map of the whole construction across chapters, [Section 33.3](#well-behaved-charges) gives the definition at the heart of both theorems, [Section 33.4](#charging-the-rounds) and [Section 33.5](#windows) prove the round-counting argument of the paper at the level of the controller, [Section 33.6](#charges-of-the-original-sequence) gives the two concrete charges used in [Chapter 38](combined-finger.html), and [Section 33.7](#finite-families) builds the families.

The definitions of this section are in `Algorithms/Combination/Analysis/Definitions/Abstract.lean`, `Charges/Definitions/Abstract.lean`, `Family/Definitions/Abstract.lean` and `Family/Physical/Definitions/Abstract.lean`; the theorems are in the `Abstract.lean` files next to them.

## The construction at a glance

ComboBST is built in layers, and the library follows the paper's layers closely. Each layer has its own page.

```
 A₀, A₁   interruptible workers: one charged step at a time      {{ref:combo-workers}}
   │
   ▼
 controller: rounds of budget (C₁+1)·F, alternating A₀ and A₁,   {{ref:combo-rounds}}
 each round restarting from the saved initial tree
   │              accounting: well-behaved charges, rounds,      this section
   │              windows
   ▼
 save and restore the initial tree in O(n) operations             {{ref:tree-state}}
   │
   ▼
 one pointer execution: the controller, the snapshot finger and   {{ref:combo-online}}
 the worker's finger on a single tree, simulated with one finger  (and {{num:finger-hands}})
   │
   ▼
 Theorem 3 on every window  ──►  finite families  ──►  Theorem 4.3   this section,
                                                                     {{ref:combined-finger}}
```

**Workers** ([Chapter 34](combo-workers.html)). The paper's input is two online BSTs $A_0$, $A_1$. ComboBST must be able to stop either of them in the middle of a request, after a fixed number of operations, and later throw the partial work away. The library therefore takes the inputs as *interruptible workers*: a [[Combo.Controller.Worker]] has a restart state for each side and a `step` function that performs one charged unit of work on the current request and reports whether the request is finished. A complete standalone request is [[Combo.Worker.Access]], and a standalone run from the restart state is [[Combo.Worker.Requests]]. Two algorithms with different state types are packed into one worker by [[Combo.Worker.Pair.worker]].

**Rounds** ([Chapter 35](combo-rounds.html)). This is Section 4 of the paper. Each round runs one worker, from the initial tree, for at most $C_3 f(n)$ operations. When the budget runs out in the middle of request $x_i$, ComboBST restores the initial tree, switches to the other worker and re-runs $x_i$ there. In the library, $C_3 f(n)$ is the budget [[Combo.Analysis.budget]]` F C₁` $= (C_1 + 1) F$, the restore is charged an explicit $57F$ in the final theorem, and one request is served by [[Combo.Controller.serve]]: one attempt with the remaining budget, then, if it fails, a fresh attempt on the other side with the full budget. The paper's choice $C_3 > C_1$ guarantees that a fresh round always completes its first request, so the second attempt never fails.

**Snapshots** ([Chapter 50](tree-buffers.html) and [Chapter 51](snapshots.html)). This is Section 3 of the paper: with $O(\log n)$ bits per node, a tree can store a description of another tree on the same keys, and saving or loading it takes $O(n)$ operations (Lemmas 9 and 10). The library's tree buffers and snapshots implement these scans, including scans interleaved with rotations by another finger.

**One online execution** ([Chapter 36](combo-online.html)). This is Section 2 and Definition 12 of the paper. The controller, the worker's finger and the snapshot finger are refined onto shared nodes of one tree, and the two fingers are simulated by a single pointer with the finger hands of [Chapter 43](finger-hands.html). Each controller step costs at most $8384$ pointer operations, amortized. The result is a prepared policy, chosen once, whose execution [[Combo.Online.execute]] is a legal [[RotationBST.Pointer.Execution]].

**Windows and families** (this section). The paper's Section 5 counts the rounds. The analysis below proves its bound for the controller, on every prefix and on every window. [Chapter 36](combo-online.html) transfers it to the physical execution, which gives the first box. The finite families of the second box nest the construction: the combined policy is replayed as a new worker and combined again.

**Applications** ([Chapter 38](combined-finger.html)). Theorem 4.3 of Iacono and Langerman combines GreedyASS with Tango through this construction and then deamortizes the result ([Chapter 37](deamortization.html)).

| Paper | Library | Section |
|---|---|---|
| Definition 2, well-behaved bounds | [[Combo.Analysis.WellBehaved]] | this one |
| Section 4, rounds of $C_3 f(n)$ operations | [[Combo.Controller.serve\|Controller.serve]], [[Combo.Analysis.budget\|budget]] | [Chapter 35](combo-rounds.html) |
| Section 5, proof of Theorem 13 | [[Combo.Analysis.Results.minimum_bound\|minimum_bound]], [[Combo.Analysis.Results.window_minimum\|window_minimum]] | this one |
| Section 3, Lemmas 9 and 10 | tree buffers and snapshots | [Chapter 50](tree-buffers.html), [Chapter 51](snapshots.html) |
| Section 2, Theorem 5 | finger hands, refinement, online policy | [Chapter 43](finger-hands.html), [Chapter 36](combo-online.html) |
| Theorem 3 | [[Combo.Online.Results.window_policy\|window_policy]] | [Chapter 36](combo-online.html) (stated here) |
| Section 1.2, $k$ algorithms | [[Combo.Family.Physical.Results.finite_policy\|finite_policy]] | this one |

## What is assumed and what is proved

The first box has the shape *if the inputs satisfy these contracts, then there is a policy with this bound*. Every contract is an explicit hypothesis of [[Combo.Online.Results.window_policy]]. None is automatic for an arbitrary BST algorithm, and a reader who wants to apply the theorem has to prove each of them for the algorithms at hand.

**Supplied by the caller.**

1. **The workers.** A [[Combo.Controller.Worker]]: a deterministic step function for each side, which sees the current state and request and nothing else. This is the paper's "online" requirement, made operational: a round can be interrupted after any step.
2. **A pointer interpretation.** A [[Combo.Refinement.WorkerModel]]: each step performs one legal pointer instruction or none (local bookkeeping), both sides restart with the cursor at the root of the same saved tree $S$, and the tree keeps its $n$ keys.
3. **Request correctness.** [[Combo.Refinement.Visits.Correct]]: from every request boundary that a standalone run can reach, a completed access visits the requested key among the steps it performs.
4. **Well-behaved charges.** [[Combo.Analysis.WellBehaved]] for the given $F$, $C_0$, $C_1$ and charges ([Section 33.3](#well-behaved-charges)). This includes that the charges bound the actual standalone cost, that each single request from any reachable boundary costs at most $C_1 F$, and that the charges of a window, taken standalone, are close to its charges inside the whole sequence.
5. **Sizes.** The saved tree is nonempty and $n \le F$. The theorem also takes arbitrary initial contents of the per-node fields (`fields`, `oldData`), which the preparation overwrites; the bound holds for every choice.

**Proved by the library.** Everything else: that a fixed preparation exists and costs $O(n)$, that the controller never fails on valid requests, that the single physical execution is legal and visits every requested key, that its cost splits exactly over any window, and the bound itself.

**Which workers are proved to satisfy the contracts.** In this book, two: GreedyASS, well-behaved against the lazy-finger charges of every fixed tree with $C_0 = 1$, $C_1 = 20$ and $F = 46225920\,n$ ([[Geometric.GreedyASS.Combination.Results.greedy_worker]]), and Tango with linear startup, well-behaved against interleave charges of the balanced reference with $C_0 = 1$, $C_1 = 20$ and $F = 2816\,n$ ([[Tango.Combination.Results.linear_balanced_worker]]). Both are in [Chapter 38](combined-finger.html), with the startup analysis of [Chapter 30](tango-linear.html), and both use the charges of [Section 33.6](#charges-of-the-original-sequence). Splay trees and the other algorithms of Corollary 4 are not provided as workers, so Corollary 4 itself is not a consequence of the library.

::: caveat
The policy is a fixed function of the current state and request, so the combination is online. It is defined with classical choice, and its internal planning is not charged: the abstract pointer model counts pointer operations and requests, not private computation or memory. The storage clauses of the paper ("if $A_0$ and $A_1$ are real-world BSTs, so is ComboBST", with $O(\log n)$ bits per node) are not formalized.
:::

## Well-behaved charges

This section gives the definition that both boxes are built on. It is the paper's Definition 2, made precise in the operational worker model.

### Charges, windows and masses

A charge function gives each request of a sequence an amortized cost, for each of the two sides:

@decl Combo.Analysis.Charges Combo.Analysis.segment Combo.Analysis.mass Combo.Analysis.total

`charges side xs i` is $\tau_{side}(X, i)$, the charge of the $i$-th request when the whole sequence is $X$; side `false` is $A_0$ and side `true` is $A_1$. A charge may depend on the entire sequence, past and future: it is only used in bounds, never by the algorithm. `segment xs lo hi` is the window $x_{lo}, \dots, x_{hi-1}$ as a list of its own. `mass charges side xs lo hi` sums the charges of the original sequence over the indices $[lo, hi)$, which is the paper's $T_{X'}(A, T, X)$ for $X' = $ `segment xs lo hi`. `total` is the mass of the whole sequence.

Two different numbers are attached to a window, and the distinction runs through the whole section:

- `mass charges side xs lo hi`: the requests of the window, charged **as part of $X$**, with their original indices and history;
- `total charges side (segment xs lo hi)`: the window charged **as a sequence of its own**, starting from scratch.

For a working-set charge, for example, the first request of each key inside the window is more expensive standalone than in context. Well-behavedness bounds the second number by the first.

### The definition

@decl Combo.Analysis.WellBehaved

The four fields correspond to the paper's definition as follows. The paper writes $T(A, T, X) = \sum_i \tau(A, T, X, i) + f(n)$ for an upper bound on the running time of $A$ on $X$ from tree $T$; here $f(n)$ is `overhead`, written $F$.

1. `nonneg`: every charge is nonnegative. The paper assumes this implicitly.
2. `single`: from any state that a standalone run of either side can reach on valid requests, every valid request completes, at a cost of at most $C_1 F$ worker steps. This is the paper's "the cost of executing any single access $x_i$ is at most $C_1 f(n)$". It also asserts that the request terminates.
3. `upper`: a standalone run from the restart state on any valid sequence completes all of it, at a cost of at most $\sum_i \tau(X, i) + F$. This is the paper's statement that $T$ bounds the running time.
4. `stable`: for every valid sequence and every window, the window's standalone charge plus $F$ is at most $C_0$ times its mass in the original sequence plus $C_1 F$:
$$\sum_{i} \tau\bigl(X', i\bigr) + F \;\le\; C_0 \sum_{lo \le i < hi} \tau(X, i) + C_1 F, \qquad X' = x_{lo} \dots x_{hi-1}.$$
This is the paper's $T(A, T, X') \le C_0\,T_{X'}(A, T, X) + C_1 f(n)$.

Only `single` and `upper` mention the worker. `nonneg` and `stable` are properties of the charge function alone. The costs in `single` and `upper` are worker steps, which include bookkeeping steps, so they are at least the number of pointer instructions. Both sides share the constants and the overhead; a worker built from two inputs with different constants can use the larger of each, by `overhead_mono` below for $F$ and directly for $C_0$ and $C_1$.

Lean also generates one projection per field, which the proofs use to extract a property from a hypothesis `well : WellBehaved …`:

@decl Combo.Analysis.WellBehaved.nonneg Combo.Analysis.WellBehaved.single Combo.Analysis.WellBehaved.upper Combo.Analysis.WellBehaved.stable

The round budget is fixed in terms of the same constants:

@decl Combo.Analysis.budget

$(C_1 + 1) F$ is the paper's $C_3 f(n)$ with $C_3 = C_1 + 1$, the least integer choice with $C_3 > C_1$. The docstring states the point: the budget strictly exceeds the cost $C_1 F$ of any single request, so that every round finishes at least one request.

### First consequences

**Theorem (fresh rounds complete).** If the charges are well-behaved, then from the restart state of either side, every valid request completes within $C_1 F$ steps.

@decl Combo.Analysis.Results.fresh

[[Combo.Controller.FreshBound]] is the controller's form of this property, stated with the executable [[Combo.Controller.attempt]]. It is what the online contract of [Chapter 36](combo-online.html) requires, and it holds for every larger budget, in particular for $(C_1 + 1) F$.

**Theorem (standalone windows).** If the charges are well-behaved, then a standalone run of either side on any window of a valid sequence completes, at cost at most $C_0$ times the window's original mass plus $C_1 F$.

@decl Combo.Analysis.Results.segment_bound

This is `upper` applied to the window, followed by `stable`. It is the inequality the paper uses for each round: a round runs a contiguous piece of the sequence from the initial tree, which is exactly a standalone run of a window.

**Theorem (larger overhead).** If the charges are well-behaved with overhead $F$ and $C_1 \ge 1$, they are well-behaved with every larger overhead.

@decl Combo.Analysis.Results.overhead_mono

The hypothesis $C_1 \ge 1$ is needed for `stable`, whose right-hand side gains $C_1(F' - F)$ while the left gains $F' - F$. Theorem 4.3 uses this to bring GreedyASS and Tango to a common overhead.

## Charging the rounds

This section proves the paper's main counting argument for the controller ([Chapter 35](combo-rounds.html)), before any pointer machine is involved. Throughout, the budget is [[Combo.Analysis.budget]]` F C₁` and the restore charge is `restoreFactor * F`. A run is a [[Combo.Controller.Execution]], and its rounds are the spans [[Combo.Rounds.spans]] of request positions served by one side between two switches. Consecutive rounds share the interrupted request, which belongs to both.

The argument in the paper is short. Let $A_{\min}$ be the side with the smaller total charge. Every round except the last runs out of budget, so it spends at least $(C_1 + 1) F$ steps on a contiguous piece of the sequence that it could not finish. By the standalone-window bound, finishing that piece would cost at most $C_0$ times its charge plus $C_1 F$. So the piece's charge is at least $F / C_0$. The pieces of one side are disjoint, so there are at most $C_0 \cdot \mathrm{total} / F$ closed rounds of $A_{\min}$, the two sides alternate, and each round costs at most a budget plus a restore.

**Theorem (a closed round is expensive).** In a run from the initial controller state on valid requests, every round except the last has original charge at least $F / C_0$ on its own side.

@decl Combo.Analysis.Results.closed_span_charge

`dropLast` removes the last round, the only one that may end without exhausting its budget. [[Combo.Rounds.Span.charge]] sums the given weights over the span's positions, here `charges span.side xs`, the original charges of the round's side.

**Theorem (few closed rounds).** In the same setting, for either side, the number of closed rounds of that side times $F$ is at most $C_0$ times that side's total charge.

@decl Combo.Analysis.Results.closed_count_bound

This sums the previous inequality over the rounds of one side, which are disjoint ([[Combo.Rounds.Separated]]), and uses `nonneg` to bound the sum of their charges by the total.

For a run that starts in the middle of a round, at an arbitrary controller state, the first round is not fresh. The same bounds hold for the *interior* rounds, those that are neither first nor last:

@decl Combo.Analysis.Results.interior_span_charge Combo.Analysis.Results.interior_count_bound

`dropLast.tail` removes both ends. An interior round starts with a switch, from the restart state with the full budget, which is all the argument needs.

**Theorem (prefix bound, two sides).** For a run from the initial controller state on valid requests, and for either side $s$, the cost is at most $(C_1 + 1 + r)\bigl(2 C_0 \sum_i \tau_s(X, i) + 3F\bigr)$, where $rF$ is the restore charge.

@decl Combo.Analysis.Results.prefix_bound

Each round costs at most its budget $(C_1+1)F$ plus a restore $rF$. The rounds alternate between the sides, so if $c$ is the number of closed rounds of side $s$, the run pays at most $2c + 3$ budgets and restores, and $c F \le C_0 \sum_i \tau_s(X,i)$ by `closed_count_bound`.

**Theorem (prefix minimum).** The cost of such a run is at most $(C_1 + 1 + r)\bigl(2 C_0 \min(\sum_i \tau_0(X, i), \sum_i \tau_1(X, i)) + 3F\bigr)$. Moreover the executable controller [[Combo.Controller.run]] does not fail on valid requests.

@decl Combo.Analysis.Results.minimum_bound Combo.Analysis.Results.execute

`minimum_bound` is `prefix_bound` for the better side. `execute` adds that the executable `run` returns a result and that this result is certified by an `Execution`: by `fresh`, a fresh attempt always completes its request, so the second attempt of [[Combo.Controller.serve]] never fails. Together they are the controller form of the paper's Theorem 13 for prefixes. Its physical counterpart is [[Combo.Online.Results.prefix_policy]].

## Windows

Theorem 3 is about windows: a contiguous piece $X' = x_{lo} \dots x_{hi-1}$ of the online sequence, served **inside** the run on all of $X$. When the window starts, the controller is in whatever state the prefix left it: in the middle of a round, possibly of the worse side, with part of its budget used.

**Theorem (from any state).** For a run of the controller from any state whose remaining budget is at most the round budget, on valid requests, and for either side $s$, the cost is at most $(C_1 + 1 + r)\bigl(2 C_0 \sum_i \tau_s(X, i) + 5F\bigr)$.

@decl Combo.Analysis.Results.state_bound

Compared with `prefix_bound`, the first round is not fresh, so only interior rounds are charged and the additive term grows from $3F$ to $5F$. The hypothesis `limit` excludes states with more budget left than a round can have; every state reached by the controller satisfies it.

**Theorem (window bound).** Let $X$ be a valid sequence and $lo \le hi \le |X|$. Any run of the controller on the window $x_{lo} \dots x_{hi-1}$, from any state whose remaining budget is at most the round budget, costs at most

$$(C_1 + 1 + r)\Bigl(2\,C_0^2 \sum_{lo \le i < hi} \tau_s(X, i) + (2 C_0 C_1 + 5)\,F\Bigr)$$

for either side $s$, and so at most the same with the minimum over the two sides.

@decl Combo.Analysis.Results.window_bound Combo.Analysis.Results.window_minimum

The proof applies `state_bound` to the window as a sequence of its own, which gives its standalone charge `total charges s (segment xs lo hi)`. Then `stable` converts the standalone charge into the original mass: $2C_0\,\mathrm{total}(X') + 5F \le 2C_0\,(C_0\,\mathrm{mass} + C_1 F - F) + 5F \le 2C_0^2\,\mathrm{mass} + (2C_0C_1 + 5)\,F$, where $X'$ is the window. This is where $C_0^2$ and $2C_0C_1$ come from.

**Theorem (the window inside the run).** Let a controller run on a valid sequence $X$ start from a state with remaining budget at most the round budget, and let $lo \le hi \le |X|$. Then the run is the composition of three runs, on $x_0 \dots x_{lo-1}$, on the window, and on $x_{hi} \dots$, each starting where the previous one ended, the costs and switch counts add up exactly, and the window's cost satisfies the bound of `window_minimum`.

@decl Combo.Analysis.Results.executed_window

::: note What the window bound compares
Both sides of the inequality refer to the original run on the original sequence.

- **The cost** is the cost of the middle piece of the actual run, from the state `beforeState` that the actual prefix produced. The window is not rerun from the saved tree, and the controller is not reset at $lo$.
- **The comparator** is the mass of the original charges over the indices $[lo, hi)$: `mass charges side xs lo hi`, where `xs` is the whole sequence. A request of the window is charged as the $i$-th request of $X$, with all of $X$'s history.

Neither side is the cost or the charge of the window as a fresh sequence. The standalone charge only appears inside the proof, as an intermediate step, through `stable`. This is the reading of the paper's $T_{X'}(\text{Combo-BST}, T, X)$, and it is what lets Theorem 4.3 apply the window bound to a comparator, such as an offline execution or a weighted-finger cost, defined on the whole sequence.
:::

The physical counterpart, [[Combo.Online.Results.executed_window]] in [Chapter 36](combo-online.html), has the same shape for the prepared pointer policy. It multiplies the controller cost by $8384$ for the pointer simulation and adds $570112\,n$ for the carried potential of the finger hand, or the preparation when $lo = 0$. With the restore charge $r = 57$ and $n \le F$, this additive term is absorbed: $570112\,n = 8384 \cdot 68\,n \le 8384\,(C_1 + 58) \cdot 68\,F$, which turns $2C_0C_1 + 5$ into $2C_0C_1 + 73$. The result is [[Combo.Online.Results.window_policy]], the theorem of the first box.

**Theorem 3, restated.** For two workers with a pointer interpretation and request correctness, on a common nonempty saved tree with $n$ keys, and charges that are well-behaved with overhead $F \ge n$ and constants $C_0$, $C_1$, there is one prepared policy with budget $(C_1+1)F$ and restore charge $57F$, such that for every sequence of valid keys its execution from the saved tree is a legal pointer execution, and every window $[lo, hi)$ of it is a legal pointer execution between the trees reached at $lo$ and $hi$, with exactly additive costs, of cost at most $8384\,(C_1 + 58)\bigl(2 C_0^2 \min(M_0, M_1) + (2C_0C_1 + 73)\,F\bigr)$, where $M_s$ is the original mass of side $s$ over $[lo, hi)$. Its Lean statement is shown in the first box and in [Chapter 36](combo-online.html).

## Charges of the original sequence

The hypotheses of the first box are about charges. This section provides two concrete charge functions, defined as increments of a cost on prefixes of the original sequence, and proves their well-behavedness properties. [Chapter 38](combined-finger.html) uses them to show that GreedyASS and Tango are well-behaved workers: GreedyASS against lazy-finger charges, Tango against interleave charges.

### Lazy-finger cost on prefixes and windows

Four facts about the lazy-finger cost of [Chapter 15](lazy-finger.html) are needed. Recall that [[LazyFinger.costFrom]]` t p xs` charges each request $1 + d_T(x_{i-1}, x_i)$ with $x_{-1} = p$, and [[LazyFinger.cost]] starts at the root.

@decl LazyFinger.Results.costFrom_append LazyFinger.Results.cost_le_append LazyFinger.Results.cost_take_mono

`costFrom_append` splits a sequence: the second part starts where the first ended, at its last request (or at `p` if the first part is empty, which is `getLastD p`). Since every term is nonnegative, the root-start cost is monotone under extension, and so is the cost of the prefixes `xs.take lo` as `lo` grows.

**Theorem (a window costs its share).** For valid requests and $lo \le hi$, the lazy-finger cost of the window $x_{lo} \dots x_{hi-1}$, as a sequence of its own, is at most the increase of the cost of the prefixes of $X$ from $lo$ to $hi$, plus $|T|$.

@decl LazyFinger.Results.cost_segment

The window alone starts its first search at the root of $T$, while inside $X$ it starts at $x_{lo-1}$. Only the first move differs, and the move from the root costs at most $|T|$. The subtraction is on natural numbers, but it does not truncate, by `cost_take_mono`.

### Lazy-finger charges

@decl Combo.Charges.lazyFinger

`lazyFinger factor t xs i` is $\mathit{factor}\cdot\bigl(\mathrm{LF}_T(x_0 \dots x_i) - \mathrm{LF}_T(x_0 \dots x_{i-1})\bigr)$, the cost increment of the $i$-th request in the original sequence, computed on prefixes. Because it is a difference of prefix costs, its sums over windows telescope; the subtraction is in the reals, and monotonicity makes it nonnegative. The `factor` absorbs the constant of the algorithm that is compared with the lazy-finger tree. The charge ignores the side, so the same function serves both sides when it is used as `fun _ => lazyFinger factor t`.

@decl Combo.Charges.Results.lazyFinger_nonneg Combo.Charges.Results.lazyFinger_mass Combo.Charges.Results.lazyFinger_total Combo.Charges.Results.lazyFinger_stable

The four results say: the charge is nonnegative; the mass of a window $[lo, hi)$ is $\mathit{factor}$ times the increase of the prefix cost; the total is $\mathit{factor}\cdot\mathrm{LF}_T(X)$; and the charge is stable with $C_0 = 1$ and $C_1 = 2$, provided $\mathit{factor}\cdot|T| \le F$. Stability is `cost_segment` multiplied by `factor`. These are the `nonneg` and `stable` fields of [[Combo.Analysis.WellBehaved]]; the fields `single` and `upper` depend on the worker and are proved for GreedyASS in [Chapter 38](combined-finger.html).

### Interleave charges

@decl Combo.Charges.interleave

`interleave factor t xs i` is $\mathit{factor}\cdot\bigl(1 + \mathrm{IB}_P(x_0 \dots x_i) - \mathrm{IB}_P(x_0 \dots x_{i-1})\bigr)$, where $\mathrm{IB}_P$ is Wilber's interleave quantity [[Wilber.interleave]] for the reference tree $P$ ([Chapter 14](wilber.html)). The $1$ is a unit charge per request. The increment counts the alternations that request $i$ creates along its search path in $P$.

@decl Combo.Charges.Results.interleave_nonneg Combo.Charges.Results.interleave_mass Combo.Charges.Results.interleave_total Combo.Charges.Results.interleave_stable

The charge is nonnegative, the mass of a window is $\mathit{factor}\cdot\bigl((hi - lo) + \mathrm{IB}_P(x_0 \dots x_{hi-1}) - \mathrm{IB}_P(x_0 \dots x_{lo-1})\bigr)$, and the total is $\mathit{factor}\cdot(m + \mathrm{IB}_P(X))$. Stability holds without any overhead: a window, as a sequence of its own, has at most the alternations that its requests create inside $X$, since an alternation of the window is an alternation of $X$ at the same node and the same pair of requests. So $\mathrm{IB}_P$ of the window is at most the increase, and the standalone total is at most the mass.

**Theorem (interleave charges and offline executions).** Let $P$ have the same size as the initial tree $s$, and let an offline execution serve $X$ from $s$ with $k$ rotations. Then the total interleave charge of $X$ is at most $4\cdot\mathit{factor}\cdot(m + k)$.

@decl Combo.Charges.Results.interleave_comparator

This is Wilber's lower bound $\mathrm{IB}_P(X) \le 4k + 2m$ ([[Wilber.Results.rotation_lower_bound]], [Chapter 14](wilber.html)) with the unit charges added: $m + \mathrm{IB}_P(X) \le 4(m + k)$. [[RotationBST.Execution]] counts rotations only, so $m + k$ is the rotation cost plus one per request. It is how Theorem 4.3 turns a window bound in interleave charges into a bound in terms of $\mathrm{OPT}$.

## Finite families

The paper's Section 1.2 combines $k$ algorithms two at a time in a balanced binary tree. The library does the same, with a recursion that closes because the output of a combination is again an interruptible worker: [Chapter 36](combo-online.html) replays the prepared policy as a worker ([[Combo.Online.Replay.Implementation]]), which can be combined again.

### Members, comparators and guarantees

@decl Combo.Family.Algorithm Combo.Family.Algorithm.correct

A family member bundles everything that the first box assumes about one input: a state type, a [[Combo.Controller.Worker]], its [[Combo.Refinement.WorkerModel]] on the common saved tree, and the proof `correct` of request correctness. The state type is part of the member, so members may have different state types.

@decl Combo.Family.Charge Combo.Family.Index

A comparator for a family is a single charge function $\tau(X, i)$, without the side bit. The docstring calls the charges nonnegative; that is not part of the type, but of [[Combo.Analysis.WellBehaved]], which every theorem assumes. `Index depth` is the set of leaves of a full binary combination tree of depth `depth`: a path of left/right choices.

@decl Combo.Family.Guarantees

`Guarantees algorithm F C₀ C₁ factor charges` says that one fixed worker is well-behaved, with overhead $F$ and constants $C_0, C_1$, against `factor` times **every** comparator `charges i` of the family, on both of its sides. The worker does not depend on `i`: one execution satisfies all the bounds at once. This is the property the combination preserves, level by level.

@decl Combo.Family.total Combo.Family.minimum

`total charge xs` is the original total charge, and `minimum charges xs` is the least total over the family, a minimum over a nonempty finite set, so it is attained.

@decl Combo.Family.chargeScale Combo.Family.overheadScale

Each level of the combination tree runs the construction of the first box on two workers and replays the result. A level with constant $C_1 + j$ multiplies the charge factor by [[Combo.Online.Replay.chargeFactor]]` C₀ (C₁ + j) 57` $= 33536\,C_0\,(C_1 + j + 58)$ and the overhead by [[Combo.Online.Replay.overheadFactor]], which is that factor plus $16768\,(5(C_1 + j) + 301) + 1$. The constant $C_0$ is unchanged and $C_1$ grows by one per level.

@decl Combo.Family.Results.overheadScale_pos

### Worker-level combination

**Theorem (balanced combination).** Let $2^d$ members, indexed by the leaves of the depth-$d$ tree, be well-behaved with common $F \ge n$, $C_0$, $C_1$, each against its own comparator, on a nonempty saved tree. Then there is one member that guarantees every comparator, with overhead $O_d F$, constants $C_0$ and $C_1 + d$, and factor $S_d$.

@decl Combo.Family.Results.balanced

**Theorem (any finite family).** The same holds for any nonempty finite family of at most $2^d$ members, and in particular with $d = \lceil \log_2 k \rceil$ for $k$ members.

@decl Combo.Family.Results.finite Combo.Family.Results.exists_combination

A family with fewer than $2^d$ members is padded by repeating members at unused leaves. For $k = 1$, $d = 0$, both scales are $1$, and the single member keeps its original constants.

**Theorem (standalone costs of a guaranteed worker).** If a worker guarantees a family, then a standalone run of either side from its restart state on any valid sequence completes, and its cost is at most $\mathit{factor}$ times the total of each comparator, plus $F$; hence at most $\mathit{factor}$ times their minimum, plus $F$.

@decl Combo.Family.Results.requests Combo.Family.Results.minimum_bound

This is `upper` for each `i`, with the same run: the worker is fixed, so the run does not depend on the comparator.

@decl Combo.Family.Results.combine Combo.Family.Results.minimum_policy

`combine` and `minimum_policy` package the two steps: there is one member that guarantees the family, and its standalone runs cost at most $S_d$ times the least total charge plus $O_d F$. These are statements about the combined *worker*, counted in worker steps. A worker is not yet a pointer execution, which is what the next subsection provides.

### The physical policy

The last step runs one more ComboBST, with the physical online execution of [Chapter 36](combo-online.html), on the combined worker, and transfers the bounds to the pointer machine and to windows.

@decl Combo.Family.Physical.mass Combo.Family.Physical.minimumMass

`mass charge xs lo hi` is the mass of a family comparator over the original indices $[lo, hi)$, as in [Section 33.3](#well-behaved-charges), and `minimumMass` is the least over the family. As for two algorithms, the indices and the history are those of the whole sequence; the window is not recharged as a fresh sequence.

@decl Combo.Family.Physical.chargeFactor Combo.Family.Physical.overheadFactor

These are the constants of the first box, for a worker with constants $C_0, C_1$ that guarantees `factor` times each comparator: the window bound $8384\,(C_1+58)\bigl(2C_0^2\cdot\mathit{factor}\cdot M + (2C_0C_1 + 73)\,F\bigr)$ is `chargeFactor C₀ C₁ factor * M + overheadFactor C₀ C₁ * F`.

@decl Combo.Family.Physical.Bounded

`Bounded p factor overhead charges` is the guarantee of the second box for one prepared policy `p`, fixed in advance. For every valid sequence: the run from the saved tree is a legal pointer execution; its total cost is at most `factor` times the least total charge plus `overhead`; and every window splits the run exactly, is a legal pointer execution between the trees actually reached, and costs at most `factor` times the least original window mass plus `overhead`. As in the first box, the comparator is chosen after the run, separately for each window: different windows may be bounded by different members.

**Theorem (physical bounds of a guaranteed worker).** Let a member guarantee a family with overhead $F \ge n$, constants $C_0, C_1$ and some factor, and let `p` be any prepared policy for it with budget $(C_1+1)F$ and restore charge $57F$. Then for every valid sequence, every window of the run is legal, splits additively, and costs at most `chargeFactor` times each comparator's mass, and so at most `chargeFactor` times the least mass, plus `overheadFactor` $\cdot F$; the whole run is bounded in the same way by the least total.

@decl Combo.Family.Physical.Results.executed_window Combo.Family.Physical.Results.window_minimum Combo.Family.Physical.Results.prefix_minimum Combo.Family.Physical.Results.bounded

These hold for **every** prepared policy `p`, not only for a chosen one: a preparation only fixes the snapshot and the initial physical state, and all preparations obey the bounds. `bounded` packages the three into [[Combo.Family.Physical.Bounded]].

**Theorem (a policy exists).** Under the same hypotheses, with a nonempty saved tree, a prepared policy exists, and it is bounded.

@decl Combo.Family.Physical.Results.policy_exists

**Theorem (finite families).** For a nonempty finite family of $k$ members, well-behaved with common $F \ge n$, $C_0$ and $C_1$, on a nonempty saved tree, there is a combined member that guarantees the whole family with the scales of depth $d$, and a prepared policy for it that is bounded with factor `chargeFactor C₀ (C₁ + d) (chargeScale C₀ C₁ d)` and overhead `overheadFactor C₀ (C₁ + d) * (overheadScale C₀ C₁ d * F)`. In `combine`, $d$ is any depth with $k \le 2^d$; in `finite_policy`, $d = \lceil \log_2 k \rceil$.

@decl Combo.Family.Physical.Results.combine Combo.Family.Physical.Results.finite_policy

`finite_policy` is the theorem of the second box. The final policy runs the controller once more, on the two sides of the combined member, so even a singleton family pays the physical factor once.

## What is not formalized

- **Real-world storage.** The paper's clauses that ComboBST is a real-world BST when $A_0$ and $A_1$ are, and that OneFinger-BST preserves this (Theorems 3 and 5), are not formalized. The library's model charges pointer operations and requests only; the policy uses classical choice and uncharged private planning.
- **The $O(k)$ overhead.** The paper states an $O(k)$ overhead for $k$ algorithms. The library's scales grow by a factor of order $C_0(C_1 + d)$ per level, which is a constant for fixed $k$ but much larger than $O(k)$.
- **Corollary 4.** The paper's application combines splay trees, multi-splay trees [@wang2006] and layered working-set trees [@bose2012layered]. None of these is provided as a well-behaved worker, so Corollary 4 is not formalized. The applications that are formalized are GreedyASS and Tango, in [Chapter 38](combined-finger.html).
- **Arbitrary BSTs.** No theorem turns an arbitrary [[RotationBST.Algorithm]] into a well-behaved worker. The worker, its interpretation, correctness and charges are always supplied.
