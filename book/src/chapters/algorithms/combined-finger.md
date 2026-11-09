# All the finger bounds at once

Part IV has produced two online BSTs whose guarantees do not compare. GreedyASS ([Chapter 24](greedy-finger.html)) is within a constant factor of the best weighted dynamic finger bound, with a linear startup term, but no competitive ratio better than $O(\log n)$ is known for it. Tango ([Chapter 29](tango.html)) is $O(\log\log n)$-competitive with the offline optimum, but its bound is relative to the optimum only, and it is not known to have the finger bounds. Neither guarantee implies the other. Iacono and Langerman [-@iacono2016] end their paper with Theorem 4.3, which takes the best of both. They combine the two algorithms with the ComboBST construction of Demaine, Iacono, Langerman and Özkan ([Chapter 33](combining.html)), so that one BST costs at most a constant times the *minimum* of the two bounds, plus $O(n)$. They then apply the deamortization of Bose, Collette, Fagerberg and Langerman ([Chapter 37](deamortization.html)), so that every search also costs $O(\log n)$ in the worst case.

The paper gives this theorem in two lines, citing the other two papers. The library proves it. This chapter assembles the proof from the pieces built in the preceding chapters, and states the result with its explicit constants.

```headline combined-finger
title: One BST has the weighted dynamic finger bound, is $O(\log\log n)$-competitive, and costs $O(\log n)$ per search
source: @iacono2016
key: yes
theorems: Geometric.GreedyASS.Combination.Deamortized.Results.combined
skip: Geometric.GreedyASS.Combination.Policy | The combined policy is an existential witness. The theorem states its bounds directly about the deamortized program `d`, whose meaning (setup trace, served stream, response costs, causality) does not depend on what the policy is. The policy's ComboBST machinery is explained in the chapter but need not be read to check the claim.
skip: Geometric.GreedyASS.Combination.Policy.cost | Used only in one conjunct of the `correct` field of `Deamortized`, which compares the program's costs with the policy's ComboBST execution. That conjunct only adds information about the existential witness, and `combined` states the resulting bound in closed form.

This is the abstract BST-operation counterpart of Theorem 4.3 of the paper, in a normalized form. Let `saved` be any nonempty initial tree on $n$ keys. There is one program, fixed before the requests, the start finger, the weights and the offline comparator are chosen, with the following properties.

- **Setup.** Before the first request, a legal pointer trace of cost $S \le 16\,n$ turns `saved` into the program's prepared tree.
- **Serving.** For every sequence $X = x_1, \dots, x_m$ of keys less than $n$, the empty sequence included, the program's instructions form a legal single-finger pointer execution from the prepared tree. They split into one contiguous segment per request, and the segment of $x_j$ visits $x_j$. The response cost $c_j$ is $1$ plus the length of that segment, so $\sum_j c_j = m + {}$(number of instructions).
- **Online.** The instructions and response costs for $x_1, \dots, x_j$ do not depend on the later requests.
- **Worst case.** Every response costs $c_j < 251 + 195 \log_2 n$.
- **Total.** For every start key $p < n$, every initial tree on $n$ keys and every offline rotation-model execution that serves $X$ from it with $R$ rotations,

$$S + \sum_{j=1}^m c_j \;\le\; 16\,n + 2480\Bigl(1307904 \min\bigl(184903680\,\mathrm{WF}^*(p, X),\; 8\,\lceil 64\,(14\,L + 6)\rceil\,(m + R)\bigr) + 3839872 \cdot 46225920\, n\Bigr),$$

where $L = \log_2(1 + \lfloor\log_2 n\rfloor)$. So the total cost is

$$O\bigl(n + \min\bigl(\mathrm{WF}^*(p, X),\; (m + R)(1 + \log_2(1 + \lfloor\log_2 n\rfloor))\bigr)\bigr).$$

Here $\mathrm{WF}^*(p, X)$ is [[WeightedFinger.optimalCostFrom]], the infimum over all weightings positive on the keys of the weighted dynamic finger cost with $x_0 = p$ and one unit per request ([Chapter 24](greedy-finger.html)). It is not assumed to be attained. The comparator is any [[RotationBST.Execution]], so the bound holds in particular for the optimal one. The program is a [[Geometric.GreedyASS.Combination.Deamortized]] structure: its fields give the setup trace and the causality, and the theorem gives the rest.
```

```headline combined-finger-weights
title: The same program, against every weighting
source: @iacono2016
theorems: Geometric.GreedyASS.Combination.Results.policy_exists Geometric.GreedyASS.Combination.Deamortized.Results.policy_exists Geometric.GreedyASS.Combination.Deamortized.Results.weights_competitive
skip: Geometric.GreedyASS.Combination.Policy | The combined policy is only required to exist. The bound is stated directly about the deamortized program `d`, whose meaning (setup trace, served stream, response costs, causality) does not depend on what the policy is.
skip: Geometric.GreedyASS.Combination.Policy.cost | Used only in one conjunct of the `correct` field of `Deamortized`, which compares the program's costs with the policy's ComboBST execution. That conjunct only adds information about the witness, and the bound is stated without it.

The form of Theorem 4.3 for a single weighting. For every nonempty tree on $n$ keys there is a combined policy `p` and a deamortized program `d` for it. For every weighting $w$ positive on the keys, every $p < n$, and every rotation-model execution with $R$ rotations that serves $X$ from a tree on $n$ keys, if the program serves $X$ then its setup plus response costs is at most

$$16\,n + 2480\Bigl(1307904 \min\bigl(184903680\,\mathrm{WF}_w(p, X),\; 4\,\mathtt{linearChargeFactor}(\mathtt{balanced}\ n)\,(m + R)\bigr) + 3839872 \cdot 46225920\, n\Bigr).$$

The weights are chosen after the program, which never sees them.
```

The first box is all that a reader who wants to confirm the result needs; the second restates its weighted form for a single weighting. The rest of the chapter has two parts. [Section 38.1](#reading-the-statement) explains the conventions of the statement, and compares it line by line with the paper's Theorem 4.3. [Section 38.2](#how-the-pieces-fit) gives a map of the proof. The later sections state every theorem of the four interface files `Algorithms/Tango/Combination/Abstract.lean`, `Algorithms/GreedyASS/Combination/Abstract.lean`, `Algorithms/GreedyASS/Combination/Deamortized/Abstract.lean` and their definitions, in the order of the proof: the two source workers ([Section 38.3](#the-greedyass-worker) and [Section 38.4](#the-tango-worker)), the combined policy ([Section 38.5](#the-combined-policy)), and its deamortization ([Section 38.6](#deamortizing-the-policy)).

This chapter needs almost nothing from the construction behind ComboBST and the deamortization. It uses their main theorems, as black boxes with explicit constants, and their interfaces. The reader who wants to know how a combined BST can switch between two algorithms without losing their bounds should read [Chapter 33](combining.html) to [Chapter 36](combo-online.html), and the reader who wants to know how amortized costs become worst-case costs should read [Chapter 37](deamortization.html).

## Reading the statement

### One program, chosen first

The quantifiers of [[Geometric.GreedyASS.Combination.Deamortized.Results.combined]] come in this order:

$$\forall\, \mathit{saved}\ \ \exists\, \mathit{policy}\ \ \exists\, \mathit{program}\ \ \forall\, X\ \ \forall\, p\ \ \forall\, \mathit{offline}.$$

The program is fixed before the requests, before the start key $p$ of the finger benchmark, and before the offline execution it is compared with. Like GreedyASS with respect to its weights, it never sees $p$, the weights or the offline execution: they appear only in the bound. It is fixed after the initial tree `saved`, as an online algorithm knows its own tree, and after `fields` and `oldData`, the arbitrary initial contents of the per-node fields that the ComboBST snapshots use. The combined policy's startup initializes those fields, and the proof builds the same two source workers whatever their initial contents.

The program is a function from whole request sequences to outputs (a [[Deamortization.Scheduler.Output]]: final state, instruction list, and one response cost per request). What makes it online is its `causal` field: the output on a prefix of a sequence is a prefix of the output on the whole sequence, both for the instruction list and for the cost list. Since every request has its own contiguous segment of instructions ([[Deamortization.Scheduler.ServedStream]]), the response to $x_j$ is fixed once $x_1, \dots, x_j$ are known.

### Conventions

- **What is counted.** The program runs on the single-finger pointer machine of [Chapter 6](pointer.html) and [Chapter 10](fingers.html): every finger move and every rotation is one instruction. The response cost of a request is $1$ plus the number of instructions in its segment, so every request costs at least $1$, and the costs sum to $m$ plus the number of instructions. The computation that decides the instructions is not counted (see [What is not claimed](#what-is-not-claimed) below).
- **Setup.** The setup trace $S \le 16\,n$ is paid once, before the first request, and belongs to no response. It is included in the total. The startup of ComboBST (initializing the node fields and saving the first snapshot) is not part of $S$: it is paid inside the response costs, so it is subject to the worst-case bound, and it is included in the additive term $3839872 \cdot 46225920\, n$.
- **A unit per request.** The weighted charge is $1 + \log_2(W[x_{j-1}, x_j] / \min(w_{x_{j-1}}, w_{x_j}))$, as in [Chapter 24](greedy-finger.html), and the competitive term charges $m + R$, not $R$. Without the unit, a sequence that repeats one key would have benchmark $0$ and no BST could meet it.
- **The finger benchmark.** $\mathrm{WF}^*(p, X)$ starts from an explicit predecessor $x_0 = p$, and the bound holds for every valid $p$. It is an infimum of real numbers over the weightings positive on $\{0, \dots, n-1\}$. A bound by the infimum implies the bound for every weighting; [[Geometric.GreedyASS.Combination.Deamortized.Results.weights_competitive]] states that form.
- **The competitive benchmark.** $R$ is the number of rotations of any [[RotationBST.Execution]] serving $X$: the rotate-to-root model of [Chapter 3](accesses.html), where each access rotates the requested key to the root. Its initial tree is any tree on $n$ keys, not necessarily `saved`.
- **The doubly logarithmic factor.** The paper's $\log\log n$ appears as $\lceil 64(14L + 6)\rceil$ with $L = \log_2(1 + \lfloor\log_2 n\rfloor)$, coming from Tango on the balanced reference tree [[Tango.balanced]] of height at most $1 + \lfloor\log_2 n\rfloor$. Since $\lceil 64(14L + 6)\rceil \le 896\,L + 385$, the factor is $O(1 + L)$, and it is positive even when $n = 1$, where $L = 0$.
- **Constants.** They are explicit witnesses, products of the constants of the ingredients, and nowhere near optimal: the coefficient of $\mathrm{WF}^*$ in the total is about $6.0 \cdot 10^{17}$, and that of $n$ is about $4.4 \cdot 10^{17}$. [Section 38.2](#how-the-pieces-fit) shows where each comes from.
- **Valid inputs.** Requests and the start key must be less than $n$, and `saved` must be nonempty. The empty sequence is allowed: its total is the setup alone.

### Compared with Theorem 4.3

| Theorem 4.3 of the paper | [[Geometric.GreedyASS.Combination.Deamortized.Results.combined\|combined]] |
|---|---|
| "There is a BST algorithm" | For each nonempty initial tree, one combined policy and one causal deamortized program, on the single-finger pointer machine |
| $W$ ranges over positive weights, minimum over $W$ | Infimum over weightings positive on the keys, not assumed attained |
| $\sum_{i=1}^m \log(\cdots)$, with $s_0$ unspecified | $\sum_{j=1}^m (1 + \log_2(\cdots))$, with $x_0 = p$ for every $p < n$ |
| $\mathrm{OPT}(S)$ | $m + R$ for every rotation-model execution from every tree on $n$ keys |
| $\log\log n$ | $\lceil 64(14L + 6)\rceil$, $L = \log_2(1 + \lfloor\log_2 n\rfloor)$ |
| $O(n + \min(\cdot, \cdot))$ | Explicit constants, setup included |
| Each search $O(\log n)$ worst-case | Each response $< 251 + 195\log_2 n$; setup $\le 16\,n$ before the first request |
| | Exactly one response per request, each visiting its key; the empty sequence included |

The paper's proof is the sentence before the theorem: deamortize and combine GreedyASS with Tango. Two remarks about how the library carries it out.

- **The source contracts are proved.** ComboBST does not combine arbitrary algorithms. Its Theorem 3 assumes that each source has *well-behaved* amortized charges: bounded single accesses, an upper bound that holds on every contiguous piece of the sequence, and a linear restart allowance ([[Combo.Analysis.WellBehaved]], [Chapter 33](combining.html)). In the library's ComboBST theorems these are hypotheses. Here they are theorems: [[Geometric.GreedyASS.Combination.Results.greedy_worker]] for GreedyASS and [[Tango.Combination.Results.linear_balanced_worker]] for Tango. So `combined` has no hypothesis beyond a nonempty initial tree.
- **Tango needed a new proof.** The Tango analysis of [Chapter 29](tango.html) has a startup term $(14L + 6)\,n$, of order $n\log\log n$, because it charges each first setting of a preference like a preference change. Combined directly, it would give $O(n\log\log n + \min(\cdot, \cdot))$, which is weaker than Theorem 4.3. The bottom-up preference updates of [Chapter 30](tango-linear.html) bring Tango's startup term down to $O(n)$. The paper's one-sentence proof does not address this point.

The sentence before Theorem 4.3 also mentions the working-set bound. Theorem 4.3 does not state it, and neither does the library.

### What is not claimed

::: caveat Not claimed
- **Private computation and storage.** All bounds count BST instructions. The program decides its instructions by simulating the two sources, replaying their logs, and scheduling their work, and none of this computation is charged or bounded. Planning, instruction logs and snapshots are abstract resources of the model. The library does not claim the clauses of the source papers about auxiliary storage and execution on a finite-word machine: Theorem 7 of the deamortization paper, and the storage parts of Theorems 3 and 5 of the ComboBST paper.
- **Dynamic optimality.** The competitive factor is $O(\log\log n)$, as for Tango. Nothing here says that the program, GreedyASS or Tango is dynamically optimal.
- **Optimal constants.** The constants witness the asymptotic statement; no effort was made to reduce them.
:::

## How the pieces fit

The proof has five steps, each a theorem of an earlier chapter, or a short theorem of this chapter.

```text
 GreedyASS as a BST (Ch. 24)              bottom-up Tango on balanced n (Ch. 30)
 Performance.Results.bst                   BottomUp.policy, linear_run_bound
          │  replay adapter (x 64)                  │  replay adapter (x 64)
          ▼                                         ▼
 greedy_worker                             linear_balanced_worker
   allowance 46225920 n                      allowance 2816 n
   charges: lazy finger on any tree t        charges: interleave on balanced n
          └───────────────┬─────────────────────────┘
                          │  Worker.Pair, common allowance F = 46225920 n
                          ▼  ComboBST: Online.Replay.Results.combine (Ch. 33–36)
                  Policy   (Combination.Results.policy_exists)
                    cost ≤ 1307904 · min(...) + 2531968 F
                          │  lazy finger → weights (Ch. 15), interleave → OPT (Ch. 14)
                          ▼
                  weighted_competitive: 184903680 WF*, 4 c (m + R), 3839872 F
                          │  deamortization: Deamortization.Replay.Results.deamortize (Ch. 37)
                          ▼
                  Deamortized   (Deamortized.Results.policy_exists)
                    S ≤ 16 n,  Σ c ≤ 2480 · cost,  each c < 251 + 195 log₂ n
                          │
                          ▼
                  combined
```

1. **Two workers.** ComboBST runs its sources as interruptible *workers* ([Chapter 34](combo-workers.html)): it executes them a bounded number of instructions at a time, and restores their trees from snapshots when it switches. Any online rotation-model algorithm becomes such a worker by the replay adapter [[Combo.Worker.Replay.Results.algorithms_well_behaved]], which costs at most $64$ times the algorithm's total cost. GreedyASS as a BST ([[Geometric.GreedyASS.Performance.Results.bst]]) costs at most $722280\,\mathrm{LF}^*(X) + 96303\,n$, and $64 \cdot 722280 = 46225920$. This gives [[Geometric.GreedyASS.Combination.Results.greedy_worker]], with allowance $46225920\,n$. The bottom-up Tango policy on the balanced reference ([[Tango.BottomUp.Results.balanced_policy]]) gives [[Tango.Combination.Results.linear_balanced_worker]], with allowance $2816\,n$.
2. **One policy.** The two workers are paired ([[Combo.Worker.Pair.Results.well_behaved]]), with the larger allowance $F = 46225920\,n$ for both ([[Geometric.GreedyASS.Combination.overhead]]). ComboBST's replay theorem [[Combo.Online.Replay.Results.combine]] turns the pair into one prepared online policy, which [[Geometric.GreedyASS.Combination.Results.policy_exists]] packages as a [[Geometric.GreedyASS.Combination.Policy]]. Its cost bound comes from [[Combo.Online.Results.minimum_bound]] with $C_0 = 1$, $C_1 = 20$ and restore factor $57$: the factor is $8384 \cdot (20 + 1 + 57) \cdot 2 = 1307904$, and the additive term is $8384 \cdot 78 \cdot 3\,F + 524 \cdot 1088\, n \le 2531968\,F$.
3. **From fixed trees to the benchmarks.** The GreedyASS charges are those of a lazy finger on a fixed reference tree, and hold for every tree; at the best tree they give $\mathrm{LF}^*(X)$, and the characterization of [Chapter 15](lazy-finger.html), $\mathrm{LF}^*(X) \le n + 4\,\mathrm{WF}^*(p, X)$ ([[LazyFinger.Results.characterization_root]]), gives the coefficient $4 \cdot 46225920 = 184903680$. The Tango charges are Wilber's interleave bound on the balanced reference, and $m + \mathrm{IB}(X) \le 4(m + R)$ by [[Wilber.Results.rotation_lower_bound]] ([Chapter 14](wilber.html)). The additive term becomes $(2531968 + 1307904)\,F = 3839872\,F$.
4. **Deamortization.** The combined policy is again a replay planner. The deamortization theorem for planners [[Deamortization.Replay.Results.deamortize]] turns it into a program with setup at most $16\,n$, worst-case responses below $251 + 195\log_2 n$, and total response cost at most $1240$ times the planner's run, which is at most twice the policy's cost ([[Combo.Online.Replay.Results.run_bound]]); hence $2480$.
5. **Closed form.** The Tango coefficient is $4 \cdot \mathtt{linearChargeFactor}(\mathtt{balanced}\ n) \le 8\,\lceil 64(14L+6)\rceil$ ([[Tango.Combination.Results.balanced_linear_factor]]), which gives `combined`.

Only step 1 for Tango contains new mathematics: the linear startup of [Chapter 30](tango-linear.html). The rest is arithmetic on the theorems of other chapters.

## The GreedyASS worker

A worker for ComboBST is a [[Combo.Worker.Replay.Planner]]: a causal function that, from its current state and the current request, produces the pointer instructions that serve the request, certified legal and visiting the request ([Chapter 34](combo-workers.html)). Its state type here is `List Nat × Pointer.Lazy.Online.State`: the past requests and the state of the lazy pointer simulation [[Pointer.Lazy.Online.run]] of an online algorithm. A worker is *well-behaved* with allowance $F$, constants $C_0, C_1$ and charges $\phi$ if, for every valid sequence ([[Combo.Analysis.WellBehaved]]):

- every single access, from any reachable state, costs at most $C_1 F$;
- the whole sequence costs at most its total charge plus $F$;
- for every contiguous piece $X[lo, hi)$, the total charge of the piece as a sequence of its own, plus $F$, is at most $C_0$ times the charges of the same positions *in the original sequence*, plus $C_1 F$.

The last condition is what lets ComboBST restart a source in the middle of a sequence. For the lazy-finger charges it holds because restarting a lazy finger at the root, instead of at the previous request, costs at most $n$ more, which the allowance pays ([[Combo.Charges.Results.lazyFinger_stable]], [Chapter 33](combining.html)).

**Theorem (the GreedyASS worker).** For every tree `saved` on $n$ keys there is one replay planner starting from `saved` that is well-behaved, with allowance $46225920\,n$, $C_0 = 1$ and $C_1 = 20$, for the lazy-finger charges $46225920 \cdot \bigl(\mathrm{LF}_t(x_1 \dots x_{i+1}) - \mathrm{LF}_t(x_1 \dots x_i)\bigr)$ of *every* tree $t$ on $n$ keys.

@decl Geometric.GreedyASS.Combination.Results.greedy_worker

The planner is chosen before the reference tree $t$: one GreedyASS worker satisfies the contract for all trees at once. This is what lets the combined policy be chosen before the benchmark. The charges are [[Combo.Charges.lazyFinger]], the increments of the root-start lazy-finger cost [[LazyFinger.cost]], scaled by the constant of the GreedyASS simulation; they sum to $46225920\,\mathrm{LF}_t(X)$. The planner is the replay adapter applied to the GreedyASS algorithm of [[Geometric.GreedyASS.Performance.Results.bst]], whose bound $722280\,\mathrm{LF}^*(X) + 96303\,n$ multiplied by the adapter's $64$ is below $46225920\,\mathrm{LF}_t(X) + 46225920\,n$.

## The Tango worker

### The charge factors

Tango's charges are Wilber's interleave bound on a fixed reference tree, one unit per request plus one per preference change ([[Combo.Charges.interleave]]), scaled by a factor that pays for the work per change. The factor depends on the height $h$ of the reference.

@decl Tango.Combination.chargeFactor Tango.Combination.linearChargeFactor

`chargeFactor reference` is $\lceil 64\,(14 \log_2 h + 6)\rceil$: the replay adapter's factor $64$, times a coefficient that covers the $O(\log h)$ cost of Tango per preference change, per first setting of a preference and per request in the analysis of [Chapter 29](tango.html). `linearChargeFactor` is twice that, for the bottom-up policy of [Chapter 30](tango-linear.html), whose per-request coefficient $17\log_2 h + 5$ is larger and whose startup is accounted separately.

The following five lemmas are the arithmetic facts about these factors that the proofs need: lower bounds by the real expressions, positivity, and the bounds for the balanced reference on $n$ keys, whose height is at most $1 + \lfloor\log_2 n\rfloor$.

@decl Tango.Combination.Results.factor_lower Tango.Combination.Results.factor_pos Tango.Combination.Results.balanced_factor Tango.Combination.Results.linear_factor_lower Tango.Combination.Results.balanced_linear_factor

### Workers with an $n \log\log n$ startup

The first adapter takes the top-down Tango policy of [Chapter 29](tango.html) as it is.

**Theorem (Tango workers).** For every Tango policy on a reference tree, and every tree `saved` of the same size $n$, there is a replay planner starting from `saved` that is well-behaved, with allowance $\mathtt{chargeFactor} \cdot n$, $C_0 = 1$, $C_1 = 20$, and the interleave charges of the reference scaled by `chargeFactor`. The second version adds that the worker, restarted on any sequence $X$, costs at most $4\,\mathtt{chargeFactor}\,(m + R) + \mathtt{chargeFactor} \cdot n$ for every offline execution with $R$ rotations. The third is the case of the balanced reference.

@decl Tango.Combination.Results.worker Tango.Combination.Results.competitive_worker Tango.Combination.Results.balanced_worker

These workers are not used for Theorem 4.3. Their allowance, $\mathtt{chargeFactor} \cdot n$, is $\Theta(n\log\log n)$ for a balanced reference. The combination charges the common allowance $F$ a constant number of times (the term $3839872\,F$), so a superlinear $F$ would leave a superlinear additive term in the final bound.

### The linear-startup worker

**Theorem (the Tango worker with linear startup).** For every tree `saved` on $n$ keys there is a replay planner starting from `saved` that is well-behaved, with allowance $2816\,n$, $C_0 = 1$, $C_1 = 20$, and the interleave charges of [[Tango.balanced]]` n` scaled by `linearChargeFactor`.

@decl Tango.Combination.Results.linear_balanced_worker

The planner is the replay adapter applied to the bottom-up Tango policy `Tango.BottomUp.policy` on the balanced reference. Its run costs at most the reference's local initialization credit, plus $14\log_2 h + 4$ per preference change, plus $17\log_2 h + 5$ per request ([[Tango.BottomUp.Results.linear_run_bound]]). For the balanced reference the local credit is at most $42\,n$ ([[Tango.Initialization.Local.Results.balanced_localAllowance]]), and the conversion to an online algorithm adds $2\,n$; the adapter's factor $64$ turns $44\,n$ into $2816\,n$. Segment stability holds for interleave charges because a contiguous piece keeps every preference change internal to it ([[Combo.Charges.Results.interleave_stable]]).

## The combined policy

### The definitions

Both sources use the same state type, and one common allowance:

@decl Geometric.GreedyASS.Combination.SourceState Geometric.GreedyASS.Combination.overhead

$F = 46225920\,n$ is the larger of the two allowances. A well-behaved worker stays well-behaved when its allowance grows, so both sources can use $F$.

@decl Geometric.GreedyASS.Combination.charges Geometric.GreedyASS.Combination.pairModel

`charges saved reference` assigns the GreedyASS lazy-finger charges on `reference` to side `false` and the Tango interleave charges on the balanced tree to side `true`. The reference tree is a parameter of the analysis only: the algorithm never sees it. `pairModel` is the pointer model of the paired worker [[Combo.Worker.Pair.worker]]: GreedyASS on side `false`, Tango on side `true`, each running its own side `false`.

**Definition (the combined policy).** A `Policy saved fields oldData` consists of the two source planners, the proof that their pair is well-behaved for *every* reference tree of size $n$, a prepared ComboBST execution ([[Combo.Online.Prepared]], [Chapter 36](combo-online.html)) with round budget $21\,F$ and restore allowance $57\,F$, and a replay implementation of it ([[Combo.Online.Replay.Implementation]]).

@decl Geometric.GreedyASS.Combination.Policy

The field `supported` quantifies over the reference inside the structure, after the planners: once a policy is chosen, all the reference trees are compared with the same execution. `fields` and `oldData` are the initial contents of the node fields, which the prepared startup initializes ([Chapter 50](tree-buffers.html) and [Chapter 51](snapshots.html)).

@decl Geometric.GreedyASS.Combination.Policy.cost Geometric.GreedyASS.Combination.Policy.finalTree

`p.cost xs` is the cost of the actual pointer execution [[Combo.Online.execute]] of the prepared policy on `xs`, started in its unprepared state `none`. It includes the preparation, which the first request triggers, and is $0$ on the empty sequence. `p.finalTree xs` is the tree it ends in.

**Theorem (one combined policy).** For every nonempty tree `saved` and all initial node contents, a combined policy exists.

@decl Geometric.GreedyASS.Combination.Results.policy_exists

### Bounds for the policy

All the bounds below hold for one policy `p`, fixed before the reference tree, the start key, the weights and the offline execution.

**Theorem (every fixed reference).** For every tree $t$ on $n$ keys and every valid $X$, the policy's execution is a legal [[Pointer.Execution]] that serves $X$ from `saved` and ends in `p.finalTree X`, and its cost is at most

$$1307904 \min\bigl(46225920\,\mathrm{LF}_t(X),\; \mathtt{linearChargeFactor}\,(m + \mathrm{IB}(X))\bigr) + 2531968\,F,$$

where $\mathrm{LF}_t$ is the root-start lazy-finger cost on $t$ and $\mathrm{IB}$ is [[Wilber.interleave]] on the balanced reference. The second version replaces $\mathrm{LF}_t(X)$ by its minimum $\mathrm{LF}^*(X)$ over all trees on $n$ keys.

@decl Geometric.GreedyASS.Combination.Results.tree_bound Geometric.GreedyASS.Combination.Results.optimal_bound

The minimum is attained ([[LazyFinger.Results.optimal_attained]]), so `optimal_bound` is `tree_bound` at a minimizing tree.

**Theorem (weighted and competitive).** For every $p < n$, and every rotation-model execution with $R$ rotations that serves $X$ from a tree on $n$ keys, the policy's cost is at most

$$1307904 \min\bigl(184903680\,\mathrm{WF}^*(p, X),\; 4\,\mathtt{linearChargeFactor}\,(m + R)\bigr) + 3839872\,F.$$

The second version has $\mathrm{WF}_w(p, X)$, for every weighting $w$ positive on the keys, in place of the infimum.

@decl Geometric.GreedyASS.Combination.Results.weighted_competitive Geometric.GreedyASS.Combination.Results.weights_competitive

The validity of $X$ is not a hypothesis here: it follows from the offline execution. This is the combined bound of Theorem 4.3, with linear startup but with amortized costs.

**Theorem (the policy is again a worker).** For every reference tree and every choice `select` of which source's charges to put on each side, the replay worker of the combined policy is well-behaved with $C_0 = 1$, $C_1 = 21$, allowance `overheadFactor 1 20 57` $\cdot\,F$, and the selected charges scaled by `chargeFactor 1 20 57` ([[Combo.Online.Replay.overheadFactor]], [[Combo.Online.Replay.chargeFactor]]).

@decl Geometric.GreedyASS.Combination.Results.worker_bound

So the combined policy can itself enter a further combination, with either source's guarantee. Theorem 4.3 does not need this.

## Deamortizing the policy

### The deamortized program

**Definition (the deamortized program).** For a combined policy `p`, a `Deamortized p` consists of a prepared tree `initial`, a setup cost `startup` and a `program` from request sequences to scheduler outputs, with:

- `setup`, a legal [[Pointer.Trace]] of cost `startup` from `saved` to `initial`, both with the finger at the root, and `setup_bound`, $\mathtt{startup} \le 16\,n$;
- `correct`: on every valid sequence the program returns an output whose instructions replay legally from `initial` ([[Multifinger.replay]]); they form a [[Deamortization.Scheduler.ServedStream]], one contiguous segment per request visiting it, with response cost $1 + {}$segment length; they form a single-finger [[Multifinger.Execution]] serving the sequence at cost $m + {}$(number of instructions); there is one cost per request, summing to $m + {}$(number of instructions) and to at most $2480$ times `p.cost`; and each cost is below $251 + 195\log_2 n$;
- `causal`: the output on a prefix has a prefix of the instructions and a prefix of the costs.

@decl Geometric.GreedyASS.Combination.Deamortized

The structure records the guarantees of the deamortization theorem of [Chapter 37](deamortization.html) for this one source. The comparison with `p.cost` is the only field that mentions the policy. The worst-case bound depends only on $n$, not on the policy.

**Theorem (the deamortized program exists).** Every combined policy on a nonempty tree has a deamortized program.

@decl Geometric.GreedyASS.Combination.Deamortized.Results.policy_exists

The proof applies [[Deamortization.Replay.Results.deamortize]] to the policy's replay planner. Its total is at most $1240$ times the planner's run, and the planner's run costs at most twice the policy's execution ([[Combo.Online.Replay.Results.run_bound]]).

### Bounds for the program

**Theorem (setup included).** On every valid sequence, the setup plus all response costs is at most $16\,n + 2480\,\mathtt{p.cost}(X)$.

@decl Geometric.GreedyASS.Combination.Deamortized.Results.total_bound

**Theorem (weighted and competitive, deamortized).** For every $p < n$ and every rotation-model execution with $R$ rotations that serves $X$ from a tree on $n$ keys, the setup plus all response costs is at most

$$16\,n + 2480\Bigl(1307904 \min\bigl(184903680\,\mathrm{WF}^*(p, X),\; 4\,\mathtt{linearChargeFactor}\,(m + R)\bigr) + 3839872\,F\Bigr).$$

The second version has $\mathrm{WF}_w(p, X)$, for every weighting $w$ positive on the keys, in place of the infimum.

@decl Geometric.GreedyASS.Combination.Deamortized.Results.weighted_competitive Geometric.GreedyASS.Combination.Deamortized.Results.weights_competitive

**Theorem (closed form).** The same, with $4\,\mathtt{linearChargeFactor}$ replaced by $8\,\lceil 64(14L + 6)\rceil$, $L = \log_2(1 + \lfloor\log_2 n\rfloor)$, and $F$ by $46225920\,n$.

@decl Geometric.GreedyASS.Combination.Deamortized.Results.linear_weighted_competitive

Finally, the theorem of the headline puts the pieces together: a policy and a program exist, and for every valid sequence the program's output serves it with one response per request, each below $251 + 195\log_2 n$, and the closed-form bound holds for every start key and every offline execution.

@decl Geometric.GreedyASS.Combination.Deamortized.Results.combined

The statement omits the replay and single-finger execution clauses of `correct`, and the causality, which are fields of the program `d`. Since `d` is the existential witness, those fields hold for the same program.
