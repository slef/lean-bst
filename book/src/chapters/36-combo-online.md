# One online execution

[Chapter 34](combo-workers.html) and [Chapter 35](combo-rounds.html) built the logical side of Combo-BST. A **worker** packages the two source algorithms $A_0$ and $A_1$ as interruptible step functions, and the **controller** runs them in alternating bounded rounds, restoring the initial tree whenever it switches. All costs there are counted in *worker units*: one unit per worker step, plus an explicit restore charge per switch. Nothing there is yet a binary search tree.

This chapter turns the controller into one physical online BST algorithm, and proves its bounds. It is the last step of Theorem 3 of Demaine, Iacono, Langerman and Özkan (2013). There are three ingredients.

1. **Refinement onto shared nodes.** Each worker step becomes a bounded number of instructions on a tree buffer with two persistent fingers: finger 0 is the worker's cursor, finger 1 keeps the scan position of the saved snapshot. Restoring the initial tree is a streaming load of that snapshot. This is the paper's Combo-MFBST, a multi-finger BST in the sense of [Chapter 10](fingers.html).
2. **One finger.** The finger hand of [Chapter 43](finger-hands.html) simulates the two fingers with the single root-restarting cursor of the pointer machine ([Chapter 6](pointer.html)). This is the paper's OneFinger-BST (its Theorem 5), applied to Combo-MFBST.
3. **One fixed policy.** All choices, the snapshot, the hand, and the instructions of every request, are fixed once, before any request is known. Preparation is paid on the first request. The result is one online algorithm, and its *actual* run is analysed on every prefix and on every contiguous window.

The window theorem, `window_policy`, is the formal Theorem 3. Its headline box is in [Chapter 33](combining.html). This chapter's own headline is the whole-prefix version, which has a slightly sharper formula.

```headline combo-online-prefix
title: One fixed online pointer algorithm is within the better of two bounds on every prefix
source: Demaine, Iacono, Langerman and Özkan, *Combining binary search trees* (2013)
theorems: Combo.Online.Results.prefix_policy

Let $T$ be a nonempty tree on $n$ keys, and let a worker present two source algorithms $A_0$ and $A_1$ on $T$, with a causal pointer interpretation in which every access visits its key. Suppose both have well-behaved nonnegative amortized charges $\tau_0, \tau_1$ with constants $C_0, C_1$ and overhead $F \ge n$. Then there is one prepared online policy $p$, fixed before any request is known, such that for every sequence $X$ of keys in $\{0,\dots,n-1\}$, $p$ serves $X$ as a legal pointer-machine execution from $T$, and its total cost, pointer instructions plus one unit per request, is at most

$$524 \cdot 1088\, n \;+\; 8384\,(C_1 + 58)\Bigl(2C_0 \min\Bigl(\sum_{i<|X|} \tau_0(X,i),\ \sum_{i<|X|} \tau_1(X,i)\Bigr) + 3F\Bigr).$$

In Lean, the worker is a [[Combo.Controller.Worker]] with a [[Combo.Refinement.WorkerModel]] satisfying [[Combo.Refinement.Visits.Correct]], the charges satisfy [[Combo.Analysis.WellBehaved]], and the policy is a [[Combo.Online.Prepared]] run by [[Combo.Online.execute]] from the optional state `none`. The execution is a [[Pointer.Execution]] from `T`, in which every request starts at the root. The policy is chosen before the sequence (`∃ p, ∀ xs`), and the smaller of the two sums is chosen only in the proof.
```

The chapter has two layers. A reader who wants the statement can stop at the box above, or at [Chapter 33](combining.html) for the window version. The rest explains the construction in the order of its proof. The first section gives the overview and the constants. Then come the refinement of worker steps onto shared nodes, the online state and one request, preparation and the treatment of the first request and of empty input, the whole-prefix bound, the window bound for the actual run, and finally how the combined policy is packaged back into a worker, so that it can itself be combined again. The last section lists what is not claimed.

The definitions are in `Algorithms/Combination/Refinement/Definitions/Abstract.lean`, `Refinement/Visits/Definitions/Abstract.lean`, `Online/Definitions/Abstract.lean`, `Online/Startup/Definitions/Abstract.lean`, `Online/Algorithm/Abstract.lean` and `Online/Replay/Definitions/Abstract.lean`. The theorems are in `Refinement/Abstract.lean`, `Online/Abstract.lean` and `Online/Replay/Abstract.lean`.

## Overview

Combo-BST has four levels of description. Each level refines the one above, and each refinement multiplies the cost by a constant.

```text
  controller run        worker units: steps + restore charges      (Chapters 34–35)
        │  ×15 per step, restore ≤ 841 n
        ▼
  shared-node trace     2 fingers on one labelled tree buffer       (Chapters 50–51)
        │  ×524 per instruction (finger hand, 2 fingers + root anchor)
        ▼
  pointer execution     one cursor, every request from the root    (Chapters 6, 43)
```

Throughout, $T$ is the common initial tree (`saved`), $n = |T|$ its size, and requests are inorder ranks less than $n$. The overhead $F$ (`overhead`) is the one of the well-behaved charges, and the hypothesis $n \le F$ is the paper's $f(n) \ge n$. The controller uses round budget $B = (C_1 + 1)F$ ([[Combo.Analysis.budget]]) and restore charge $57F$. The constants in the statements come from the following facts.

| Constant | Meaning |
|---|---|
| $15$ | shared-node cost of one worker step: a maintained rotation updates interval metadata and costs 15 |
| $841\,n$ | shared-node cost of one streaming restoration of the snapshot |
| $57$ | restore factor: $841\,n \le 15 \cdot 57 F$ because $n \le F$ and $841 \le 855$ |
| $1088\,n$ | shared-node cost of startup: initializing the node fields and saving the snapshot |
| $524$ | finger-hand cost per multi-finger instruction with two fingers, $344 + 60\cdot 3$ ([Chapter 43](finger-hands.html)) |
| $8384$ | $16 \cdot 524$: pointer cost per worker unit of a request, including its request unit |
| $570112\,n$ | $524 \cdot 1088\, n$: the pointer cost of preparation |
| $32\,n$ | upper bound on the potential carried by a maintained hand |

The logical analysis, which compares controller work with $\min(\tau_0, \tau_1)$, is in [Chapter 33](combining.html) and [Chapter 35](combo-rounds.html): [[Combo.Analysis.Results.minimum_bound]] for prefixes and [[Combo.Analysis.Results.executed_window]] for windows. This chapter multiplies those bounds by the refinement constants, and makes sure that the multiplication is applied to one fixed online execution, not to a family of executions chosen after the input.

## Workers on shared nodes

The paper's Combo-MFBST keeps the initial tree state in a *tree state buffer* and runs the source algorithm with further fingers in the same tree ([Chapter 50](tree-buffers.html), [Chapter 51](snapshots.html)). The library's refinement says what an abstract worker must provide to be run that way, and what the shared-node trace then costs.

### A pointer interpretation of the worker

@decl RotationBST.Combo.Refinement.WorkerModel RotationBST.Combo.Refinement.WorkerModel.restart_ready RotationBST.Combo.Refinement.WorkerModel.restart_cursor RotationBST.Combo.Refinement.WorkerModel.size RotationBST.Combo.Refinement.WorkerModel.step_ready RotationBST.Combo.Refinement.WorkerModel.step_cursor

A `WorkerModel worker saved` interprets every worker state, on each side, as a pointer configuration ([[Pointer.Config]]): the tree the source algorithm currently has, and where its cursor is. `Ready` is an invariant of the reachable states. `instruction side state x` is what the next charged step does physically: either one opcode of [[Multifinger.Opcode]] at the cursor, or nothing (`none`), for a step of pure local bookkeeping. The fields say:

- `restart_ready`, `restart_cursor`: the restart state of each side is ready, and its cursor is the root of `saved`. Both sources therefore start from the same tree, which is the tree the snapshot holds.
- `size`: ready states keep the key set, so the cursor's tree always has $n$ nodes.
- `step_ready`, `step_cursor`: on a valid request, a step keeps readiness, and moves the cursor exactly as its instruction says. A `some op` step is the legal instruction [[Multifinger.perform]]` op`; a `none` step leaves the cursor where it is.

So a model is *causal*: each step's physical effect is determined by the current state and the current request. It does not say that the worker serves requests correctly. That is the next definition.

### Visiting the requested key

@decl RotationBST.Combo.Refinement.Visits.Boundary RotationBST.Combo.Refinement.Visits.Seen RotationBST.Combo.Refinement.Visits.Correct

`Boundary worker n side state` says that `state` is reached from the restart state of `side` by completing some valid requests (a [[Combo.Worker.Requests]]). It is a proof certificate, not data the algorithm stores. `Seen model side x count state` says that the cursor stands on key $x$ at some point during the next `count` steps on request $x$, counting the starting and the final cursor. `Correct model` is the request contract of the source algorithms: from every reachable boundary, every complete access of a valid key ([[Combo.Worker.Access]]) visits that key with the cursor. The access may continue working after the visit, as [[Pointer.Serves]] allows.

The contract is imposed only at reachable boundaries, and only on the source algorithms. It says nothing about the controller, which interrupts accesses at arbitrary points. That an interrupted and restarted run still visits each key is proved, not assumed.

### The representation invariant

@decl RotationBST.Combo.Refinement.Represents

`Represents model data actual side state` ties a worker state to a two-finger [[TreeBuffer.Shared.State]]. The worker state is ready, the shared tree is valid with node payloads `data` ([[TreeBuffer.Shared.State.Valid]]), its plain shape is the cursor's tree, and finger 0 stands on the cursor's key. Finger 1 is free: it holds the scan position of the snapshot. Both fingers denote nodes of the same tree, so there is never a second copy of the tree.

### What a refined run costs

The following theorems lift worker steps, attempts, services and whole controller runs to shared-node traces ([[TreeBuffer.Shared.Trace]]). Each has the same shape: given a representing shared state, there is a trace to a state that represents the next logical state, every cell event of the trace is a correct read of `data` ([[TreeBuffer.Snapshot.Streaming.Refinement.Reads]]), and the cost is bounded.

**Theorem (one step, one attempt).** One worker step on a valid request costs at most $15$ on shared nodes and leaves finger 1 in place. An attempt of $w$ steps costs at most $15w$.

@decl RotationBST.Combo.Refinement.Results.worker_step RotationBST.Combo.Refinement.Results.attempt

**Theorem (restart).** If the payloads hold the snapshot of `saved` ([[TreeBuffer.Snapshot.CellIO.Stored]]), the shared tree can be restored to the restart state of either side at cost at most $841n$, reading only snapshot cells.

@decl RotationBST.Combo.Refinement.Results.restart

The restored worker may be on the other side (`nextSide`): this is the switch of the controller. The cost does not depend on how far the interrupted worker had moved the tree.

**Theorem (service and execution).** Suppose the restore charge pays for a restoration, $841n \le 15 \cdot \mathit{restore}$. Then one controller service ([[Combo.Controller.Service]]) with logical work $w$, including its restore charge, costs at most $15w$ on shared nodes, and so does a whole controller execution ([[Combo.Controller.Execution]]) of logical work $w$.

@decl RotationBST.Combo.Refinement.Results.service RotationBST.Combo.Refinement.Results.execution

**Theorem (refined minimum bound).** With well-behaved charges, budget $(C_1 + 1)F$ and restore charge $rF$, a controller execution from the initial state, refined onto shared nodes, costs at most $15(C_1 + 1 + r)\bigl(2C_0 \min(\textstyle\sum\tau_0, \sum\tau_1) + 3F\bigr)$.

@decl RotationBST.Combo.Refinement.Results.execution_bound

This is [[Combo.Analysis.Results.minimum_bound]] multiplied by $15$.

**Theorem (refined startup).** For a nonempty tree with $n \le F$ and any valid sequence $X$, there is a startup that initializes the node fields and saves the snapshot ([[TreeBuffer.Snapshot.Startup.Execution]]), after which the controller with restore charge $57F$ runs on $X$ without failure, and the refined run represents its final state. The startup and the run together cost at most $1088n + 15(C_1 + 58)\bigl(2C_0 \min(\sum\tau_0, \sum\tau_1) + 3F\bigr)$ on shared nodes.

@decl RotationBST.Combo.Refinement.Results.startup

This is the shared-node form of the combination, the paper's Combo-MFBST. Its arguments `fields` and `data` are the arbitrary initial contents of the extra node fields. Note the quantifiers: the sequence `xs` is a parameter, and the trace, the snapshot data and the final state are existential *after* it. So this is a statement about one sequence at a time, an offline witness. The rest of the chapter removes that dependence.

## The online state and one request

The online policy carries the logical controller state, the shared-node state and a finger hand together, with certificates that they agree.

@decl RotationBST.Combo.Online.Contract RotationBST.Combo.Online.Contract.correct RotationBST.Combo.Online.Contract.stored RotationBST.Combo.Online.Contract.paid RotationBST.Combo.Online.Contract.fresh

A `Contract` collects the fixed obligations of one run: the visit contract of the sources, the snapshot stored in the payloads `data`, the restore charge paying for restoration, and [[Combo.Controller.FreshBound]], which says that every valid request completes within one budget from a fresh restart. None of them mentions future requests.

@decl RotationBST.Combo.Online.State RotationBST.Combo.Online.State.represented RotationBST.Combo.Online.State.boundary RotationBST.Combo.Online.State.handRep RotationBST.Combo.Online.State.left_le

A `State` has three data fields: the controller state, the actual two-finger shared state, and a [[FingerHand.Hand]]. The physical BST is `hand.tree`. The four certificates say that the shared state represents the current worker state, that the worker state is at a request boundary, that the hand represents the erased shared state ([[FingerHand.Hand.Represents]], [Chapter 43](finger-hands.html)), and that the remaining budget is at most $B$. The certificates are invariants, not stored history.

@decl RotationBST.Combo.Online.Transition

`Transition restore s x result` is the specification of one request $x$ from the state `s`. The result is a next state and a pointer cost. It requires:

1. the controller part is exactly [[Combo.Controller.serve]] on $x$, so the logical run is the one of [Chapter 35](combo-rounds.html);
2. the hand trees are related by a legal [[Pointer.Serves]] of $x$ at the reported cost: a search from the root that visits $x$, possibly continues working, and pays one unit for the request;
3. the amortized bound: cost plus the new hand potential is at most $8384$ times the logical work of the service plus the old hand potential;
4. the shared state performs a [[TreeBuffer.Shared.Requests.Visit]] of $x$ (some finger stands on $x$ during the trace), reading only correct cells, at shared cost at most $15$ times the logical work.

The logical work includes the failed attempt and the restore charge when the request triggers a switch.

**Theorem (every request completes, and has a transition).** Under a contract, the controller completes every valid request, and every valid request has a transition.

@decl RotationBST.Combo.Online.Results.completes RotationBST.Combo.Online.advance_exists

Completion uses `fresh`: if the current round fails, the other side starts fresh with the full budget and completes. The transition is built from the shared-node service, the visit theorem for interrupted runs, and the finger hand's simulation of one multi-finger request, `FingerHand.Hand.simulate_serves`.

@decl RotationBST.Combo.Online.advance RotationBST.Combo.Online.run

`advance contract s x` *chooses* one transition for $x$ from $s$, by classical choice. It sees only the current state and the current request. On an invalid key it returns `(s, 0)`, a totalization that the theorems never use. `run` threads `advance` through a list and adds the costs. Classical choice is a legitimate online rule in the abstract BST model, where planning is free, but it is not an executable program.

@decl RotationBST.Combo.Online.Results.advance_spec RotationBST.Combo.Online.Results.run_append RotationBST.Combo.Online.Results.run_spec RotationBST.Combo.Online.Results.stored_potential

`advance_spec` says that the chosen step satisfies `Transition`. `run_append` is exact composition: running $X \cdot Y$ is running $X$ and then $Y$ from where $X$ left off, with the costs added. Since appending requests cannot change the run on the prefix, `run` is online. `run_spec` sums the transitions: the logical part is a controller execution of some work $w$, the physical part is a [[Pointer.Execution]] between the two hand trees, and the cost plus the final potential is at most $8384w$ plus the initial potential. `stored_potential` bounds the potential of any maintained hand by $32n$, so the potential never costs more than a linear term.

## Preparation, the first request, and empty input

Before the first request, the snapshot must be saved and the hand built. The library fixes this preparation once, independently of the requests.

@decl RotationBST.Combo.Online.Prepared RotationBST.Combo.Online.Prepared.contract RotationBST.Combo.Online.Prepared.controller_initial RotationBST.Combo.Online.Prepared.setup RotationBST.Combo.Online.Prepared.saveBound RotationBST.Combo.Online.Prepared.trace RotationBST.Combo.Online.Prepared.charged

A `Prepared model budget restore fields oldData` consists of:

- the snapshot payloads `data` and a `contract` for them;
- the starting online `state`, whose controller is [[Combo.Controller.initial]] (`controller_initial`), on side $A_0$ with a full budget;
- the shared-node startup `setup` from the original fields `fields` and payloads `oldData`, with its events and its cost `saveCost` $\le 1088n$ (`saveBound`);
- a pointer trace ([[Pointer.Trace]]) of cost `cost` from the root of `saved` to the root of the starting hand tree (`trace`), with cost plus the starting hand potential at most $524 \cdot$`saveCost` (`charged`).

The pointer trace is the physical preparation: the single cursor carries out the simulated startup. It starts and ends at the root, so it can be prepended to a search.

@decl RotationBST.Combo.Online.Prepared.current RotationBST.Combo.Online.Prepared.controller

The policy's state is an `Option`: `none` means that nothing has happened yet, and the BST is still `saved`; `some ready` means that preparation has run, and the BST is `ready.hand.tree`. `current` reads off the physical tree, and `controller` the logical controller state, which for `none` is the initial one.

@decl RotationBST.Combo.Online.preparation_exists RotationBST.Combo.Online.prepare

**Theorem (preparation exists).** For a nonempty tree, a visit-correct model, a budget satisfying the fresh bound and a restore charge paying for restoration, a preparation exists, for any initial node fields.

`prepare` chooses one. Its arguments contain no request sequence, so the choice is made before any request is presented.

@decl RotationBST.Combo.Online.access RotationBST.Combo.Online.execute

`access p s x` serves one request. From `none`, it advances from the prepared state and charges the preparation cost `p.cost` together with the cost of the request: **preparation is paid on the first request**. From `some ready`, it just advances. `execute` threads `access` through a list. On the empty list it returns the state unchanged at cost $0$, so preparation is never inserted into an empty input, and an empty continuation costs nothing.

**Theorem (composition of the online policy).** Executing from a prepared state is `run`; executing from `none` on a nonempty list is `run` from the prepared state plus the preparation cost; and executions compose exactly over concatenation.

@decl RotationBST.Combo.Online.Results.execute_ready RotationBST.Combo.Online.Results.execute_first RotationBST.Combo.Online.Results.execute_append

`execute_append` makes the policy online in the precise sense used below: the state and cost after a prefix do not depend on the requests that follow.

**Theorem (the policy serves every valid sequence).** For every valid sequence $X$, the run of a prepared policy from `none` is a legal pointer execution of $X$ from `saved`, refining a controller execution of logical work $w$ from the initial state, with total cost at most $524 \cdot \mathit{saveCost} + 8384w$.

@decl RotationBST.Combo.Online.Results.execute_spec

For a nonempty sequence, the first request's search is the preparation trace followed by the simulated search, so the whole run is one [[Pointer.Execution]] from `saved`. For the empty sequence the execution is empty and the bound is trivial.

**Theorem (continuing from any state).** The remaining budget of any optional state is at most $B$. From any optional state, the continuation on a valid sequence is a legal pointer execution between the actual trees, refining a controller execution of logical work $w$ from that state, at cost at most $570112n + 8384w$.

@decl RotationBST.Combo.Online.Results.remaining_budget RotationBST.Combo.Online.Results.execute_from

The additive term covers both cases at once. From `none`, it pays for the preparation, $524 \cdot 1088n$. From a prepared state, it pays for the carried hand potential, at most $32n$, which a continuation cannot assume to be zero.

## Whole prefixes

**Theorem (prefix bound for a prepared policy).** Let the charges be well-behaved, and let $p$ be prepared with budget $(C_1 + 1)F$ and restore charge $rF$. For every valid sequence $X$, the run of $p$ is a legal pointer execution of $X$ from `saved`, with cost at most

$$524 \cdot 1088\,n + 8384\,(C_1 + 1 + r)\Bigl(2C_0 \min\bigl(\textstyle\sum_i \tau_0(X,i), \sum_i \tau_1(X,i)\bigr) + 3F\Bigr).$$

@decl RotationBST.Combo.Online.Results.minimum_bound

This is `execute_spec` combined with [[Combo.Analysis.Results.minimum_bound]]. The sums are [[Combo.Analysis.total]], the charges of the whole sequence.

**Theorem (one policy for all prefixes).** The headline statement: for a nonempty tree with $n \le F$ and a visit-correct model with well-behaved charges, there is one prepared policy with budget $(C_1 + 1)F$ and restore charge $57F$ that satisfies the bound above, with $r = 57$, for every valid sequence.

@decl RotationBST.Combo.Online.Results.prefix_policy

The proof takes $p$ to be `prepare` with budget $(C_1 + 1)F$ and restore charge $57F$. The fresh bound comes from the single-access clause of [[Combo.Analysis.WellBehaved]] ($C_1 F \le B$), and the restore condition from $n \le F$. So the policy depends on $F$ and $C_1$, but not on $C_0$, on the charges, or on the requests. Which of the two sums is smaller is decided only in the proof. The bound holds for every prefix of an infinite online sequence at once, since the run on a prefix is the beginning of the run on the whole.

## Windows of the actual run

Theorem 3 of the paper is stronger than a prefix bound. It bounds the cost that Combo-BST spends on any contiguous window $X' = (x_{lo}, \dots, x_{hi-1})$ of the input $X$, *within its run on $X$*, by the amortized charges that the sources assign to the requests of $X'$ as part of $X$. The library proves exactly this for the actual run of the fixed policy.

**Theorem (the run splits at a window).** For every sequence $X$ and $lo \le hi$, the run of a prepared policy on $X$ is the run on the prefix $X[0, lo)$, followed by the run on the window $X[lo, hi)$ from the state the prefix left, followed by the run on the suffix $X[hi, |X|)$ from the state the window left. The final state is that of the suffix, and the cost is the sum of the three costs.

@decl RotationBST.Combo.Online.Results.execute_window_split

The window is [[Combo.Analysis.segment]]` xs lo hi`. The three parts are not three runs started afresh: the middle starts from the actual state after the prefix, the suffix from the actual state after the middle. In particular the window is not rerun from the saved tree, and the controller is not reset at $lo$.

**Theorem (window bound from any state).** Let the charges be well-behaved and $p$ be prepared with budget $(C_1+1)F$ and restore charge $rF$. From any optional state $s$, the run of $p$ on the window $X[lo, hi)$ of a valid sequence $X$ is a legal pointer execution between the actual trees, with cost at most

$$570112\,n + 8384\,(C_1 + 1 + r)\Bigl(2C_0^2 \min\bigl(M_0, M_1\bigr) + (2C_0C_1 + 5)F\Bigr), \qquad M_j = \sum_{lo \le i < hi} \tau_j(X, i).$$

@decl RotationBST.Combo.Online.Results.window_bound

$M_j$ is [[Combo.Analysis.mass]]` charges j xs lo hi`. The charges are those of **the original sequence $X$ at the original indices $i$**: $\tau_j(X, i)$ may depend on all of $X$, in particular on the history before $lo$. They are not the charges of the window viewed as a standalone sequence. The proof first compares the controller's work with the window's standalone charges, from an arbitrary controller state ([[Combo.Analysis.Results.state_bound]]), and then uses the stability clause of [[Combo.Analysis.WellBehaved]] to convert those into original charges; this second comparison is where $C_0^2$ and the term $2C_0C_1F$ come from ([[Combo.Analysis.Results.window_bound]]). The state $s$ is arbitrary, not necessarily one reached by the policy.

**Theorem (executed window).** For a prepared policy $p$ as above, a valid sequence $X$ and $lo \le hi \le |X|$, write $\mathit{first}$, $\mathit{middle}$, $\mathit{last}$ for the runs on the prefix, window and suffix as in the split. Then the run on $X$ is their exact composition, the middle is a legal pointer execution of $X[lo, hi)$ from the actual tree after the prefix to the actual tree after the window, and the middle cost satisfies the window bound.

@decl RotationBST.Combo.Online.Results.executed_window

The physical trees `p.current first.1` and `p.current middle.1` are the trees of the run on $X$ at times $lo$ and $hi$. If $lo = 0$ the first is `saved`, and the middle includes the preparation; otherwise the middle starts from a prepared state and carries its hand potential. Both are covered by $570112n$. If $lo = hi$ the middle is empty and costs $0$.

Finally, the policy is fixed before both the requests and the window, and the linear term is absorbed into the overhead.

**Theorem (Theorem 3, abstract form).** Let $T$ be a nonempty tree on $n$ keys, and let the worker have a visit-correct pointer interpretation and well-behaved nonnegative charges $\tau_0, \tau_1$ with constants $C_0, C_1$ and overhead $F \ge n$. Then there is one prepared policy $p$ with budget $(C_1 + 1)F$ and restore charge $57F$ such that, for every sequence $X$ of keys in $\{0, \dots, n-1\}$:

1. the run of $p$ on $X$ is a legal pointer execution from $T$; and
2. for every $lo \le hi \le |X|$, the run on $X$ splits exactly into prefix, window and suffix as above, the window part is a legal pointer execution between the actual trees at times $lo$ and $hi$, and its cost is at most

$$8384\,(C_1 + 58)\Bigl(2C_0^2 \min\Bigl(\sum_{lo \le i < hi} \tau_0(X, i),\ \sum_{lo \le i < hi} \tau_1(X, i)\Bigr) + (2C_0C_1 + 73)F\Bigr).$$

@decl RotationBST.Combo.Online.Results.window_policy

This is `executed_window` with $r = 57$, and $570112n = 8384 \cdot 68\, n \le 8384(C_1 + 58) \cdot 68F$, which turns $(2C_0C_1 + 5)F$ into $(2C_0C_1 + 73)F$. In the paper's notation, the cost of Combo-BST on the window $X'$ of $X$ is $O(\min(T_{X'}(A_0, T, X), T_{X'}(A_1, T, X)) + f(n))$, with explicit constants. The smaller source can differ from one window to another; the bound holds for all windows of the same run.

## The combined policy as a worker

To combine more than two algorithms, the paper combines them two at a time in a balanced binary tree. That needs the output of one combination to be an input of the next: a [[Combo.Controller.Worker]] with a pointer interpretation and well-behaved charges. The `Replay` layer provides this. It is used by the finite families of [Chapter 33](combining.html) and by the combined finger bound of [Chapter 38](combined-finger.html). A reader interested only in two algorithms can skip this section.

@decl RotationBST.Combo.Online.Replay.Implementation RotationBST.Combo.Online.Replay.Implementation.initial RotationBST.Combo.Online.Replay.Implementation.tree RotationBST.Combo.Online.Replay.Implementation.expansion

An `Implementation p` is a [[Combo.Worker.Replay.Planner]] whose states are the optional states of $p$. A planner turns each request into an explicit list of pointer opcodes from the root back to the root, and [[Combo.Worker.Replay.worker]] executes that list one opcode per worker step, with one unit to plan and one to report completion. The fields say that the planner starts at `none` on both sides, that its tree is `p.current`, and that each planned request reaches the same state as `access p` with at most twice its cost, counting the two extra units. Both sides of the replay worker run the same policy $p$.

@decl RotationBST.Combo.Online.Replay.chargeFactor RotationBST.Combo.Online.Replay.overheadFactor RotationBST.Combo.Online.Replay.scaledCharges

These are the constants of the inherited bound. `chargeFactor` multiplies the charges, `overheadFactor` multiplies $F$, and `scaledCharges factor charges` multiplies every charge by `factor`. They are explicit, so that a balanced family can compute its constants by recurrence.

**Theorem (replay implementations).** Every prepared policy has an implementation. Its replay run on any valid sequence ends in the same state as the policy, at most twice the cost; as a worker from its restart state it completes every valid sequence at most at twice the policy's cost; and a single access from any reachable boundary costs at most $1140224n + 16768(2B + \mathit{restore})$.

@decl RotationBST.Combo.Online.Replay.Results.implementation_exists RotationBST.Combo.Online.Replay.Results.run_bound RotationBST.Combo.Online.Replay.Results.requests RotationBST.Combo.Online.Replay.Results.single

The single-access bound is the worst case of one request: at most one failed round, one restoration and one fresh round, plus the preparation if the request is the first one. The factors $16768 = 2 \cdot 8384$ and $1140224 = 2 \cdot 570112$ are the factor 2 of the replay applied to the policy's constants.

**Theorem (the replay worker inherits the bounds).** The replay worker completes every valid sequence from its restart state at cost at most $1140224n + 16768(C_1 + 1 + r)\bigl(2C_0\min(\sum\tau_0, \sum\tau_1) + 3F\bigr)$. If $n \le F$, it is well-behaved with overhead `overheadFactor` $\cdot F$, constants $C_0$ and $C_1 + 1$, and charges `chargeFactor` $\cdot\,\tau$, where side $j$ of the replay worker may inherit the charges of either source, chosen by `select`.

@decl RotationBST.Combo.Online.Replay.Results.minimum_bound RotationBST.Combo.Online.Replay.Results.well_behaved_selection RotationBST.Combo.Online.Replay.Results.well_behaved

`well_behaved` is the case where side $j$ inherits $\tau_j$. Since both sides run the same policy, either choice is valid: the combined worker is well-behaved with respect to the scaled charges of $A_0$ and also with respect to those of $A_1$. The minimum is not a charge function itself; it reappears when the combined worker is combined again.

**Theorem (one combination step).** For a nonempty tree with $n \le F$, a visit-correct model and well-behaved charges, there are a prepared policy with restore charge $57F$ and an implementation whose replay worker is again visit-correct and well-behaved, with overhead `overheadFactor C₀ C₁ 57` $\cdot F$, constants $C_0$ and $C_1 + 1$, and charges `chargeFactor C₀ C₁ 57` $\cdot\,\tau$.

@decl RotationBST.Combo.Online.Replay.Results.combine

This is the induction step of the balanced family: the output worker satisfies the same hypotheses as the inputs, with $C_1$ increased by one and the charges and overhead multiplied by explicit factors. Iterating it compounds those factors from level to level, so the library does not obtain the paper's $O(k)$ overhead for $k$ algorithms.

## What is and is not claimed

::: caveat Hypotheses on the sources
The theorems assume a [[Combo.Refinement.WorkerModel]] (a causal pointer interpretation of both sources on the common initial tree), [[Combo.Refinement.Visits.Correct]] (every access visits its key), and [[Combo.Analysis.WellBehaved]] charges, including the single-access bound, the complete-run upper bound and the stability of contiguous segments. These are operational hypotheses on the input workers. An arbitrary BST algorithm does not satisfy them automatically: each application must prove them, as [Chapter 38](combined-finger.html) does for GreedyASS and Tango.
:::

::: check
- **Cost.** The cost is that of a [[Pointer.Execution]]: pointer instructions, moves and rotations alike, plus one unit per request. Every request starts at the root of the current tree. Snapshot reads, restorations and hand maintenance are all paid in pointer instructions.
- **Online.** The policy is one fixed object, chosen before the requests and before the window (`∃ p, ∀ xs, ∀ lo hi`), and its run on a prefix is the beginning of its run on every extension (`execute_append`). The individual steps are chosen by classical choice from the current state and request. Planning is free, as everywhere in the abstract BST model, and the policy is noncomputable.
- **Startup.** The initial tree is fixed, both sources start from it, and it must be nonempty. Preparation is charged once, on the first request; on an empty input nothing is charged.
- **Charges.** Charges are functions $\tau_j(X, i)$ of the whole sequence and the index, nonnegative and real-valued. Window bounds use the charges of the original sequence at the original indices.
:::

::: caveat Compared with the paper
- The paper's "real-world" clauses of Theorems 3 and 5, that Combo-BST uses only $O(\log n)$ bits per node and $O(1)$ registers when the sources do, are not formalized. The online state contains abstract certificates, and the replay worker keeps its pending opcode list as abstract state.
- The sharper $O(k)$ overhead of the paper's balanced family is not claimed; see the family statements in [Chapter 33](combining.html).
- The constants are explicit and large. They come from composing generic simulations, not from a tuned implementation.
- Corollary 4, which combines specific known bounds, is not derived in full. [Chapter 38](combined-finger.html) uses this chapter's results for one combination, GreedyASS with Tango.
:::
