# Interruptible workers

ComboBST, the combined search tree of [Chapter 33](combining.html), runs two online BST algorithms $A_0$ and $A_1$ in alternating rounds. A round has a fixed budget of $C_3 f(n)$ operations. When the budget runs out, the round usually stops in the middle of a request. The combined tree then restores the initial tree, switches to the other algorithm, and re-runs the interrupted request from scratch on that side. To describe this precisely, an input algorithm cannot be a black box that serves one whole request per call. It must be presented so that it can be run one charged unit at a time, stopped at any unit, and either resumed or abandoned. The library calls such a presentation a **worker**.

This section collects what the library knows about workers *as inputs*:

- the facts that hold for every worker, whatever algorithm it implements (determinism of a request, budgets and closed rounds);
- the **replay adapter**, which turns an ordinary online algorithm into a worker, together with its pointer interpretation and the proof that its requests are served correctly;
- the **pair** construction, which puts two workers with different state types behind one state type, as the controller requires.

The controller that schedules the rounds is the subject of [Chapter 35](combo-rounds.html), and the single online pointer execution built from it is the subject of [Chapter 36](combo-online.html). Both take a worker as their input and assume the hypotheses discussed here. A reader interested only in Theorem 3 can read the statement in [Chapter 33](combining.html) and return here for one question: what must an input algorithm satisfy, and which of those requirements are already proved for ordinary online algorithms? The box below answers the second half.

```headline combo-workers-replay
title: Every online BST algorithm gives a worker, well-behaved for stable charges that dominate its cost
source: Demaine, Iacono, Langerman and Özkan, *Combining binary search trees* (2013)
theorems: Combo.Worker.Replay.Results.algorithms_well_behaved Combo.Worker.Replay.Results.correct

Let $A_0, A_1$ be two online algorithms of the rotation model ([Chapter 5](online.html)) and let $T$ be a tree on $n$ keys. There is one interruptible replay worker for the pair, fixed before any charges, overhead or constants are chosen, with the following property. Take any overhead $f \ge n$, any constants $C_0$ and $C_1 \ge 20$, and any nonnegative charges $\tau_\mu(X, i)$ (the charge of the $i$-th request of $X$ on side $\mu$) such that, for every sequence $X$ of keys below $n$,

$$64 \cdot \bigl(|X| + \mathrm{rot}_{A_\mu}(T, X)\bigr) \;\le\; \sum_{i<|X|} \tau_\mu(X, i) + f,$$

and, for every contiguous segment $X[lo, hi)$,

$$\sum_{i} \tau_\mu\bigl(X[lo,hi), i\bigr) + f \;\le\; C_0 \sum_{lo \le i < hi} \tau_\mu(X, i) + C_1 f.$$

Then the worker satisfies the operational well-behavedness contract [[Combo.Analysis.WellBehaved]] with these parameters. Every step of the worker is either one legal pointer instruction or local bookkeeping, and every valid request it completes from a reachable request boundary moves the cursor over the requested key ([[Combo.Refinement.Visits.Correct]] for [[Combo.Worker.Replay.model]]).

The cost on the left of the first inequality is [[RotationBST.Algorithm.totalCost]]: one unit per request plus rotations. The factor $64$ is the price of the translation to the pointer machine. The single-request bound of well-behavedness ($C_1 f$ per access from any reachable state) is not a hypothesis here: the worker caps every request at $20n$ units.
```

So the three hypotheses that Theorem 3 places on its input workers (a pointer interpretation, request service, and well-behavedness) reduce, for an ordinary rotation-model algorithm, to the paper's own assumption: an amortized bound that dominates the algorithm's cost (here, $64$ times its total cost) and is stable on contiguous segments. That reduction is the content of the box, proved in [Section 34.3](#from-an-online-algorithm-to-a-worker-replay). The GreedyASS and Tango sources of [Chapter 38](combined-finger.html) enter the combination as replay workers of this kind.

The Lean sources are in `Algorithms/Combination/Worker/`: `Definitions/Abstract.lean` and `Abstract.lean` for the general facts, `Replay/` for the adapter, and `Pair/` for the pairing.

## What a worker is

The worker structure itself, [[Combo.Controller.Worker]], is shown with the controller in [Chapter 35](combo-rounds.html). It has two fields:

- `restart side : σ`, the worker state right after the initial tree has been restored, for side `side`;
- `step side s x : σ × Bool`, one charged unit of work on the current request `x` from state `s`, returning the new state and a **completion bit**.

A worker is indexed by a side `side : Bool`. It is really two workers, one for $A_0$ (`false`) and one for $A_1$ (`true`), sharing one state type `σ`. A step sees only the current state and the current request, never the future, so a worker is causal by construction. Nothing in the structure says what a unit *is*; that is the job of a separate pointer interpretation ([[Combo.Refinement.WorkerModel]], [Chapter 36](combo-online.html)), which says that each step performs at most one pointer instruction.

The controller runs a worker on one request with a fuel budget, using [[Combo.Controller.attempt]], or its relational form [[Combo.Controller.AttemptRun]]. An attempt calls `step` until the completion bit is set or the fuel is exhausted, and returns an [[Combo.Controller.Attempt]]: the state reached, the fuel left, and whether the request completed. A failed attempt keeps its partial state. The controller then discards it by restoring the initial tree, which is why the interface has `restart` rather than any way to roll back.

A round on side $\mu$, with budget $B$ and requests $x_1, x_2, \dots$, looks like this:

```
side μ,   budget B:   | x₁ ✓ | x₂ ✓ |  x₃ ✓  | x₄ · · · · ·  (budget exhausted: x₄ interrupted)
restore the initial tree, switch sides
side 1−μ, budget B:   |     x₄ ✓     | x₅ ✓ | x₆ · · · · · ·
```

When the budget suffices for any single request from a fresh restart, as [Chapter 35](combo-rounds.html) assumes, each request is completed by exactly one round, and the interrupted request is shared by two consecutive rounds. (If the second attempt also fails, the controller reports a failure; it never counts the request as served.) The library's convention, used throughout, is that the closing round *includes* its interrupted request, even when its budget was already zero when the request arrived.

### What is proved and what is assumed

This is the most important distinction in the section.

| Property | Status |
|---|---|
| A completed request is deterministic: its final state and cost do not depend on the fuel ([[Combo.Worker.Results.completed_unique\|completed_unique]]) | proved for every worker |
| A failed attempt had less fuel than the request needs ([[Combo.Worker.Results.failed_lt_complete\|failed_lt_complete]]) | proved for every worker |
| Each completed request costs at least one unit ([[Combo.Worker.Results.Requests.length_le_cost\|length_le_cost]]) | proved for every worker |
| A closed round's budget is less than the cost of completing its requests ([[Combo.Worker.Results.ClosedRound.lower_bound\|lower_bound]]) | proved for every worker |
| A pointer interpretation: each step is one legal instruction or none ([[Combo.Refinement.WorkerModel]]) | hypothesis of Theorem 3; proved for replay workers ([[Combo.Worker.Replay.model]]) |
| Request service: a completed request visits its key ([[Combo.Refinement.Visits.Correct]]) | hypothesis of Theorem 3; proved for replay workers ([[Combo.Worker.Replay.Results.correct\|correct]]) |
| Well-behaved charges: nonnegativity, single-request bound, complete-run bound, segment stability ([[Combo.Analysis.WellBehaved]]) | hypothesis of Theorem 3; for replay workers of rotation-model algorithms, reduced to a cost bound and segment stability of the charges ([[Combo.Worker.Replay.Results.algorithms_well_behaved\|algorithms_well_behaved]]) |
| Pairing preserves interpretation, service and well-behavedness ([[Combo.Worker.Pair.Results.correct\|correct]], [[Combo.Worker.Pair.Results.well_behaved\|well_behaved]]) | proved |

The segment stability of the charges is never proved by this section. It is a property of the bound being combined, such as the lazy finger bound or Wilber's interleave bound, and is established for those bounds where they are used ([Chapter 33](combining.html), [Chapter 38](combined-finger.html)).

## Facts true of every worker

These results are about an arbitrary [[Combo.Controller.Worker]] and use nothing but its two fields. They are the worker-level half of the paper's counting argument for Theorem 13: every round except the last runs for its whole budget, so the requests it completes would cost the input algorithm *more* than the budget.

### Whole requests

**Definition (access, request sequence).** An access of `x` from state `s` with cost `work` is a successful attempt run with fuel exactly `work`: it completes, ends in state `t`, and has no fuel left. A request sequence is a chain of accesses, with costs added.

@decl Combo.Worker.Access Combo.Worker.Requests

[[Combo.Worker.Access]] is the cost of a request when the worker is run to completion with no controller interference. It is the quantity that well-behavedness bounds. Fixing the fuel to the work makes it a single number; the next theorem shows that any other completing fuel gives the same answer.

**Theorem (determinism of a request).** Two attempts of the same request from the same state that both complete reach the same state with the same work, whatever their fuels. An attempt that fails had strictly less fuel than the work of any completing attempt. A completing attempt with any fuel is an access with the same work.

@decl Combo.Worker.Results.completed_unique Combo.Worker.Results.failed_lt_complete Combo.Worker.Results.to_access

All three follow by induction on the attempt: `step` is a function, and the first completion bit stops the run.

**Theorem (request sequences).** Request sequences compose under concatenation, are unique given the start state and the requests, and cost at least one unit per request.

@decl Combo.Worker.Results.Requests.append Combo.Worker.Results.Requests.unique Combo.Worker.Results.Requests.length_le_cost

### Closed rounds

**Definition (closed round).** A closed round from state `s` with budget `fuel` on a list of requests completes every request but the last, each one with the fuel left by the previous ones, and then fails on the last request with the fuel that remains.

@decl Combo.Worker.ClosedRound

The last request is always in the list, even when it receives zero fuel: the `failed` case allows an exhausted attempt with `fuel = 0`. This matches the coverage convention of the round partition in [Chapter 35](combo-rounds.html), where a closing round contains its interrupted request. No worker step is invented for that request; it merely belongs to the round.

**Theorem (closed rounds are expensive).** If a closed round with budget $B$ covers requests $X$, and the worker can complete all of $X$ from the same state at cost $c$, then $B < c$. A closed round may also be extended at the front by completed requests, adding their cost to its budget.

@decl Combo.Worker.Results.ClosedRound.lower_bound Combo.Worker.Results.ClosedRound.prepend

The lower bound is the strict form of the paper's inequality $T(A_{\min}, T, X'_j) \ge C_3 f(n)$ for every round $j$ but the last.

**Theorem (the first switch closes a round).** Run the controller of [Chapter 35](combo-rounds.html) from a state whose active side is $\mu$, whose worker state is $s$ and whose remaining budget is $\ell$. If the first switch happens at request index `boundary` (the first entry of [[Combo.Rounds.cuts]], counted from `offset`), then the requests up to and including that index form a closed round of side $\mu$ from $s$ with budget $\ell$. Consequently, completing them from $s$ costs more than $\ell$.

@decl Combo.Worker.Results.first_closed Combo.Worker.Results.first_lower_bound

This links the controller's actual behaviour to the worker-level notion. [Chapter 35](combo-rounds.html) applies it round by round, where each fresh round starts from `restart` with the full budget, and turns it into round certificates.

## From an online algorithm to a worker: replay

An online BST algorithm serves one whole request per call. To make it interruptible, the replay adapter asks a **planner** for the complete list of pointer instructions of the current request, then plays them back one per unit. If the round is interrupted, the half-played list is simply abandoned, together with the tree it was building. If the round continues, the adapter finishes the list and moves to the planner's next state.

This is a different decomposition from the paper's, which emulates the input BST operation by operation inside the combined structure. The planning happens in one unit, and the retained list of instructions is abstract state. Both are allowed by the abstract BST model, which charges pointer instructions and does not bound private computation or storage. The real-world storage clause of Theorem 3 is not claimed.

### Planners

A planner works on the pointer machine of [Chapter 6](pointer.html). A [[RotationBST.Pointer.Config]] is a tree with a cursor, and an instruction is one of the six [[RotationBST.Multifinger.Opcode]]s of [Chapter 10](fingers.html), executed by [[RotationBST.Multifinger.replay]].

**Definition (visit).** An instruction list visits key `x` from a cursor if some prefix of it, possibly empty, leads to a cursor on `x`.

@decl Combo.Worker.Replay.Visits

The empty prefix counts, so a request for the root key is visited before any movement.

**Definition (planner).** A planner with state type `σ` for the initial tree `saved` has, for each side, an initial state, a tree represented by each state, and a planning function. Given a state and a request, `plan` returns the next state and the instructions that serve the request. The three conditions say: the initial state represents `saved`; on a tree of the right size and a valid key, the instructions start with the cursor at the root of the current tree and end with the cursor at the root of the next state's tree; and they visit the requested key on the way.

@decl Combo.Worker.Replay.Planner

@decl Combo.Worker.Replay.Planner.initial_tree Combo.Worker.Replay.Planner.legal Combo.Worker.Replay.Planner.visits

A planner is causal: `plan` sees the side, the current state and the current request, and nothing else. The obligations are imposed only on states whose tree has $n$ keys, and only for keys below $n$; the invariant `Ready` below ensures that only such states are reached. Ending each request at the root is a normalization. The pointer machine's own requests ([[RotationBST.Pointer.Serves]]) leave the cursor anywhere, and the next request starts again at the root. The planner pays explicitly for the walk back, which [[Combo.Worker.Replay.Results.rooted]] below bounds.

### The replay worker

**Definition (replay worker).** A replay state is either at a request boundary, holding a planner state, or running, holding the planner's next state, the current cursor and the instructions still to play. One step from a boundary calls the planner and keeps the cursor at the root. Each later step plays one instruction. When none remain, one more step reports completion and moves to the boundary of the next state.

@decl Combo.Worker.Replay.State Combo.Worker.Replay.step Combo.Worker.Replay.worker

A request with a plan of length $k$ therefore costs exactly $k + 2$ units: one to plan, $k$ to play, one to finish. If an instruction were illegal, the step would leave the state unchanged and never report completion, so the attempt would only burn its budget. The pointer invariant below shows that this never happens on reachable states.

For comparisons with the planner, the same computation is also written request by request, without interruption. `run` threads the planner state through a sequence and adds $k + 2$ per request. `policyRun` does the same for an arbitrary causal rule that returns a next state and a cost, which is how a source algorithm is described before it is turned into a planner.

@decl Combo.Worker.Replay.run Combo.Worker.Replay.policyRun

**Theorem (replay serves whole requests at the planner's cost).** From a boundary state whose tree has $n$ keys, a valid request is an [[Combo.Worker.Access]] that ends at the boundary of the planner's next state, at cost plan length plus $2$. A sequence of valid requests is a [[Combo.Worker.Requests]] whose final state and cost are those of `run`.

@decl Combo.Worker.Replay.Results.access Combo.Worker.Replay.Results.requests

### The pointer interpretation

The controller treats a worker as a black box of units. [Chapter 36](combo-online.html) needs more: each unit must correspond to at most one physical pointer instruction, so that the units of the controller become the instructions of one pointer execution. This is the contract [[Combo.Refinement.WorkerModel]]. For a replay worker, the cursor is the root of the planner's tree at a boundary and the current cursor while running, and the instruction of a step is the next one in the list.

@decl Combo.Worker.Replay.cursor Combo.Worker.Replay.Ready Combo.Worker.Replay.instruction

`Ready` is the invariant: at a boundary, the tree has $n$ keys; while running, the next tree has $n$ keys and the remaining instructions really lead from the current cursor to its root. `Ready` holds at `restart` by `initial_tree`, and the planner's `legal` field makes it hold again after the planning step.

**Theorem (the invariant is maintained).** A ready state's cursor tree has $n$ keys. A step on a valid key keeps the state ready. A step either leaves the cursor where it is (planning and completion) or performs exactly the reported instruction.

@decl Combo.Worker.Replay.model_ready_size Combo.Worker.Replay.model_step_ready Combo.Worker.Replay.model_step_cursor

These are the obligations of [[Combo.Refinement.WorkerModel]], packaged into one model:

@decl Combo.Worker.Replay.model

The log of pending instructions is abstract state. No bound on its size, or on the planner state, is asserted.

**Theorem (replay workers serve their requests).** Every request boundary that the worker reaches from `restart` by completing valid requests is a boundary state whose tree has $n$ keys. From such a state, every completed valid request moves the cursor over the requested key during its consumed steps.

@decl Combo.Worker.Replay.Results.request_boundary Combo.Worker.Replay.Results.correct

The second statement is the request-service contract [[Combo.Refinement.Visits.Correct]] for every planner, with no hypothesis. It is a contract on the input worker only: what the combined execution does after an interruption is analysed in [Chapter 36](combo-online.html).

### Building planners from pointer algorithms

The planner interface is close to that of an ordinary online pointer algorithm, except that a request must return to the root.

**Theorem (returning to the root).** If the pointer machine serves `x` from tree `s` to tree `t` at cost `c` (including its request unit), then some instruction list leads from the root of `s` to the root of `t`, visits `x`, and has length at most $2c - 2$.

@decl Combo.Worker.Replay.Results.rooted

The walk back to the root is no longer than the work already done, because each instruction changes the cursor's depth by at most one.

**Theorem (pointer algorithms are planners).** Let `next` be a causal rule that, from each state whose tree has $n$ keys and each valid request, serves the request on the pointer machine and returns a new state and a cost. Then there is a planner with the same initial states and trees whose successor states are those of `next` and whose plans cost at most twice the rule's cost, per request and over any sequence.

@decl Combo.Worker.Replay.Results.planner_exists Combo.Worker.Replay.Results.run_bound

The planner is obtained by choice, so it is a mathematical object, not a program; the abstract model allows this.

### Capping a request at $20n$

Well-behavedness asks that every single access, from every reachable state, cost at most $C_1 f(n)$. In the paper this is part of the assumption on the input algorithms. For replay workers it comes for free, because a request can always be served in linear time while still producing the planner's intended next tree.

**Theorem (a short rooted program always exists).** For any two trees $s$ and $t$ of the same size $n$ and any key $x < n$, some instruction list leads from the root of $s$ to the root of $t$, visits $x$, and has length plus $2$ at most $20n$.

@decl Combo.Worker.Replay.Results.short_rooted

It searches for $x$ from the root and returns, then reshapes $s$ into $t$ with the linear pointer reshaping of [Chapter 6](pointer.html).

**Theorem (capped planners).** Every planner has a capped version with the same initial states, trees and successor states, whose plans are never longer than the original's and cost at most $20n$ each (plan length plus $2$). Over any sequence, the capped planner ends in the same state and costs no more.

@decl Combo.Worker.Replay.Results.bounded_planner Combo.Worker.Replay.Results.refined_run

Because the successor states are unchanged, the capped worker makes the same decisions as the original on every later request. Only the instructions of an expensive request are replaced.

**Theorem (capped replay workers are well behaved).** Let a capped planner be derived from a planner as above. Suppose $n \le f$, $C_1 \ge 20$, the charges are nonnegative, the original planner's cost on every valid sequence from its initial state is at most the total charge plus $f$, and the charges are stable on contiguous segments with constants $C_0, C_1$. Then the capped replay worker satisfies [[Combo.Analysis.WellBehaved]] with $n$, $f$, $C_0$, $C_1$ and these charges.

@decl Combo.Worker.Replay.Results.bounded_well_behaved

Of the four fields of well-behavedness, nonnegativity and segment stability are copied from the hypotheses, which concern the charges alone. The complete-run bound follows from the original planner's bound and [[Combo.Worker.Replay.Results.refined_run]]. The single-access bound follows from the cap: $20n \le C_1 f$.

### Rotation-model algorithms

Combining the pieces gives a worker for any pair of [online algorithms](online.html) of the rotation model. The rotation-model algorithm is first run on the pointer machine by the online lazy simulation of [Chapter 6](pointer.html) ([[RotationBST.Pointer.Lazy.Online.State]]), which costs at most $32$ times its total cost. Returning to the root doubles this, and capping adds the single-access bound.

**Theorem (a planner for every pair of algorithms).** For any two rotation-model online algorithms $A_0, A_1$ and any initial tree $T$ on $n$ keys, there is a planner whose state is the list of past requests together with a lazy-simulation state, whose plans cost at most $20n$ per request, and whose run on any valid sequence $X$ from its initial state on side $\mu$ costs at most $64$ times the total cost of $A_\mu$ on $X$ from $T$.

@decl Combo.Worker.Replay.Results.algorithm_planner

**Theorem (the replay worker is well behaved).** For the same data, one planner can be chosen with the following property. Take any overhead $f \ge n$, any $C_0$, any $C_1 \ge 20$, and any nonnegative charges $\tau$ such that $64\,\mathrm{totalCost}_{A_\mu}(T, X) \le \sum_i \tau_\mu(X, i) + f$ for every valid $X$ and both sides, and such that $\tau$ is stable on contiguous segments with constants $C_0, C_1$. Then the replay worker of that planner satisfies [[Combo.Analysis.WellBehaved]] with $n$, $f$, $C_0$, $C_1$ and $\tau$. This is the statement of the box at the top of the section.

@decl Combo.Worker.Replay.Results.algorithms_well_behaved

The order of quantifiers matters: the planner exists before the charges. This is used in [Chapter 38](combined-finger.html), where the charges of the GreedyASS side depend on a reference tree chosen after the algorithm, and the same worker must serve for all of them.

### The emitted program

The deamortization of [Chapter 37](deamortization.html) also starts from a planner, but uses it differently. It does not interrupt requests; it needs the concatenated stream of instructions, to feed into the bounded-depth finger simulation of [Chapter 49](finger-histories.html).

**Definition (program).** The program of a planner on a sequence is the concatenation of its plans, threading the successor states.

@decl Combo.Worker.Replay.Requests.program

**Theorem (program accounting).** `run` splits over concatenated sequences. The program has length exactly the cost of `run` minus two units per request: the planning and completion units of the interruptible worker, which are bookkeeping, not instructions.

@decl Combo.Worker.Replay.Requests.Results.run_append Combo.Worker.Replay.Requests.Results.program_cost

**Theorem (planners are source algorithms of the simulation).** An instruction list that is legal on the erasure of a labelled cursor ([[RotationBST.LabelledCursor.Config]]) and visits a key also runs on the labelled cursor, with the same erasure, and serves the key in the sense of [[HeavyPath.Finger.History.Simulation.Requests.Serves]]. Consequently, every planner and side yield a source algorithm of the simulation ([[HeavyPath.Finger.History.Simulation.Requests.Algorithm]]) that, after any valid history and from a cursor at the root of the planner's current tree, emits exactly the planner's program, ends at the root of the planner's next tree, and has the same cost accounting.

@decl Combo.Worker.Replay.Requests.Results.source_lift Combo.Worker.Replay.Requests.Results.planner_source

The constructed source algorithm recomputes the planner state from the history it is given. This is allowed by the abstract model, in which an online algorithm sees its past requests.

## Two state types: pairs

The controller of [Chapter 35](combo-rounds.html) takes one [[Combo.Controller.Worker]], with one state type for both sides. Two independently built workers may have different state types. This happens in the finite families of [Chapter 33](combining.html), where combined workers are themselves paired again. Even when the state types agree, the pair is how two separately built workers become the two sides of one worker, as for the GreedyASS and Tango planners of [Chapter 38](combined-finger.html). The pair construction puts the two inputs, for the same initial tree, behind the sum type `α ⊕ β`.

**Definition (paired worker).** Given a left worker on `α`, a right worker on `β`, and a chosen side of each (`leftSide`, `rightSide`), the paired worker restarts side `false` as the left worker's chosen side and side `true` as the right worker's chosen side, tagging the state. A step on side `false` of a left-tagged state is a step of the left worker, and symmetrically on the right. A step with mismatched side and tag does nothing and never completes. The paired charges and pointer model take each side from the selected input.

@decl Combo.Worker.Pair.worker Combo.Worker.Pair.charges Combo.Worker.Pair.model

Mismatched states are never reached from a restart, and the paired model declares them not ready, so they never matter. The chosen sides let the pair take one side of each input. In [Chapter 38](combined-finger.html), for example, both inputs are replay workers used on their side `false`.

**Theorem (pairing is transparent).** An attempt, an access or a request sequence of the paired worker on a tagged state is exactly the tagged image of the same object for the selected input worker, with the same fuel, work and cost.

@decl Combo.Worker.Pair.Results.attempt_left Combo.Worker.Pair.Results.attempt_right Combo.Worker.Pair.Results.access_left Combo.Worker.Pair.Results.access_right Combo.Worker.Pair.Results.requests_left Combo.Worker.Pair.Results.requests_right

**Theorem (pairing preserves the hypotheses).** If both input models serve their requests, so does the paired model. If both inputs are well behaved with the same key count $n$, overhead $f$ and constants $C_0, C_1$, then the paired worker is well behaved for the paired charges with the same parameters.

@decl Combo.Worker.Pair.Results.correct Combo.Worker.Pair.Results.well_behaved

The well-behavedness transfer asks for a *common* $n$, $f$, $C_0$ and $C_1$. Inputs with different constants must first be brought to common ones; the pairing theorem does not do this. Each side keeps its own original charges, so a later bound in terms of $\min(\tau_0, \tau_1)$ compares the combined tree with each input's own bound.
