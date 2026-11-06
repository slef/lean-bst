# Alternating rounds

Combo-BST serves one request sequence with two BST algorithms $A_0$ and $A_1$, but it holds only one tree. Demaine, Iacono, Langerman and Özkan (2013, Section 4) arrange this in *rounds*. A round runs one algorithm, from the fixed initial tree $T$, for a fixed number of steps $C_3\,f(n)$. When the budget runs out in the middle of a request $x_i$, the tree is restored to $T$, the other algorithm becomes active, and the new round starts again at $x_i$. The analysis in Section 5 of the paper charges each round to the algorithm that is cheaper on the whole sequence. Every round of that algorithm except its last one used up its budget, so it served a piece of the sequence that costs it at least $C_3\,f(n)$. Well-behavedness turns this into a lower bound on its amortized charge for that piece.

This chapter formalizes that bookkeeping in three layers, all under `Algorithms/Combination`:

- `Controller`: the executable controller. It runs bounded **attempts** of one worker, switches workers when an attempt is exhausted, and follows a finite input prefix. The exact work accounting is proved here.
- `Rounds`: the **rounds** of a run, as intervals of request positions. They are computed from the controller's switch positions; the controller does not store them. The theorems count the rounds and add up charges over them.
- `Rounds.Certificates`: **closed-round certificates**. Every round except the last one is a complete record of an exhausted round started from the restart state, so rerunning its requests from that state costs more than the budget.

::: note Do you need this chapter?
The combination theorem of [Chapter 33](combining.html), and the combined finger theorem of [Chapter 38](combined-finger.html) built on it, are stated for an online policy that runs [[Combo.Controller.serve]] under the fresh-round hypothesis [[Combo.Controller.FreshBound]]. These two definitions are on the reading path of both results, together with what they use: the worker, attempts, controller states and results. [Section 35.2](#workers-and-bounded-attempts) and [Section 35.3](#serving-one-request) explain them. The rest of the chapter is proof machinery: the rounds, their certificates, and the counting behind Section 5 of the paper. Read it if you want to see where the factors $2k+1$ and $3f(n)$ of the final bound come from. [Section 35.6](#how-the-pieces-give-the-bound) sketches how the analysis of [Chapter 33](combining.html) assembles them.
:::

## Overview

Here is a run with budget $B = 5$. Worker $A_0$ completes $x_0$ and $x_1$ at cost $2$ each, then runs out of budget during $x_2$. The tree is restored, and $A_1$ starts from scratch at $x_2$.

```
positions           0     1     2     3     4     5     6
round 1 (A0)      [ x0    x1    x2 ]                         budget exhausted in x2
                                 restore
round 2 (A1)                  [ x2    x3    x4    x5 ]       budget exhausted in x5
                                                   restore
round 3 (A0)                                    [ x5    x6   still open
```

Three features of this picture recur throughout.

- **Rounds share their interrupted request.** Position $2$ belongs to round 1, whose attempt at $x_2$ failed, and to round 2, which served it. The library keeps the failed request in the closing round, so rounds of *different* workers overlap in one position. Rounds of the *same* worker never overlap: the paper's "no access gets executed by the same BST data structure in more than one round".
- **Every round restarts.** Round 3 runs $A_0$ from the initial tree on $x_5, x_6, \dots$. It does not resume where round 1 stopped. Each round is thus a standalone run of one algorithm on a contiguous piece of the sequence, which is why well-behaved bounds are stated for contiguous subsequences.
- **Only the last round is open.** Rounds 1 and 2 are *closed*: their budgets were spent exactly. Round 3 may still have budget left when the prefix ends.

**The budget is fixed.** The overhead $f(n)$ is known in advance, so every round of the paper has the same budget $C_3\,f(n)$, and the library does the same. The controller takes one `budget` for all rounds. The analysis of [Chapter 33](combining.html) instantiates it as [[Combo.Analysis.budget]] $= (C_1 + 1)\,F$, that is, $C_3 = C_1 + 1$, where $F \ge n$ is the overhead and $C_1$ is the additive constant of well-behavedness. No budget doubling takes place. The cost of restoring the tree is likewise a fixed number `restore`, charged at every switch. The paper pays $O(n)$ for `LoadState`. The analysis takes `restore` to be a multiple of $F$, and the physical restoration is in [Chapter 36](combo-online.html).

**What a worker is here.** At this level a worker is not yet a BST. It is a pure state machine whose steps each cost one unit of work and which reports when the current request has been served. [Chapter 34](combo-workers.html) defines what it means for such a worker to serve whole request sequences, and how two algorithms with different state types become one worker. [Chapter 36](combo-online.html) connects the steps to physical pointer operations on a shared tree.

## Workers and bounded attempts

A controller worker packages both algorithms over one common state type `σ`. The Boolean `side` selects the algorithm: `false` for $A_0$ and `true` for $A_1$.

@decl Combo.Controller.Worker

`restart side` is the state of algorithm `side` immediately after the tree has been restored to the initial tree $T$. It is the state in which every round starts. `step side s x` performs one charged unit of work of algorithm `side`, in state `s`, on the current request key `x`. It returns the new state and a completion bit, which is `true` when the step finishes request `x`. The step sees only the current state and request, never future requests, so any worker is online by construction. Several algorithms with different state types are combined into this common format in [Chapter 34](combo-workers.html).

An **attempt** runs one worker on the current request with a limited amount of fuel:

@decl Combo.Controller.Attempt Combo.Controller.attempt

`attempt worker side x fuel s` steps until the completion bit appears or the fuel runs out, whichever comes first. The result records the state reached, the fuel `left`, and whether the request was completed (`done`). With zero fuel no step is taken and the attempt fails at once. A failed attempt keeps its partial state, but the controller discards it, since it restores the tree instead.

The same process as an inductive trace, with an explicit work count:

@decl Combo.Controller.AttemptRun

The three constructors are an attempt with no fuel (`exhausted`, work $0$), one step that completes (`done`, work $1$), and one step that does not complete followed by the rest of the attempt (`more`). Each step costs exactly one unit of fuel. The function and the trace agree, and the work is the fuel consumed:

@decl Combo.Controller.Results.attempt_run Combo.Controller.Results.AttemptRun.failed Combo.Controller.Results.attempt_extra

`attempt_run` says that `attempt` produces an `AttemptRun` whose work is `fuel - left`. `AttemptRun.failed` says that a failed attempt has consumed all of its fuel: `left = 0` and `work = fuel`. This is the formal "each round but the last one runs for $C_3\,f(n)$ steps exactly". `attempt_extra` says that more fuel does not change a completed attempt: the same state is reached and the extra fuel is left over. A worker that finishes within some bound therefore finishes within any larger budget.

## Serving one request

The controller state records the active side, the active worker's state, and the budget left in the current round:

@decl Combo.Controller.State Combo.Controller.initial Combo.Controller.Result

`initial worker budget` starts with $A_0$ (side `false`) in its restart state and a full budget. A `Result` reports the new state, whether the request was served (`done`), whether a switch occurred (`switched`), and the work charged for this request.

@decl Combo.Controller.serve

`serve worker budget restore s x` is the controller's response to one request:

1. Attempt `x` with the active worker, from its current state, with the round's remaining fuel `s.left`. If it completes, stay in the same round, with the state and fuel the attempt left. The work is the fuel consumed.
2. Otherwise switch. Flip the side, start the other worker in its restart state, and attempt `x` with a *fresh, full* budget. The work is the fuel the first attempt consumed (all of `s.left`, by `AttemptRun.failed`), plus `restore`, plus the fuel the second attempt consumed.

So there is at most one switch per request. If the second attempt fails too, `serve` reports `done = false`. The request is never silently counted as served. Under the fresh-round hypothesis below this case does not happen. The relational version spells out the two cases with their traces:

@decl Combo.Controller.Service

In the `switch` case the restore cost `restore` sits between the two attempts. The two workers run one after the other, never in parallel. Three facts about one request:

@decl Combo.Controller.Results.serve_service Combo.Controller.Results.serve_left Combo.Controller.Results.serve_alternates

`serve_service` says that `serve` satisfies `Service`. `serve_left` says that the remaining fuel never exceeds the budget. `serve_alternates` says that the side changes exactly when `switched` is set.

**Fresh rounds always make progress.** The paper takes $C_3$ "suitably large" so that every round completes at least one access. The library states this as a hypothesis on the worker:

@decl Combo.Controller.FreshBound

`FreshBound worker n bound` says that, from its restart state, either algorithm completes any single valid request $x < n$ within `bound` units of work. This is the single-access part of well-behavedness, applied to the first request of a round. [[Combo.Analysis.Results.fresh]] derives it, with `bound` $= C_1 F$, from [[Combo.Analysis.WellBehaved]]. The budget $(C_1+1)F$ is strictly larger.

@decl Combo.Controller.Results.serve_done Combo.Controller.Results.fresh_completes

If `bound ≤ budget`, then `serve_done` says that every valid request is served, whatever the controller state. In the worst case, the retry runs from a fresh restart with a full budget, and `FreshBound` guarantees that it completes. `fresh_completes` says that a request served from a fresh round state (restart state, full budget) does not switch and costs at most `bound`.

## Running a prefix

`run` feeds a list of requests to `serve`, adds up the work, and stops with `none` at the first failure. `Execution` is the corresponding trace. It also counts the switches, a quantity used only in proofs: the controller does not store it.

@decl Combo.Controller.run Combo.Controller.Execution

The first theorem says that under `FreshBound` the controller never fails, with a crude per-request bound:

@decl Combo.Controller.Results.complete

From any state whose fuel is within the budget, and for any list of valid keys, `run` returns `some (final, cost)`, an `Execution` with the same final state and cost exists, the final fuel is still within the budget, and the cost is at most $(2\cdot\mathit{budget} + \mathit{restore})$ per request. The sharper bound, relative to the cheaper algorithm, needs the rounds below.

The central accounting identity is exact:

@decl Combo.Controller.Results.Execution.account

$$\mathit{cost} + t.\mathit{left} \;=\; s.\mathit{left} + \mathit{switches}\cdot(\mathit{budget} + \mathit{restore}).$$

The work of a run is the fuel available at the start, plus a full budget and one restore per switch, minus the fuel still unspent at the end. Since `AttemptRun.failed` makes every exhausted round spend all of its fuel, the identity holds with equality. The paper's Equation (1), $O(k\,f(n) + k\,n)$ for $2k+1$ rounds, follows from it by counting switches.

@decl Combo.Controller.Results.Execution.switches Combo.Controller.Results.Execution.left_le Combo.Controller.Results.run_append Combo.Controller.Results.Execution.split Combo.Controller.Results.Execution.window

These are the composition lemmas. There is at most one switch per request (`Execution.switches`), and the fuel stays within the budget along a whole run (`Execution.left_le`). Running `xs ++ ys` is running `xs` and then `ys` from the state reached (`run_append`), and an execution of `xs ++ ys` splits into two executions whose costs and switch counts add up (`Execution.split`). `Execution.window` splits a run at positions $lo \le hi$ into a prefix, a window and a suffix, with costs and switches adding up exactly. The window part starts from whatever state the prefix left. It is the controller's own state at position $lo$, not a fresh restart. The window theorems of [Chapter 33](combining.html) and [Chapter 36](combo-online.html) bound this actual middle segment of the actual run.

## Rounds as spans

A round is recorded as a span of request *positions*, not of key values: equal keys at different positions are different requests and are charged separately.

@decl Combo.Rounds.Span Combo.Rounds.Span.Contains

A `Span` has the side that ran it and the half-open interval `[start, stop)` of positions it covers.

The spans of a run are computed in two steps. `cuts` replays the controller and lists the positions at which a switch happened. `partition` turns a list of switch positions into spans of alternating sides. A span that ends at switch position $b$ stops at $b + 1$, so that it includes the interrupted request, and the next span starts at $b$. `spans` applies both to an input prefix whose first position is `offset`.

@decl Combo.Rounds.cuts Combo.Rounds.partition Combo.Rounds.spans

The convention that the closing round includes its interrupted request is conservative. If the round's fuel was already zero when the request arrived, the round did no work on it, but the request still belongs to the round. No extra worker step is inferred. The convention makes every closed round end with a failed attempt, which is the shape the certificates below need. In the overview example, `cuts` is `[2, 5]` and `spans` is `[⟨A₀, 0, 3⟩, ⟨A₁, 2, 6⟩, ⟨A₀, 5, 7⟩]`.

Two more definitions give the vocabulary of the counting argument. `Separated` says that, in a list of spans, an earlier span and a later span of the same side do not overlap. `count side` is the number of spans of that side.

@decl Combo.Rounds.Separated Combo.Rounds.count

The structural facts about rounds:

@decl Combo.Rounds.Results.cuts_ordered Combo.Rounds.Results.cuts_length Combo.Rounds.Results.spans_bounds Combo.Rounds.Results.spans_separated Combo.Rounds.Results.spans_length Combo.Rounds.Results.rounds_count

The switch positions are strictly increasing and lie inside the prefix (`cuts_ordered`). There is one per switch of the execution (`cuts_length`), so there are $\mathit{switches} + 1$ spans (`spans_length`). Each span lies inside the prefix and has `start ≤ stop` (`spans_bounds`). Same-side spans are separated (`spans_separated`). The proof uses that switch positions increase strictly, so the next same-side round begins at or after the next switch. `rounds_count` is the paper's "at most $2k+1$ rounds, $k$ of them performed by $A_{\min}$": for *either* side, the total number of rounds is at most $2\cdot\mathit{count} + 1$, since the sides alternate. The final round may be empty, for example on the empty prefix.

Charges are attached to positions of the original sequence by a weight function. A span's charge is the sum of the weights of its positions, and a side's charge is the sum over that side's spans:

@decl Combo.Rounds.Span.charge Combo.Rounds.charge

In the analysis the weights are the amortized charges $T_{X'}(A_\mu, T, X)$ of the paper, read at their positions in the *original* sequence $X$. Rounds are thus charged with the history of the whole sequence, not as if they were the start of a fresh sequence. The two quantitative consequences:

@decl Combo.Rounds.Results.work_by_rounds Combo.Rounds.Results.charge_le_interval

`work_by_rounds` bounds the work of an execution that starts within the budget by the number of rounds of either side: $\mathit{cost} \le (2\cdot\mathit{count} + 1)(\mathit{budget} + \mathit{restore})$. It combines `Execution.account`, `cuts_length` and `rounds_count`. `charge_le_interval` says that, for nonnegative weights, one side's rounds together carry at most the total weight of the prefix. This is the paper's "the $X'_j$ are disjoint subsets of $X''$". It follows from separation. Without the nonnegativity hypothesis it could fail, and the weights of the two sides cannot be added: their rounds overlap in the interrupted positions.

## Closed-round certificates

Counting rounds only bounds the work in terms of $k$. To bound $k$, the paper shows that each closed round of $A_{\min}$ is expensive: "$T(A_{\min}, T, X'_j) \ge C_3\,f(n)$ for all $j < k$". The certificates make "closed" precise. They use two relations from [Chapter 34](combo-workers.html): [[Combo.Worker.Requests]], a worker serving a list of requests to completion, and [[Combo.Worker.ClosedRound]], a round in which every request but the last completes and the last attempt is exhausted, starting from a given state with a given fuel.

@decl Combo.Rounds.Certificates.Record Combo.Rounds.Certificates.Active Combo.Rounds.Certificates.records

A `Record` is a span together with the request values it covers. It is a ghost: the controller never builds a list of records. `Active worker budget s earlier` is the invariant of the current round. The round began at `restart s.side`, its worker has served the requests `earlier` to completion, and the work spent on them plus the fuel left is exactly `budget`. `records` follows the controller and emits a record each time a round closes. The interrupted request ends the closing record, and the same request, now served by the retry, begins the `earlier` list of the next round.

@decl Combo.Rounds.Certificates.Results.initial_active Combo.Rounds.Certificates.Results.records_closed Combo.Rounds.Certificates.Results.records_spans Combo.Rounds.Certificates.Results.records_bounds Combo.Rounds.Certificates.Results.records_slice Combo.Rounds.Certificates.Results.records_tail_closed

The controller's initial state is active with nothing served (`initial_active`). If the run starts in an active state, every record is a `ClosedRound` of its side, from that side's restart state, with fuel exactly `budget` (`records_closed`). The records' spans are the round spans with the last, open, one removed (`records_spans`). They lie in the prefix (`records_bounds`), and their request lists are the corresponding slices of the input (`records_slice`). Without the `Active` hypothesis, every record except the first is still closed (`records_tail_closed`): any round that began at a switch began from a restart with a full budget.

Read in terms of spans, these give the three statements that the analysis uses:

@decl Combo.Rounds.Certificates.Results.closed_spans Combo.Rounds.Certificates.Results.span_lower_bound Combo.Rounds.Certificates.Results.interior_spans

For an execution from [[Combo.Controller.initial]], every span except the last is a closed round, from the restart state with the full budget, on its slice of the input (`closed_spans`). `span_lower_bound` is the paper's inequality, in strict form: if the worker of such a span serves all of its requests from its restart state at total work $w$, then $\mathit{budget} < w$. The proof is [[Combo.Worker.Results.ClosedRound.lower_bound]]. The exhausted last attempt shows that the full run needs more than the fuel the round had. For an execution from an *arbitrary* state, the first round may have begun before the prefix, with less than a full budget. `interior_spans` then certifies every span except the first and the last.

## How the pieces give the bound

The analysis in [Chapter 33](combining.html) ([[Combo.Analysis.Results.prefix_bound]] and its relatives) puts these facts together, with budget $B = (C_1 + 1)F$ and restore cost $rF$. Fix either side $\mu$, for example the one with the smaller total charge, and let $k$ be its number of rounds.

1. **Each closed round is charged at least $F$.** Let $X'_j$ be the requests of a closed round of $\mu$. By well-behavedness ([[Combo.Analysis.Results.segment_bound]]), running $\mu$ from the restart state on the standalone piece $X'_j$ costs at most $C_0\,T_{X'_j}(A_\mu, T, X) + C_1 F$. By `span_lower_bound` this cost exceeds $(C_1 + 1)F$. Hence $F \le C_0\,T_{X'_j}(A_\mu, T, X)$: this is [[Combo.Analysis.Results.closed_span_charge]].
2. **Closed rounds are few.** Summing over the at least $k - 1$ closed rounds of $\mu$, and using `charge_le_interval`, gives $(k-1)\,F \le C_0\,T(A_\mu)$, where $T(A_\mu)$ is the total charge of $\mu$ on the prefix ([[Combo.Analysis.Results.closed_count_bound]]).
3. **Work is proportional to rounds.** By `work_by_rounds`,

$$\mathit{cost} \;\le\; (2k+1)\,(C_1 + 1 + r)\,F \;\le\; (C_1 + 1 + r)\bigl(2\,C_0\,T(A_\mu) + 3F\bigr).$$

Since $\mu$ is arbitrary, the cost is bounded by the minimum over both sides. This is [[Combo.Analysis.Results.minimum_bound]]. For a window of an ongoing run, `Execution.window` isolates the middle segment and `interior_spans` certifies all of its rounds except the first and the last. Two uncertified rounds instead of one is why the window bounds of [Chapter 33](combining.html) have $5F$ where the prefix bounds have $3F$.

::: caveat What this layer does not provide
Everything here is about an abstract worker, whose steps cost one unit each. Restoring the tree is the number `restore`, charged once per switch. The fact that a worker step is a legal pointer operation on a real tree, and that restoring the initial tree costs $O(n)$, are separate obligations, discharged by the refinement and snapshot machinery of [Chapter 36](combo-online.html) and [Chapter 51](snapshots.html). The hypothesis [[Combo.Controller.FreshBound]] is an assumption on the worker, and it is derived from well-behavedness, never proved for arbitrary algorithms. The switch counts, spans and records exist only in proofs. The controller itself stores a side, a worker state and a fuel counter.
:::
