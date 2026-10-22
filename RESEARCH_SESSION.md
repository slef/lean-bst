# Six-hour state-elimination session

Authorized window: 2026-10-21 20:43:48 UTC through 2026-10-22 02:43:48 UTC
(04:43:48 Brussels). Heartbeat `bst-state-elimination-six-hour-research` resumes
this chat every 15 minutes. Stop research and pause it at the deadline.

## Targets and conventions

Cost = requests + rotations, as in StateElimination.lean. Deterministic online
algorithms, same initial tree, fixed key universe, no uncharged persistent
memory for the simulator beyond the tree shape.

1. Main relaxed target: for every stateful A, some tree-only B and constant C_A
   independent of n and sequence X satisfy cost_B <= C_A cost_A + f_A(n).
   Any additive function independent of sequence length is initially allowed;
   improve to O(n). Constants and f may depend on A.
2. Strong reading of user's 'not multiplicative': C_A = 1. Investigate separately.
   A negative result for this does NOT refute target 1.

## Existing checked results

StateElimination.lean on state-elimination branch: exact erasure under a
state-recovery invariant; n-factor move-to-root baseline; conditional implication
from a universally competitive tree-only algorithm. No general constant bound.
Draft PR https://github.com/slef/lean-bst/pull/1, branch originally c05755c.

## First checkpoint (20:49 UTC approximately)

Created reproducible experiment research/small_trees.py. Enumerates every tree
of n nodes, builds all rotation distances by BFS, and enumerates all tree-only
endpoint policies. For fixed endpoints, shortest rotations dominate extra
rotations, since only the endpoint is persistent. Product graph (B tree, offline
tree) has edge weight B rotation cost minus offline rotation cost. Positive
reachable cycle implies an unbounded additive gap on repeated witness inputs.
Bellman-Ford-style longest-path relaxation initializes all common initial trees.

Results: n=2 has one policy, no positive cycle. n=3 has 5 trees and 1024 endpoint
policies; ALL 1024 have a positive reachable cycle. This is experimental evidence
that no tree-only algorithm is 1-competitive with offline optimum on n=3.
It is NOT yet a counterexample to state elimination: offline != one fixed online A.
No Lean proof or certificate checker yet.

Promising next step: extract explicit cycles and check reachability from the
unique balanced tree (root key 1) rather than any common initial tree. On n=3,
request 1 forces this unique tree, erasing all tree memory. Use a prefix code
ending in 1 to tell a stateful A which of finitely many witness words to execute;
then A remembers the selected periodic schedule while every tree-only B starts
its tail in the same balanced tree. If each B has a witness from that tree,
one fixed stateful A can potentially beat EVERY tree-only B by an unbounded
additive amount. Need rigorous quantifiers, cycle extraction, transient costs,
legal A behavior on mismatched requests, and Lean certification. Larger actual
rotation counts only make B worse than its shortest-endpoint projection.

This direction addresses only C=1. Continue main constant-factor + f(n) target
even if it succeeds. Other routes: finite-state game/potential characterization,
reset diameter <=2n and amortization, finite-horizon compactness, state encoding.
Remember that arbitrary A may have infinite state; positional determinacy in a
game whose positions include A's hidden state does not give a tree-only policy.

## Reset idea audit

## Checkpoint 2026-10-21 21:30 UTC

BREAKTHROUGH for the stronger C=1 reading: a single fixed periodic input suffices.
See research/pure-additive-obstruction.md for the argument. On three keys define
U=021, V=02021, starting at balanced c. Every request 1 forces c. A stateful
modulo-eight clock serves UV with 11 rotations (19 including requests). Every
tree-only policy uses >=12 rotations (20 total). Repeating yields an unbounded
gap m at fixed n=3, defeating every f(3). This refutes C=1 only, NOT the main
constant-factor target. It needs no prefix coding, diagonalization, or offline
comparator: same clock algorithm A and same periodic word work against all B.

ThreeKeySeparation.lean compiles: kernel-checked 32-case policy inequality,
five-shape completeness for size=3, distance table lower bound on arbitrary
Rotations, and induced endpoint policy from arbitrary TreeAlgorithm. No sorry.
Added it as a default library target. Still to formalize: clock StatefulAlgorithm
and its legal traces; run-cost lower-bound bridge; repeated-word induction; full
negation of C=1 elimination. The prose proof is written; do not call the full
theorem Lean verified yet. Simplifying branch constraints immediately after each
case keeps the finite-policy proof fast (~0.6 sec file compile); avoid expanding
all 3125 branches before simplification.

Next priorities: finish the short complete Lean separation theorem, then return
to main C_A constant + arbitrary f(n) target and O(n) reset/finite-game approaches.

O(n) resets every n requests are affordable for constant-factor cost, but choosing
the best private state for each block may depend on the future. Simulation within
a block still carries state, and a tree-only rule has no external phase counter.
Repeated (tree, request) pairs must make consistent endpoint decisions.

## Working rules

No sorry, extra axioms, or unsupported claims. No subagents requested. Save useful
proofs and failures, run lake build --wfail for Lean changes. Preserve main and
work on current branch. Update this file every checkpoint for continuation.

## Checkpoint 2026-10-21 21:38 UTC (full C=1 theorem)

Finished the FULL Lean proof in ThreeKeySeparation.lean:
`no_purely_additive_simulation (b : TreeAlgorithm) (f : Nat → Nat)` supplies
valid t,xs with clockAlgorithm.totalCost t xs + f t.size < b.totalCost t xs.
The clockAlgorithm has state Fin 8 and a correct move-to-root fallback.
`tree_only_lower` proves 20*m <= cost B; `clock_cost` proves cost A =19*m.
No extra axioms or sorry; guard lists only propext, Classical.choice, Quot.sound.
Updated README and prose proof verification status. The earlier incomplete
status above is superseded. Full file compiles quickly (~0.7s).

Next: focus on constant C + arbitrary f(n). The C=1 counterexample does not
settle this and should not consume more time. Consider proving reset diameter
and a cycle/potential certificate for finite-state comparators. Do not conflate
memorylessness on product states (B tree, A tree, A state) with tree-only B.
Searches for memoryless BST simulation yielded no direct theorem; generic
memoryless queries mostly irrelevant RFID results. No claim of literature novelty.

## Additional checked reset ingredient (same checkpoint)

TreeReset.lean proves `reset_linear`: equal-size trees are connected by at most
2*n rotations, via a canonical right vine. `promote_left` drains a left subtree
in exactly its size rotations, `to_spine` gives a linear conversion, and rotation
traces reverse. `reset_then_access` prefixes a reset to a legal access. This
placement matters: resetting after an access to a tree whose root is different
would break the root-at-end requirement. Reset before the next access instead.

Next research route worth examining: weighted-automaton terminology. Finite n
makes tree shapes a finite weighted transition system with request-dependent
endpoint sets. Stateful online algorithms resolve choices using history;
tree-only algorithms select one transition per (shape, request). This resembles
history determinism versus determinization by pruning / regret determinization.
No transfer theorem established. For a fixed finite-state A and tree-only B,
absence of positive cycles in the reachable product graph for weights
cost_B-C*cost_A yields a finite additive bound (simple path length * max edge
weight). Its converse follows by repeating a reachable positive cycle. This
could support synthesis experiments, but existential B remains the hard part.

## Checkpoint 2026-10-21 21:49 UTC: potentials and automata route

Added SimulationPotential.lean (compiled): defines the relaxed conjecture with
arbitrary f(n), proves linear additive implies relaxed, and proves a sufficient
one-step potential criterion telescopes to cost_B <= C*cost_A + f(n).
Potential may inspect A's private state and both trees, but B's implementation
still sees only its tree/request. Initial potential bound determines f. No
potential for arbitrary A supplied: this is a proof tool, not the conjecture.

New reproducible research/competitive_policies.py enumerates all 1024 policies
for n=3 using exact rational positive-cycle tests against ALL offline executions.
Experimental best ratio =8/7, with 3 attaining policies. Example endpoint rows
(a,b,c,d,e), columns request (0,1,2):
[(a,c,d),(b,c,d),(a,c,e),(b,c,d),(a,c,e)].
For product states (A-tree,B-tree) having equal roots, in order
(a,a),(a,b),(b,a),(b,b),(c,c),(d,d),(d,e),(e,d),(e,e), longest-prefix excess
7*cost_B-8*cost_A from a common initial tree has bounds
[0,-8,-3,0,2,2,-8,-3,0]. Hence experimental uniform additive numerator bound2.
This is not yet Lean checked; finite certificate could be easy to check, but
avoid over-investing in n=3 at expense of uniform n question. C=1 obstruction
needs only small multiplicative slack for this finite universe.

Literature route: Boker & Lehtinen FSTTCS 2021, Theorem21 establishes that Sum
and Avg history-deterministic finite-word automata can be determinized by
pruning. Read primary author PDF:
https://faculty.runi.ac.il/udiboker/files/hdvsgfg.pdf (pp13-14).
Its hypothesis requires online resolution matching the automaton's OPTIMAL
value for EVERY word. Our arbitrary comparator A does not satisfy that, so it
cannot be applied directly. Putting A's state into a product automaton would
produce a positional strategy on the product, not a tree-only algorithm.
Aminof/Kupferman/Lampert 2010 connects online cost/memory questions to weighted
automata; verified abstract at
https://cris.huji.ac.il/en/publications/reasoning-about-online-algorithms-with-weighted-automata-13/
Full paper fetch at CiteSeer failed403. No general state-elimination theorem found.

Potential future directions: finite-state comparator synthesis via product
positive cycles; try block-reset/minimal-state selections with amortized credits;
try shape encodings with a constant number of extra logical bits, but preserve
same n and requested root. A naive shape-capacity count alone cannot prove
impossibility of COST domination (only exact-state simulation). The pure additive
counterexample is complete and should not distract from constant C target.

Further thought (not a theorem): bounded private state K may be an approachable
intermediate question, allowing a factor depending on K but not n. Exact encoding
of every (tree,state) into same-size trees is impossible by cardinality, but this
does not rule out cost simulation. Mapping to nearby shapes loses the original
virtual tree and arbitrary A can react discontinuously to that loss. Any coding
argument must explain this rather than merely reserve a few nodes for bits.

## Checkpoint 2026-10-21 ~22:10 UTC: potentially important reductions

Read research/constant-factor-reductions.md NEXT. New mathematical argument:
state elimination with arbitrary additive f may actually be equivalent to
existence of a single tree-only dynamically optimal algorithm. Build one online
probe U that learns every ultimately periodic input, then eventually serves its
period via a minimum-mean cycle. If memoryless B dominates U at factor C,
any positive B-vs-offline product cycle gives an ultimately periodic input
contradicting domination. Therefore B is offline-competitive with some additive
g(n). This is a written reduction argument, NOT Lean checked yet. Must audit U's
online construction, alignment after hypothesis changes, and all quantifiers.

A second positive reduction seems provable: any TREE-ONLY B already offline
C-competitive with arbitrary additive g(n) can be changed to another tree-only
B' with the SAME C and additive O(n). Define least credit V(s,t) for cost_B(s,X)
vs C*offline(t,X). V is finite, nonnegative, and Lipschitz in t with range at
most C*R, R=2n. A maximal-excess finite path ends at a pair (s*,t*) with V=0.
Use a tree-only threshold on V to reset to s*. Truncate the potential for high
states; every reset is paid by the dropped credit. Full prose proof is in the
new note. This DOES NOT supply B or settle dynamic optimality.

New CHECKED modules:
- CostComposition.lean: execution append, size/validity, prepend rotations to
  nonempty execution, tree-only cost append/cons, competitive_change_start.
- CompetitiveCredit.lean: least Nat credit, attainment, zero_credit_pair,
  Lipschitz continuity, and the one-step credit inequality. All compile, axiom
  guard standard only. No sorry/extra axioms. Nat.find is unavailable in Std;
  proved private least_nat via strongRecOn. by_contra tactic unavailable;
  use Classical.byContradiction. Product projections need explicit destructuring
  in treeOnly_cost_cons to avoid omega treating equivalent expressions separately.

NEXT IMPLEMENTATION: finish reset-potential normalization to a full theorem.
Avoid the minimum v(s)=min_t V(s,t) if convenient: choose the zero pair's anchor
u_n and threshold H=R+2*C*R on V(s,u_n). For high states reset s to seed s*_n,
then perform original B's action for the current request. Define
P(s,t)=V(s,t) in low states and R+V(s*_n,t) in high states.
Reverse Lipschitz + threshold gives P<=V. Forward Lipschitz bounds P everywhere
by R+3*C*R=(2+6C)n. The old one-step credit inequality then proves B' has same
C and this linear additive bound. Use reset_linear with Classical.choose for
reset count; B' has Unit state. Select zero pair for each n using canonical
spine n nil (prove its size=n). Can package V/seed/anchor/specs in a structure
to keep definitions manageable, then instantiate from CompetitiveCredit.

The earlier minimum-based argument gives (2+4C)n; the simpler anchor threshold
loses only a harmless constant. Formalize the easier (2+6C)n first.

## Checkpoint 2026-10-21 ~22:25 UTC: normalization fully verified

AdditiveNormalization.lean now proves normalize_additive: given tree-only B
with coefficient C against ALL offline executions and any additive f(n),
construct tree-only B' with the SAME C and additive (2+6C)*n. Threshold uses
only current shape; reset occurs before serving current access. Transformation
is noncomputable, as allowed by present existence model. No state elimination
for arbitrary comparator follows yet. Axiom guard standard only, no sorry.

Updated README and reduction note to distinguish this checked theorem from the
unformalized periodic-probe argument. Next focus: rigorously formalize/audit
periodic probe -> offline competitiveness. A finite weighted-graph cycle lemma
is a useful first step. Beware returning an algorithm on tree/state product
rather than tree alone. Universal probe needs online consistency learning and
phase alignment but has unrestricted private state. A reduction to tree-only
dynamic optimality would explain difficulty, not solve the main conjecture.

## Checkpoint 2026-10-21 ~22:40 UTC: periodic reduction ingredients

Added PeriodicComparison.lean: repeatWord, repeated execution/cost/endpoint
lemmas, a precise PeriodicProbe property, and probe_forbids_positive_loop.
This last theorem says any tree-only B dominating such a probe at coefficient C
has no positive B-versus-offline product loop reachable from a common initial
tree. The two endpoint trees need not coincide. Domination holds on valid
inputs only; validity is derived from the repeated offline execution. No
finite-state assumption about A is required. Existence of a PeriodicProbe is
NOT proved or assumed as an axiom; it is an explicit hypothesis.

Added PeriodicLearning.lean: bounded monotone natural-valued sequences stabilize;
least consistent hypothesis indices stabilize when one permanently correct
candidate exists; a stabilized consistent hypothesis matches every prefix.
These establish the learning argument abstractly, not the BST scheduling cost.

NEXT: finite weighted path cycle-erasure bound (no positive reachable loops =>
bounded excess), and construct a single stateful periodic probe with the exact
PeriodicProbe property. The prose construction still looks sound: enumerate
ultimately periodic words, select least consistent one, and on stabilization
use a minimum-mean phase/tree cycle. Need formally justify finite tree set,
minimum mean cycle, and bounded startup/remainder cost. The property allows K
to depend on the offline periodic schedule and prefix but never repetitions.
Do not mistake these ingredients for a completed equivalence or state elimination.

## Checkpoint 2026-10-21 ~22:55 UTC: finite path bound verified

FiniteWeightedPaths.lean proves generic integer-weighted cycle erasure:
Trace edge s t xs can be replaced by a trace with distinct vertices and weight
at least as large, provided every closed trace has nonpositive weight.
finite_path_bound bounds weight by states.length*M when start is in a finite
list, every edge target is in it, and each edge weight <= natural M. It does
NOT require the entire vertex type to be finite. This permits using Tree×Tree
and restricting graph edges to reachable pairs. All proven with Std only.

FiniteTrees.lean gives treeCover n, a redundant finite list covering every tree
of size <=n, plus stepBound b n bounding every legal one-step total cost of b
on size n. The enumeration is deliberately huge; only existence is needed.

NEXT concrete bridge: define reachable pair (s,t) from common T by existence
of offline Execution T pre t j and b's endpoint on pre equal s. Define edges
on Tree×Tree with this reachable-source condition, an offline Access t u x k,
and B's step endpoint, weighted by (1+Bstepcost)-C*(1+k) in Int.
Prove trace => shared request word and offline execution, cost difference equal
weight; then noPositive for nonempty loops follows from
probe_forbids_positive_loop applied to reachable-source witness. Empty loops
have weight0. Edge targets have size n via reachability/correctness; use
(treeCover n)×(treeCover n) as states list. The finite_path_bound gives g(n)
roughly treeCover.length^2*stepBound. Combine normalize_additive afterward.
This would complete the reduction conditional on an existing PeriodicProbe.
Actual construction of that probe remains unformalized.

## Checkpoint 2026-10-21 ~23:12 UTC: conditional reduction COMPLETE

ProbeReduction.lean now connects all graph ingredients. Reachable product
vertices pair B's endpoint with an offline endpoint from common initial T.
Edge weights are total B step cost minus C times offline step cost. Both
trace/execution directions are checked with exact integer weight identities.
Periodic probe domination excludes positive loops, finite_path_bound gives
additive graphAllowance(n), then normalize_additive makes it (2+6C)n.

Main checked theorems:
- probe_domination_offline: if B dominates a PeriodicProbe at C+f(n), B itself
  is offline-competitive at C+graphAllowance(n).
- probe_domination_linear: some B' is offline-competitive at C+(2+6C)n.
- elimination_iff_universal_given_probe: assuming existence of a PeriodicProbe,
  StateEliminationWithAdditive iff ∃tree-only universally competitive B.
- arbitrary_iff_linear_given_probe: under same assumption, arbitrary additive
  state elimination iff linear additive state elimination.
Axiom guards standard only. These are CONDITIONAL theorems. Missing obligation
is exactly ∃σ a, PeriodicProbe a. No claim the original conjecture is settled.

Next: construct the probe. Existing PeriodicLearning lemmas supply stabilization
but need concrete enumeration of ultimately periodic inputs, then a legal
online policy after hypothesis stabilization with asymptotically optimal mean
cost. A route that may simplify minimum-mean theory: for each predicted word
choose a least-cost-per-period cycle among finite simple cycles in phase/tree
graph; cycle-erasure implies this mean <= every periodic serving witness.
Finite graphs already available, but minimum-ratio/simple-cycle construction
not formalized. Alternatively choose increasing finite horizons and resets:
sublinear overhead might suffice for positive-loop contradiction, but the
CURRENT PeriodicProbe property demands a bounded additive K, not o(m).
Can weaken property to epsilon-asymptotic if it meaningfully simplifies proof;
then adapt probe_forbids_positive_loop using slope gap. Avoid silently changing
existing stronger property or conflating unproved existence with an axiom.

## Checkpoint 2026-10-21 ~23:27 UTC: simpler probe route via compactness

New plan avoids minimum-mean-cycle machinery altogether. For ANY known infinite
valid request word, choose a clairvoyant infinite serving plan whose every
prefix is within 2n of optimal from its own initial tree (4n from any equal-size
initial tree). Finite-horizon optimal plans have this prefix property: replace
prefix by a better plan, reset into old suffix, contradict optimality. Every
individual action in an optimal finite plan costs <=2n as well (replace it
while preserving endpoint). Hence there is a finitely branching tree of good
finite plans, with arbitrarily large depth. König supplies an infinite plan.

Checked new modules:
- FiniteBranching.lean: finite_cover downward-closed pigeonhole, Extension,
  unbounded_child, and infinite_branch (choice-based König lemma).
- OptimalPrefixes.lean: existence of optimal finite execution; optimal_prefix_bound
  (+2n against same start), optimal_prefix_other_start (+4n), and
  optimal_access_bound (every action of finite optimum costs <=2n).
No extra axioms. These do not yet construct the infinite BST plan.

Probe implementation can be simpler than maintaining a new plan at each switch:
for each enumerated infinite periodic candidate q, preselect a good clairvoyant
plan from canonical tree, indexed by ABSOLUTE time. Learner stores last q/time.
When q changes, reset to that plan's tree at current time, then perform its action;
if q stays the same, current tree already equals the next plan tree. After
hypothesis stabilizes, no more resets. Following a suffix of the plan costs at
most its entire prefix cost (costs nonnegative), plus finite earlier actual cost.
Its prefix guarantee compares to the given repeated offline witness with +4n.
Thus K absorbs finite mistakes, offline prefix cost, resets and 4n; strong
PeriodicProbe property follows, with no asymptotic approximation needed.

NEXT IMPLEMENTATION: finite good-plan prefix tree. Enumerate children by
(treeCover n × List.range(2*n+1)); filter certified Access and good-prefix
inequalities. Nodes carry a finite trajectory, not just current shape, so good
prefix bookkeeping is available. Optimal finite executions give arbitrary
depth. Infinite_branch then yields the infinite actions. Need trace splitting
at arbitrary prefix to apply optimal_prefix_bound to every intermediate node.
Could define a bounded-plan inductive relation (list of endpoints/costs) and
prove optimal Execution admits such a trace using optimal_access_bound.
After infinite-plan existence, concrete enumeration of eventuallyperiodic words
and learner implementation remain. Main original conjecture still open.

## Checkpoint 2026-10-21 ~23:42 UTC: infinite clairvoyant plan COMPLETE

InfinitePlan.lean now defines InfinitePlanning.segment and constructs
known_future_plan word initial valid : Plan word initial. It has tree(i),
rotations(i), cost(i), legal accesses, cumulative-cost equation, initial tree,
action bound 2n, and simultaneous prefix_bound: cost(i)<=j+4n against ANY
Execution from an equal-size initial tree on segment word 0 i. This is a
clairvoyant plan depending on the ENTIRE word, explicitly not online.

Construction avoided building an explicit prefix tree. FutureOptimal asserts
that the already executed prefix extends to finite optimal plans at arbitrarily
distant horizons (not necessarily every horizon). A finite_cover argument on
(treeCover n × counts0..2n) selects one next action retaining this property.
Partial stores prefix Execution and FutureOptimal. Recursively extend via
choice. Prefix bound follows from optimal_prefix_other_start applied to any
future optimal completion. Axiom guard standard only; compiled successfully.
The generic infinite_branch lemma is not needed by this tighter construction,
but finite_cover from FiniteBranching is used.

NEXT: concrete periodic candidate learner and its online BST wrapper. No need
for min-mean cycles anymore. Each candidate infinite word gets a fixed plan
from canonical tree, indexed by absolute time. On candidate changes reset to
that plan's current tree then serve; after stabilization continue with no reset.
Need candidate enumeration and stabilization. Std seems to lack Nat.pair/unpair
and Encodable. Avoid spending time coding integers if possible: use a family
of finite covers of candidate (prefix,period) pairs, each cover listing all
words of length<=bound over range n. Choose least bound admitting a consistent
candidate, then least index in that finite cover. Least bound stabilizes by
bounded_monotone_stabilizes; thereafter the least index stabilizes in a fixed
finite list. All finite input prefixes have an eventually-constant extension.
Empty periods can interpret as constant0 when n>0; n=0 has no valid nonempty
requests and can use the fallback. Alternatively implement explicit countable
enumeration if simpler. The plan theorem is complete; PeriodicProbe existence
still is not. Original state-elimination conjecture remains unresolved.

## Checkpoint 2026-10-21 ~23:58 UTC: concrete learner COMPLETE

FiniteCoverLearning.lean defines Pick from a countable family of finite lists:
least feasible bucket then least compatible index. pick_exists/pick construct
it by classical least-natural choice. stabilizes proves eventual constant
candidate along shrinking compatibility predicates whenever a permanently
correct candidate belongs to some bucket. First bucket stabilizes, then index.

PeriodicCandidates.lean concretizes this for Candidate=List Nat × List Nat.
forecast p i reads prefix then period by modulo; empty period means constant0.
words n b covers all words of length<=b over range n; covers pairs those words.
Covers valid/complete checked. Compatible history p means agreement at every
index of observed history; every valid history has extension (history,[]).
selected is a history-only Pick with valid candidate. segment_length/atRank/
compatible_segment and segment_values connect to InfinitePlanning.segment.
selected_eventually_correct proves: on any infinite valid word equal to a valid
candidate forecast, eventually selection is one fixed valid p whose forecast
matches the WHOLE infinite word. No oracle used in selection; it only inspects
finite history. forecast_valid needs n>0 because of empty-period default0.
All 41 build jobs pass, guards standard axioms only.

NEXT: actual online BST wrapper and cost bound. Suggested state = history only;
selection on history++[x] includes current request. Each candidate p gets fixed
known_future_plan (forecast p) (spine n nil), using covers_valid/forecast_valid.
At step time=history.length, if currenttree equals plan.tree time, use its
certified action; otherwise reset currenttree to plan.tree time then act.
No need to store last candidate: equality test handles synchronization directly.
After selection stabilizes, endpoint of each action is plan.tree(time+1), so
subsequent accesses require no reset. Empty/invalid-history cases can fallback
to moveToRoot; legal runs initialized with [] have valid histories by induction.
Require hn:0<currenttree.size (follows from legal x) and historyvalid to select;
fallback on arbitrary unreachable states maintains StatefulAlgorithm.correct.

Plan action roots match forecast p time, which equals current x via selected
consistency on history++[x]. Need list append indexing lemma. For repeated
input proof, connect history runs to segment word 0 time; after cutoff+1,
rotations equal plan rotations. Telescoping cost<=finite actual prefix+plan
prefixcost+length; plan.prefix_bound against repeated offline execution yields
PeriodicProbe. Also still need forecast(pre,period) prefix equals
pre++repeatWord period m for nonempty period; emptyperiod repeatedword is
constant pre and can handle separately. n=0 all legal inputs empty.
Main conjecture unresolved; these complete the learner but not its BST wrapper.

## Checkpoint 2026-10-22 ~00:12 UTC: legal online wrapper COMPLETE

ForecastAlgorithm.lean defines algorithm : StatefulAlgorithm (List Nat).
Persistent state is observed history. On each request it selects a candidate
from history++[x], gets its fixed known_future_plan from spine n nil, repairs
current tree to plan.tree(history.length) if needed, then serves current x.
Ready checks positive size and validity of history++[x]; unreachable bad-history
states use legal moveToRoot fallback. StatefulAlgorithm.correct fully checked.
No future input queried by selection: noncomputable plan depends only on the
selected periodic forecast, not actual unknown future.

Checked repair_spec (<=2n; repair_same=0), plan_size, candidatePlan, selected_valid,
selected_current, planned_correct, run_history, step_candidate_endpoint and
synchronized_step. Last two prove synchronization after one action and zero
repair cost if tree already matches selected plan at current time. Proofs use
proof irrelevance to align candidatePlan validity witnesses.

NEXT: ForecastTracking.lean. Let runAt i := algorithm.runFrom [] initial
(segment word 0 i). Use segment_add word 0 i 1, runFrom_append and run_history
to get successor tree/cost equations. Histories are segment word 0 i; sizes
remain n by algorithm.execution. Validity gives Ready at each i. Selection on
history++[word i] is selection on segment word 0(i+1); use
selected_eventually_correct to get fixed p after N. Then all steps i>=N end
at plan.tree(i+1); steps i>=N+1 pay exactly plan.rotations i. Summing/telescoping
bounds all prefix costs by plan prefix cost plus a finite constant.
For short prefixes, either use monotonicity of actual cumulative costs up to
N+1, or prove general one-step <=4n rotations and absorb (N+1)*4n. Do not
claim PeriodicProbe until this cost bridge AND forecast/pre/repeatedword list
identity are checked. Empty period / n=0 handle separately.

## Checkpoint 2026-10-22 ~00:36 UTC: UNCONDITIONAL EQUIVALENCE COMPLETE

ForecastTracking.lean completes actual-run history/size/successor identities,
eventual endpoint alignment, zero-reset steps after cutoff, cost monotonicity,
and bounded_transient telescoping. eventual_offline_bound: for a valid infinite
word represented by any valid periodic candidate, our online algorithm has
cost <= offline prefix cost+K for ALL prefixes and ALL offline executions,
with K fixed for the infinite input and initial tree.

PeriodicProbe.lean proves forecast segment = pre++repeatWord period m, handles
empty periods, and concludes algorithm_is_probe : PeriodicProbe algorithm.
Therefore state_elimination_iff_universal and arbitrary_iff_linear are now
UNCONDITIONAL Lean theorems, not merely conditional on probe existence.

Exact result: in THIS rotation model, state elimination with constant C_A and
arbitrary f_A(n) iff linear-additive state elimination iff existence of a
single tree-only offline-competitive algorithm. This proves equivalence, NOT
truth of any existence statement. C=1 is already disproved. Planning is uncharged;
algorithms may be noncomputable, as permitted by existing definitions. No claim
of novelty or transfer to the standard pointer model; correspondence remains
an independent unproved obligation. README and reduction note now make the
completed status clear and retain earlier failed/alternative routes as history.

NEXT research during remaining session: audit quantifiers and model assumptions
of the equivalence; explore whether a weaker per-A claim restricted to computable
algorithms changes the probe argument (do not change original definitions).
Try productive constructive subcases or identify an actual obstruction for
constant C, avoiding further scaffolding that merely restates dynamic optimality.
One worthwhile question: the probe is classically selected; can a computable
periodic oracle via finite phase/tree minimum-mean cycles recover the same
mathematical reduction? Could document without formalizing if little time.
Also assess bounded-state comparators, reset-based positive subcases, and whether
user's repeated-tree idea gives anything beyond the checked additive normalization.
Continue until 02:43:48 UTC; do not mark overall conjecture proved.

## Checkpoint 2026-10-22 ~00:50 UTC: audit and computability route

Audited equivalence quantifiers, reachable graph, costs and online dependence;
no gap found. Added research/model-audit.md. Read primary PDFs Iacono 2013
(arxiv1306.0207) and Combining BSTs (arxiv1304.7604). Epoch/reset combiner results
retain extra state/annotations, so do not directly solve our tree-only request.
No novelty or standard-pointer-model transfer claimed.

A computable alternative periodic probe appears available via finite phase/tree
minimum-average cycles. research/periodic_cycle.py implements exact rational
cycle search with Bellman-Ford potentials and a tight cycle certificate.
Saved four reproducible outputs in periodic_cycle_results.jsonl. For n3 UV,
minimum mean=19/8 (matches clock); n4 periods 0312 and 0123 give3 and5/2.
This is an experiment/mathematical route, not a Lean computability theorem.
The credit-based normalization is still noncomputable in its current form.

Strengthened checked three-key result: no_ratio_below_20_19 proves failure of
EVERY rational coefficient strictly below20/19, with arbitrary additive f(n),
using scaled natural inequalities. This sharpens the already-described lower
bound but does not rule out larger constants. Full47-job build passes.

NEXT: seek genuinely new constructive subcases or a uniform-n obstruction.
Could synthesize small n4 memoryless policies via finite games/constraint solving,
but avoid assuming a finite-n ratio is evidence for a uniform constant. Another
useful end product is a concise TeXlish research report with diagrams explaining
the three-key obstruction, normalization and equivalence. User originally
requested TeXlish; existing docs/main.texlish describes core only. Research
session remains active until02:43:48 UTC; main existence question unresolved.

## Checkpoint 2026-10-22 ~01:05 UTC: finite synthesis and bounded probe idea

Installed z3-solver5.3.1.0 in /private/tmp/lean-bst-z3 (isolated temporary target).
research/synthesize_policy.py encodes shortest-endpoint policy variables,
reachable equal-root product pairs, and integer potentials for rational p/q.
Diagonal pairs reachable; closure under all offline endpoints. Potential values
not forced zero on diagonal. SAT policies independently checked with existing
exact Python cycle algorithm. Unknown timeouts explicitly preserved.

research/synthesize_optimal.py searches all possible simple-cycle ratios bounded
by S*(diameter+1). n4 experimental EXACT optimum6/5, with independently checked
5*B<=6*offline+2 certificate. n3 reproduces known8/7. n5 both5/4 and3/2 timed
out; no conclusion. Files/results/repro details in finite-policy-synthesis.md.
No new Lean theorem this checkpoint, no assertion of a uniform bound.

New unformalized observation added to model-audit.md: only ultimatelyperiodic
witnesses with preperiod/period <=S=Catalan(n)^2 are needed to expose positive
cycles at fixedn. Thus a universal testing probe can likely use FINITE memory
for eachn (huge function of n): finitecandidate elimination plus phasecounter
modulo lcm of all candidate/servingcycle periods. This would strengthen reduction
to locally finite-state comparators, but not uniformly bounded Fin K comparators.
Existing formal probe still uses unboundedhistory. Next useful research: prove
bounded cycle witnesses / make finite-memory observation precise, or prepare
clear TeXlish report of fully proved results. Do not spend long on n5 solver
without a new encoding or new bound; prior timeouts are not mathematical evidence.
Remaining session until02:43:48 UTC, original constant-factor existence open.

## Checkpoint 2026-10-22 ~01:18 UTC: bounded lasso theorem checked

BoundedCycles.lean extends generic finite-graph infrastructure:
- erase_with_simple_loops only assumes simple loops nonpositive;
- positive_simple_cycle extracts a positive simple loop from any positiveclosed trace;
- bounded_positive_cycle gives length<=states.length;
- simple_reaching_path erases loops ignoring weights;
- bounded_reaching_path gives length<states.length;
- bounded_lasso combines both in a graph whose edge sources are reachable from
  a fixed start. Prefix length<S, positiveperiod length<=S. Axiom guard standard.

This proves the finite-graph foundation of the finite-memory-per-size observation.
It does not yet implement the finite-memory probe or instantiate the bounded
lasso theorem on the BST product graph. Existing full equivalence unchanged.
To instantiate: Edge b C T already has Reach source witness; execution_trace
turns that prefix into a graph trace, after endpoint equalities. sources bound
follows reach_sizes+mem_pairCover. Then bounded_lasso yields producttrace lengths.
trace_execution needs an additional length-equality lemma to turn these bounds
into request-word length bounds (existing theorem only returns execution,
endpoint, and costweight). Could extend via a new theorem without breaking old.

No new resolution of uniform constantC; periodic witness bound can support a
finite-memory probe but would still only establish the same hard equivalence.
Consider prioritizing a concise TeXlish report for user's review, rather than
spending all remaining time strengthening reductions. Deadline02:43:48UTC.


## Checkpoint 2026-10-22 ~01:32 UTC: bounded BST witnesses checked

Added BoundedBSTWitness.lean, default target, successful lake build --wfail
(51 jobs). trace_execution_length makes one graph edge exactly one request.
edge_reachable connects Edge's stored reachability witness to graph traces.
bounded_request_witness instantiates bounded_lasso: a positive product loop
has a prefix shorter than pairCover(n).length and a positive period no longer
than that number, with actual offline executions and B endpoints.

bounded_tests_suffice proves those bounded paired loops alone suffice for
OfflineCompetitiveWith b C (graphAllowance b). BoundedPeriodicProbe restricts
the probe requirement to the finite family of short prefix/period words;
bounded_probe_domination proves domination of such a probe already implies
offline competitiveness. No new axioms or sorry.

research/model-audit.md now spells out a per-size finite-state learner using
candidate elimination, capped/modular time, and minimum-mean serving cycles.
The bounded-probe interface and reduction are checked; the finite-memory
construction remains an on-paper argument, not a Lean theorem. It does not
settle uniformly bounded Fin K private memory or original state elimination.

Remaining time until02:43:48UTC. Useful next priority: concise TeXlish research
report for user, with the separation/equivalence/normalization and model caveats;
avoid spending remaining session exclusively strengthening reduction scaffolding.
Unpushed prior commits0920885,abf3a1d,80cecb6 plus this checkpoint; push at next
meaningful documentation milestone. Current main conjecture still unresolved.


## Checkpoint 2026-10-22 ~01:46 UTC: four-page TeXlish research note

Created docs/state-elimination.texlish in the existing prose-and-Lean style.
Four pages cover explicit private state; the three-key pentagon and19vs20
counterexample; full equivalence; reset normalization; bounded probes and gaps.
Code snippets are automatically extracted from checked source by the existing
extract_snippets.py. Documentation Makefile builds both PDFs; Actions uploads
both and watches source dependencies. Rendered all4 pages and corrected page
break and overlapping tree-node issues; no overfull boxes. Final local PDF:
../outputs/lean-bst-state-elimination.pdf. Original core document unchanged.

No mathematical result added in this checkpoint. Prior build51jobs remains
valid; documentation build succeeds. Research still active until02:43:48UTC.
Main remaining task: seek genuinely new proof leverage or limitations for
constant-size private state; do not confuse finite-memory-per-n probe argument
with fixed Fin K. Final deadline validation and automation pause still pending.
