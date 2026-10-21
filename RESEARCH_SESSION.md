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
