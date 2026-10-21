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
