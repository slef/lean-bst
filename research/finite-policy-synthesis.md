# Finite-n policy synthesis (experimental)

For fixed n, a tree-only endpoint policy chooses a new root-compatible tree for
each (tree, request). Shortest rotation paths to those endpoints weakly improve
its cost without changing any subsequent endpoint decisions. Thus it suffices
to synthesize endpoint choices.

The solver represents all pairs (offline tree, policy tree) having the same
root. Every diagonal pair is initially reachable. For each chosen policy
endpoint, every legal offline endpoint produces a product edge. Reachability
variables are required to contain the diagonal and to be closed under these
edges. For a proposed rational coefficient p/q, integer potentials satisfy

  V(next) >= V(current) + q*policy_step_cost - p*offline_step_cost

on all reachable edges. Feasibility excludes positive reachable cycles. The
solver may mark extra pairs reachable, but this does not compromise soundness.
Conversely it can choose precisely the actual reachable set, so the encoding
should not exclude policies merely because an unreachable positive cycle exists.
There is no requirement that diagonal potentials be zero: positive transient
excess returning to a common tree is permitted when it does not repeat profitably.

A feasible policy is checked again by `competitive_policies.potential`, using
exact integer longest-path relaxations, independently of the solver's supplied
potential. This is a software cross-check, not a Lean certificate. Infeasibility
results rely on Z3 and are not formal lower-bound proofs.

For the exact finite-n search, let S be the number of equal-root product states
and D the rotation diameter. A simple cycle has at most S edges, and both total
costs are positive integers at most S(D+1). Hence every policy's maximum cycle
ratio belongs to the finite set of rational numbers whose numerator and
denominator are at most S(D+1). Binary search over this set finds an experimental
optimum, provided no solver call returns unknown.

## Results

- n=3: coefficient1 infeasible; coefficient8/7 feasible. This agrees with the
  previous exhaustive enumeration of all1024 policies.
- n=4: the full rational search gives experimental optimum **6/5**. There are
  58 product states and the numerator/denominator cap is290. The returned policy
  satisfies `5*cost_B <= 6*offline_cost+2` on all finite inputs according to the
  independent exact cycle check. Results are in `optimal_policy_n4.jsonl`.
- n=5: both5/4 and3/2 returned **unknown (timeout)**. Neither is evidence of
  feasibility or impossibility. No conclusion about n=5 is recorded.

These finite values give no uniform-in-n bound, and do not settle state
elimination. They also concern offline competitiveness; one must use the
proved periodic-probe reduction to connect a uniform result to state elimination.

## Reproduction

Use Python3 with `z3-solver==5.3.1.0`:

```sh
python3 research/synthesize_policy.py 3 1 8/7
python3 research/synthesize_optimal.py 4 5/4 --timeout-ms 10000
python3 research/synthesize_policy.py 5 5/4 3/2 --timeout-ms 10000
```

Runtime and model selection can vary. The scripts never convert `unknown` to
`unsat`. The checked-in output records the observed results and exact policies.
