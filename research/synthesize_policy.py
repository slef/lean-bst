"""Exact finite-n policy synthesis via integer potential constraints.

Requires z3-solver. The SAT certificate is independently verified by the pure
Python reachable-cycle checker. UNSAT is solver evidence, not a Lean theorem.
All equal-root product states are represented; reachability variables start at
every common initial tree and are closed under every offline endpoint choice.
"""
import argparse
import json
from fractions import Fraction
from time import monotonic
from z3 import And, Bool, Implies, Int, Or, Solver, sat
from small_trees import model
from competitive_policies import potential


def synthesize(n, ratio, timeout_ms=60000):
    ts, dist, allowed = model(n)
    root = {t: x for x, targets in enumerate(allowed) for t in targets}
    states = [(a,b) for a in range(len(ts)) for b in range(len(ts)) if root[a] == root[b]]
    reach = {s: Bool(f'r_{s[0]}_{s[1]}') for s in states}
    value = {s: Int(f'v_{s[0]}_{s[1]}') for s in states}
    choice = {(b,x): Int(f'p_{b}_{x}') for b in range(len(ts)) for x in range(n)}
    solver = Solver()
    solver.set(timeout=timeout_ms)
    for (b,x), var in choice.items():
        solver.add(Or([var == v for v in allowed[x]]))
    for a,b in states:
        if a == b:
            solver.add(reach[a,b])
        for x, targets in enumerate(allowed):
            for v in targets:
                constraints = []
                for u in targets:
                    delta = ratio.denominator*(1+dist[b][v])-ratio.numerator*(1+dist[a][u])
                    constraints += [reach[u,v], value[u,v] >= value[a,b]+delta]
                solver.add(Implies(And(reach[a,b], choice[b,x] == v), And(constraints)))
    start = monotonic()
    status = solver.check()
    result = {'n': n, 'ratio': str(ratio), 'status': str(status),
              'seconds': round(monotonic()-start, 3), 'states': len(states)}
    if status == sat:
        sol = solver.model()
        policy = [[sol.eval(choice[b,x]).as_long() for x in range(n)] for b in range(len(ts))]
        certificate = potential(policy, dist, allowed, ratio)
        assert certificate is not None, 'independent cycle verification failed'
        result.update(policy=policy, additive_numerator=certificate[2],
                      reachable_states=sum(v is not None for v in certificate[1]),
                      certificate_values=certificate[1])
    elif str(status) == 'unknown':
        result['reason'] = solver.reason_unknown()
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('n', type=int)
    p.add_argument('ratios', nargs='+')
    p.add_argument('--timeout-ms', type=int, default=60000)
    args = p.parse_args()
    for ratio in args.ratios:
        print(json.dumps(synthesize(args.n, Fraction(ratio), args.timeout_ms)), flush=True)
