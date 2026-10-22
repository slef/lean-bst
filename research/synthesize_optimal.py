"""Find experimental exact finite-n optimum among memoryless endpoint policies.

Every simple reachable product cycle uses <=S edges, and both total costs are
positive integers <=S*(diameter+1). Thus every candidate policy's worst cycle
ratio belongs to the finite rational set searched here. UNSAT results are trusted
solver results, not Lean certificates. SAT results use independent verification.
"""
import argparse
import json
from fractions import Fraction
from small_trees import model
from synthesize_policy import synthesize


def search(n, upper, timeout_ms):
    _, dist, allowed = model(n)
    states = sum(len(a)**2 for a in allowed)
    cap = states*(1+max(map(max, dist)))
    candidates = sorted({Fraction(p,q) for q in range(1,cap+1)
                         for p in range(q,min(cap,(q*upper.numerator)//upper.denominator)+1)})
    first = synthesize(n,upper,timeout_ms)
    print(json.dumps(first),flush=True)
    if first['status'] != 'sat':
        return
    lo, hi = 0, len(candidates)-1
    winner = first
    while lo < hi:
        mid = (lo+hi)//2
        result = synthesize(n,candidates[mid],timeout_ms)
        print(json.dumps(result),flush=True)
        if result['status'] == 'unknown':
            return
        if result['status'] == 'sat':
            winner, hi = result, mid
        else:
            lo = mid+1
    if winner['ratio'] != str(candidates[lo]):
        winner = synthesize(n,candidates[lo],timeout_ms)
        print(json.dumps(winner),flush=True)
    print(json.dumps({'experimental_optimum':str(candidates[lo]),'n':n,
                      'cycle_cost_cap':cap,'rational_candidates':len(candidates)}),flush=True)


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('n',type=int)
    p.add_argument('upper',type=Fraction)
    p.add_argument('--timeout-ms',type=int,default=30000)
    a=p.parse_args()
    search(a.n,a.upper,a.timeout_ms)
