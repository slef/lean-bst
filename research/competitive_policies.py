"""Finite-n tree-only competitiveness against all offline executions.

An experimental search, not a uniform-in-n theorem. Exact integer arithmetic
tests rational cycle inequalities; shortest-path distances are from small_trees.
"""
from fractions import Fraction
from itertools import product
from small_trees import model, size


def potential(policy, dist, allowed, ratio):
    root = {t: x for x, ts in enumerate(allowed) for t in ts}
    states = [(a, b) for a in root for b in root if root[a] == root[b]]
    ids = {s: i for i, s in enumerate(states)}
    edges = []
    for a, b in states:
        for x, targets in enumerate(allowed):
            v = policy[b][x]
            for u in targets:
                weight = ratio.denominator * (1 + dist[b][v]) - ratio.numerator * (1 + dist[a][u])
                edges.append((ids[a, b], ids[u, v], weight))
    # Maximum accumulated excess, reachable from a common initial tree.
    values = [0 if a == b else None for a, b in states]
    for _ in states:
        nxt = values.copy()
        for u, v, w in edges:
            if values[u] is not None:
                candidate = values[u] + w
                if nxt[v] is None or candidate > nxt[v]:
                    nxt[v] = candidate
        if nxt == values:
            return states, values, max(v for v in values if v is not None)
        values = nxt
    return None


def search_three():
    ts, dist, allowed = model(3)
    # A simple cycle has <= 9 edges, with each total cost in [1,3].
    # Thus all candidate maximal cycle ratios lie among these fractions.
    ratios = sorted({Fraction(p, q) for p in range(1, 28) for q in range(1, 28) if q <= p <= 3*q})
    best = Fraction(3)
    winners = []
    tested = 0
    for flat in product(*[allowed[x] for _ in ts for x in range(3)]):
        policy = [flat[i*3:(i+1)*3] for i in range(len(ts))]
        tested += 1
        if potential(policy, dist, allowed, best) is None:
            continue
        lo, hi = 0, ratios.index(best)
        while lo < hi:
            mid = (lo + hi) // 2
            if potential(policy, dist, allowed, ratios[mid]) is None:
                lo = mid + 1
            else:
                hi = mid
        value = ratios[lo]
        if value < best:
            best, winners = value, []
        winners.append(policy)
    print('policies', tested, 'best_ratio', best, 'winners', len(winners))
    print('policy', winners[0])
    print('certificate', potential(winners[0], dist, allowed, best))


if __name__ == '__main__':
    search_three()
