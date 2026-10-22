"""Compute an exact minimum-average periodic BST schedule on small instances.

Finite exhaustive rational search + Bellman-Ford cycle tests. This is an
experiment supporting a computable periodic-probe construction, not Lean code.
All arithmetic is exact. Run: python3 research/periodic_cycle.py
"""
from fractions import Fraction
from small_trees import model


def minimum_cycle(n, period):
    if not period or any(x < 0 or x >= n for x in period):
        raise ValueError('need a nonempty valid period')
    trees, dist, allowed = model(n)
    vertices = [(i, t) for i in range(len(period)) for t in allowed[period[i-1]]]
    ids = {v: i for i, v in enumerate(vertices)}
    edges = [(ids[i, t], ids[(i+1) % len(period), u], 1+dist[t][u])
             for i, t in vertices for u in allowed[period[i]]]
    N = len(vertices)
    max_cost = max(w for _, _, w in edges)

    def potentials(ratio):
        values = [0]*N
        for _ in range(N):
            nxt = values.copy()
            for u, v, w in edges:
                nxt[v] = min(nxt[v], values[u]+ratio.denominator*w-ratio.numerator)
            if nxt == values:
                return values
            values = nxt
        return None

    # Some simple minimum cycle has <=N edges; its ratio is in this finite set.
    candidates = sorted({Fraction(p, q) for q in range(1, N+1)
                         for p in range(q, q*max_cost+1)})
    lo, hi = 0, len(candidates)-1
    while lo < hi:
        mid = (lo+hi+1)//2
        if potentials(candidates[mid]) is not None:
            lo = mid
        else:
            hi = mid-1
    ratio = candidates[lo]
    potential = potentials(ratio)
    assert potential is not None
    tight = [[] for _ in vertices]
    for u, v, w in edges:
        if potential[v] == potential[u]+ratio.denominator*w-ratio.numerator:
            tight[u].append((v, w))
    color = [0]*N
    stack, positions = [], {}

    def visit(u):
        color[u] = 1
        positions[u] = len(stack)
        stack.append(u)
        for v, _ in tight[u]:
            if color[v] == 1:
                return stack[positions[v]:].copy()
            if color[v] == 0:
                result = visit(v)
                if result is not None:
                    return result
        stack.pop()
        del positions[u]
        color[u] = 2
        return None

    cycle = None
    for u in range(N):
        if color[u] == 0:
            cycle = visit(u)
            if cycle is not None:
                break
    assert cycle
    pivot = next(i for i, v in enumerate(cycle) if vertices[v][0] == 0)
    cycle = cycle[pivot:]+cycle[:pivot]
    cost = 0
    for u, v in zip(cycle, cycle[1:]+cycle[:1]):
        cost += next(w for target, w in tight[u] if target == v)
    assert Fraction(cost, len(cycle)) == ratio
    assert len(cycle) % len(period) == 0
    # The potential inequalities independently certify no cycle has lower mean.
    assert all(potential[v] <= potential[u]+ratio.denominator*w-ratio.numerator
               for u, v, w in edges)
    return {'n': n, 'period': period, 'vertices': N, 'mean': str(ratio),
            'cycle_requests': len(cycle), 'cycle_total_cost': cost,
            'phase_tree_cycle': [vertices[u] for u in cycle]}


if __name__ == '__main__':
    import json
    for n, period in [(3, [0,2,1,0,2,0,2,1]), (3, [0,2,1]),
                      (4, [0,3,1,2]), (4, [0,1,2,3])]:
        print(json.dumps(minimum_cycle(n, period)))
