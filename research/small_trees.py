"""Exhaustive shortest-rotation endpoint policies; experimental, not a Lean proof."""
from functools import cache
from itertools import product
from collections import deque

@cache
def trees(n):
    if n == 0:
        return (None,)
    return tuple((l, r) for k in range(n) for l in trees(k) for r in trees(n-1-k))

@cache
def size(t):
    return 0 if t is None else 1 + size(t[0]) + size(t[1])

def neighbors(t):
    if t is None:
        return
    l, r = t
    if l is not None:
        a, b = l
        yield a, (b, r)
    if r is not None:
        a, b = r
        yield (l, a), b
    for u in neighbors(l):
        yield u, r
    for u in neighbors(r):
        yield l, u

def model(n):
    ts = trees(n)
    ids = {t: i for i, t in enumerate(ts)}
    dist = []
    for t in ts:
        d = {t: 0}
        q = deque([t])
        while q:
            u = q.popleft()
            for v in neighbors(u):
                if v not in d:
                    d[v] = d[u] + 1
                    q.append(v)
        dist.append([d[u] for u in ts])
    allowed = [[i for i, t in enumerate(ts) if size(t[0]) == x] for x in range(n)]
    return ts, dist, allowed

def positive_cycle(policy, dist, allowed):
    """Reachability from any common initial tree; weight = B rotations - OPT rotations."""
    count = len(dist)
    value = [-10**9] * (count * count)
    for t in range(count):
        value[t*count+t] = 0
    for _ in range(count*count):
        nxt = value.copy()
        changed = False
        for b in range(count):
            for a in range(count):
                v = value[b*count+a]
                if v == -10**9:
                    continue
                for x, ends in enumerate(allowed):
                    u = policy[b][x]
                    for w in ends:
                        z = u*count+w
                        candidate = v + dist[b][u] - dist[a][w]
                        if candidate > nxt[z]:
                            nxt[z] = candidate
                            changed = True
        if not changed:
            return False
        value = nxt
    return True

def exhaustive(n):
    ts, dist, allowed = model(n)
    choices = [allowed[x] for _ in ts for x in range(n)]
    count = good = 0
    for flat in product(*choices):
        policy = [flat[i*n:(i+1)*n] for i in range(len(ts))]
        count += 1
        if not positive_cycle(policy, dist, allowed):
            good += 1
            print('no positive cycle', policy)
    print(dict(n=n, trees=len(ts), policies=count, no_positive_cycle=good))

if __name__ == '__main__':
    exhaustive(2)
    exhaustive(3)
