"""Exact small-instance cycle checks against the Lean one-bit comparator.
Experimental only: this Python translation is not a Lean certificate.
"""
from fractions import Fraction
from itertools import product
import json
from small_trees import model, size


def move_to_root(t, x):
    l, r = t
    if x < size(l):
        (a, b), k = move_to_root(l, x)
        return (a, (b, r)), k + 1
    if x == size(l):
        return t, 0
    (a, b), k = move_to_root(r, x - size(l) - 1)
    return ((l, a), b), k + 1


def comparator(ts):
    ids = {t: i for i, t in enumerate(ts)}
    leaf = (None, None)
    shapes = [(None, (None, leaf)), (None, (leaf, None)),
              (leaf, leaf), ((None, leaf), None), ((leaf, None), None)]
    a, b, c, d, e = map(ids.get, shapes)
    plans = {(0,c,0):(a,1), (1,a,2):(e,2), (0,e,1):(c,1),
             (1,c,0):(b,2), (0,b,2):(d,1), (1,d,0):(b,1), (1,d,1):(c,2)}
    table = {}
    for q in range(2):
        for t in range(len(ts)):
            for x in range(3):
                if (q,t,x) in plans:
                    u,k = plans[q,t,x]
                    table[q,t,x] = (1-q,u,1+k)
                else:
                    u,k = move_to_root(ts[t],x)
                    table[q,t,x] = (0,ids[u],1+k)
    return table


def certificate(policy, ts, dist, allowed, table, ratio):
    root = {t:x for x,trees in enumerate(allowed) for t in trees}
    states = [(q,a,b) for q in range(2) for a in root for b in root if root[a]==root[b]]
    ids = {s:i for i,s in enumerate(states)}
    edges = []
    for s in states:
        q,a,b = s
        for x in range(3):
            q2,a2,ca = table[q,a,x]
            b2 = policy[b][x]
            w = ratio.denominator*(1+dist[b][b2])-ratio.numerator*ca
            edges.append((ids[s],ids[q2,a2,b2],w))
    values = [0 if q==0 and a==b else None for q,a,b in states]
    for _ in states:
        nxt=values.copy()
        for u,v,w in edges:
            if values[u] is not None and (nxt[v] is None or nxt[v]<values[u]+w):
                nxt[v]=values[u]+w
        if nxt==values:
            return max(v for v in values if v is not None)
        values=nxt
    return None


def main():
    ts,dist,allowed=model(3)
    table=comparator(ts)
    # 2 * 9 equal-root product states, <=3 cost per edge.
    cap=54
    ratios=sorted({Fraction(p,q) for p in range(1,cap+1) for q in range(1,p+1)})
    best=Fraction(3)
    winner=None
    count=0
    for flat in product(*[allowed[x] for _ in ts for x in range(3)]):
        count+=1
        policy=[flat[i*3:i*3+3] for i in range(len(ts))]
        if certificate(policy,ts,dist,allowed,table,best) is None:
            continue
        lo,hi=0,ratios.index(best)
        while lo<hi:
            mid=(lo+hi)//2
            if certificate(policy,ts,dist,allowed,table,ratios[mid]) is None:
                lo=mid+1
            else:
                hi=mid
        best=ratios[lo]
        winner=policy
    print(json.dumps(dict(policies=count,best_ratio=str(best),policy=winner,
        scaled_additive=certificate(winner,ts,dist,allowed,table,best),
        status='experimental, exhaustive policies and exact rational cycle checks')))

if __name__=='__main__':
    main()
