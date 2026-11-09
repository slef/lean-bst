# Weight-balanced trees

Rank-balanced trees balance heights. Weight-balanced trees balance sizes. Let the *weight* of a subtree be its number of keys plus one. A tree is *$\beta$-balanced*, for a constant $\frac12 < \beta < 1$, when every child's weight is at most $\beta$ times its parent's. Along any root-to-leaf path the weight then shrinks by a factor $\beta$ at each step, so the height is at most $\log_{1/\beta}(n + 1)$.

Nothing in this chapter is formalized yet. The updates need the dictionary model of [Chapter 6](dictionary.html).

## The invariant and its amortization

The invariant has one property that a height condition lacks. Suppose a subtree of weight $s$ is perfectly balanced. Then $\Omega((\beta - \frac12)\, s)$ insertions and deletions must happen inside it before it can violate the invariant again. So work proportional to $s$, spent to restore the balance at that node, can be charged to the updates that broke it. Each update lies below at most $O(\log n)$ nodes, so it is charged $O(\log n)$ times in total.

There are two ways to restore the invariant, and they give the two classical structures.

## Restoring by rotations: BB[α] trees

@nievergelt1973 introduced trees of *bounded balance*, BB[α]. They keep the invariant above with $\beta = 1 - \alpha$, and repair a node whose balance is violated by a single or double rotation at that node. @blum1980 gave the correct range of the parameter for this repair to work, $\frac{2}{11} < \alpha \le 1 - \frac{\sqrt 2}{2}$. They also proved that rebalancing then needs only $O(1)$ amortized rotations per update. The rotations at a node of weight $s$ are rare: they happen only after $\Omega(s)$ updates below it.

::: todo
- BB[α] trees have height at most $\log_{1/(1-\alpha)} (n + 1)$.
- In the parameter range above, single and double rotations restore the invariant.
- Rebalancing uses $O(1)$ amortized rotations per update.

Roadmap [entry 8](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#8-weight-balanced-and-scapegoat-trees).
:::

## Restoring by rebuilding: scapegoat trees

Scapegoat trees [@andersson1989; @galperin1993] store no balance information at all. An insertion that lands deeper than $\log_{1/\alpha} n$ walks back up to find a *scapegoat*, an ancestor whose subtree violates weight balance with $\beta = \alpha$, and rebuilds that subtree into a perfect tree. When deletions shrink the tree by a constant factor, the whole tree is rebuilt.

In the rotation model, rebuilding needs no new tool. The reset theorem of [Chapter 3](accesses.html#any-shape-to-any-shape) turns any tree into any other of the same size with at most $2s$ rotations. Applied inside a subtree of size $s$, with the balanced tree as the target, it rebuilds the subtree with at most $2s$ rotations. The proof of the reset theorem rotates the tree into a right spine and back out. That is also the Day–Stout–Warren algorithm [@day1976; @stout1986], which does it in linear time.

::: todo
- A subtree of size $s$ can be rebuilt into the balanced tree with at most $2s$ rotations, by an explicit linear-time procedure.
- Scapegoat trees have height at most $\log_{1/\alpha} n + 1$.
- An insertion or a deletion costs $O(\log n)$ amortized, rebuilding included.

Roadmap [entry 8](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#8-weight-balanced-and-scapegoat-trees).
:::

## Further results

Partial rebuilding is a general technique for making static structures dynamic [@overmars1983]. The weight-balanced trees of @adams1993, the basis of the ordered sets in Haskell's containers library and in Mathlib's `Ordnode`, are a variant of BB[α] trees with integer parameters.
