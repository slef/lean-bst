# Weight-balanced trees

Rank-balanced trees balance heights. Weight-balanced trees balance sizes. Let the *weight* of a subtree be its number of keys plus one, its number of empty leaves. A tree is *$\beta$-balanced*, for a constant $\beta < 1$, when every child's weight is at most $\beta$ times its parent's. Along any root-to-leaf path the weight then shrinks by a factor $\beta$ at each step, so the height is at most $\log_{1/\beta}(n + 1)$.

There are two ways to restore the invariant after an update. BB[α] trees use rotations at the unbalanced node. Scapegoat trees rebuild a whole subtree into a balanced one. The library formalizes the invariant, rebuilding, and scapegoat trees; BB[α] rebalancing is not formalized yet.

```headline weight-balanced-height
title: Weight-balanced trees have logarithmic height, and a subtree can be rebuilt with two rotations per key
source: @nievergelt1973; @day1976; @stout1986
theorems: Classical.WeightBalanced.Results.height_le Classical.WeightBalanced.Results.rebuild_rotations Classical.WeightBalanced.Results.rebuild_cost

If every child's weight is at most $\beta$ times its parent's, for some $0 < \beta < 1$, then the height, in nodes, is at most $\log_{1/\beta}(n + 1)$. Every tree on $n$ keys can be turned into the balanced tree on the same keys by at most $2n$ rotations.

In Lean, the invariant is [[RotationBST.Classical.WeightBalanced.Balanced]] and rebuilding is [[RotationBST.Classical.WeightBalanced.rebuild]], which returns the balanced tree [[RotationBST.Tree.balanced]] with a number of rotations; `rebuild_rotations` proves that this many rotations reach it.
```

```headline scapegoat
title: Scapegoat trees keep logarithmic depth with $O(\log n)$ amortized cost per update
source: @andersson1989; @galperin1993
theorems: Classical.Scapegoat.Results.run_execution Classical.Scapegoat.Results.reachable_depth Classical.Scapegoat.Results.total_cost

Fix a rational $\frac12 < \alpha < 1$. Start from the empty tree, and run any valid sequence of accesses, insertions and deletions with the scapegoat algorithm. The run is an execution of the dictionary model. At every point, every key lies at depth at most $\log_{1/\alpha} n + 1$. The total cost, rebuilding included, is at most $\sum_i b(n_i)$, where $n_i$ is the number of keys before the $i$-th operation and $b(n) = O(\log n)$ is an explicit bound.

In Lean, the algorithm is [[RotationBST.Classical.Scapegoat.run]], the dictionary execution is [[RotationBST.Dictionary.Execution]] of [Chapter 6](dictionary.html), and the bound is [[RotationBST.Classical.Scapegoat.bound]].
```

## The invariant

@decl RotationBST.Classical.WeightBalanced.weight RotationBST.Classical.WeightBalanced.Balanced

**Theorem (height).** If a tree is $\beta$-balanced, for $0 < \beta < 1$, then its height, in nodes, is at most $\log_{1/\beta}(n + 1)$. The balanced tree on $n$ keys is $\beta$-balanced for every $\beta \ge \frac23$.

@decl RotationBST.Classical.WeightBalanced.Results.height_le RotationBST.Classical.WeightBalanced.Results.balanced_balanced

The constant $\frac23$ comes from the smallest trees: a root with one child has weights $2$ and $3$.

The invariant has one property that a height condition lacks. Suppose a subtree of weight $s$ has just been balanced. Then $\Omega((\beta - \frac12)\, s)$ insertions and deletions must happen inside it before it can violate the invariant again. So work proportional to $s$, spent to restore the balance at that node, can be charged to the updates that broke it. Each update lies below $O(\log n)$ nodes, so it is charged $O(\log n)$ times in total. The scapegoat analysis below makes this argument precise, with a potential.

## Rebuilding

In the rotation model, rebuilding needs no new tool. The reset theorem of [Chapter 3](accesses.html#any-shape-to-any-shape) turns any tree into any other of the same size with at most $2n$ rotations, by rotating both into the right spine. Rebuilding applies the same idea with the balanced tree as the target, and counts the rotations exactly:

@decl RotationBST.Classical.WeightBalanced.vineCost RotationBST.Classical.WeightBalanced.rebuild

`vineCost t` is the number of right rotations that turn `t` into its right spine: each node of the root's left subtree is rotated over the root once, and then the rest of the spine is done the same way. `rebuild t` returns the balanced tree on `t.size` keys, and the number of rotations of two phases: from `t` to the spine, and from the spine to the balanced tree, which is the first phase for the balanced tree, run backwards.

**Theorem (rebuilding).** `rebuild t` is the balanced tree on the keys of `t`, of minimum height $\lfloor\log_2 n\rfloor + 1$. It is reached from `t` by exactly the reported number of rotations, which is at most $2n$.

@decl RotationBST.Classical.WeightBalanced.Results.rebuild_tree RotationBST.Classical.WeightBalanced.Results.rebuild_height RotationBST.Classical.WeightBalanced.Results.rebuild_rotations RotationBST.Classical.WeightBalanced.Results.rebuild_cost

The Day–Stout–Warren algorithm [@day1976; @stout1986] follows the same plan, a vine and back, in linear time and constant extra space. Its second phase compresses the vine into a tree of minimum height that is not exactly [[Tree.balanced]], so the library uses its own second phase. The library specifies rebuilding by its result and its count, and proves that a sequence of that many rotations exists; it does not execute the rotations one by one, and does not model the running time of a rebuilding procedure.

## Restoring by rebuilding: scapegoat trees

Scapegoat trees [@andersson1989; @galperin1993] store no balance information at all. Insertions and deletions are the plain ones, without rebalancing. Balance is restored only occasionally, by rebuilding a subtree.

@decl RotationBST.Classical.Scapegoat.bstDelete RotationBST.Classical.Scapegoat.deleteTarget

A deletion splices out the node, or its successor when the node has two children ([Chapter 6](dictionary.html)). Insertion is [[Tree.insertAt]], which adds a leaf at the gap.

The algorithm keeps one number besides the tree: $N$, the largest number of keys since the last rebuild triggered by a deletion.

- **Insertion.** If the new leaf lands at depth $d$ with $\alpha^d N < 1$, that is $d > \log_{1/\alpha} N$, find the deepest subtree on its search path that is too tall for its size, the *scapegoat*, and rebuild it.
- **Deletion.** If fewer than $\alpha N$ keys remain, rebuild the whole tree, and set $N$ to the number of keys.
- **Access.** Search, and change nothing.

@decl RotationBST.Classical.Scapegoat.Violates RotationBST.Classical.Scapegoat.instDecidableViolates RotationBST.Classical.Scapegoat.fix RotationBST.Classical.Scapegoat.State RotationBST.Classical.Scapegoat.step RotationBST.Classical.Scapegoat.run

`Violates α t k` says that the node of rank `k` lies at depth $d$ in `t` with $\alpha^d\,|t| < 1$: the subtree `t` is too tall for its size. The instance makes the test decidable, so that `fix` can evaluate it. `fix α t k` rebuilds the deepest such subtree on the search path to `k`. Galperin and Rivest define the scapegoat by weight balance, and also discuss a test by height; the library uses a height condition, which yields the same depth bound. `step` returns the new state and the main cost of the dictionary model: one plus the depth of the place of the change, plus the rotations of the rebuilding. The parameter is a rational number, so that `step` and `run` can be evaluated.

**Theorem (scapegoat trees are dictionary algorithms).** Every valid operation is a dictionary step with the reported cost and no data edits, and every valid run is a dictionary execution.

@decl RotationBST.Classical.Scapegoat.Results.step_dictionary RotationBST.Classical.Scapegoat.Results.run_execution

**Theorem (depth).** From the empty tree, after any valid sequence of operations, every key lies at depth at most $\log_{1/\alpha} n + 1$.

@decl RotationBST.Classical.Scapegoat.Results.reachable_depth

The cost bound is amortized. Its potential has two parts: a multiple of the total imbalance $\sum (|\,\mathrm{size}(l) - \mathrm{size}(r)| - 1)^+$ over all nodes, which pays for partial rebuilds, and a multiple of $N - n$, which pays for the rebuild of the whole tree after deletions.

@decl RotationBST.Classical.Scapegoat.sizesFrom RotationBST.Classical.Scapegoat.bound

**Theorem (amortized cost).** From the empty tree, the total cost of a valid sequence of operations is at most $\sum_i b(n_i)$, where $n_i$ is the number of keys before operation $i$ and
$$b(n) = \Bigl(\frac{2}{2\alpha - 1} + 1\Bigr)\bigl(\log_{1/\alpha} n + 2\bigr) + 1 + \frac{2\alpha}{1 - \alpha}.$$
In particular $m$ operations cost at most $m\,b(m)$.

@decl RotationBST.Classical.Scapegoat.Results.total_cost RotationBST.Classical.Scapegoat.Results.total_cost_le

The state includes $N$, which is not stored in the tree, so the algorithm is stated as a function on states rather than as a [[Dictionary.Algorithm]]. The scapegoat search compares depths with subtree sizes; computing those sizes is not charged, since the model counts search paths and rotations only.

## Restoring by rotations: BB[α] trees

@nievergelt1973 introduced trees of *bounded balance*, BB[α]. They keep the invariant above with $\beta = 1 - \alpha$, and repair a node whose balance is violated by a single or double rotation at that node. @blum1980 gave the correct range of the parameter for this repair to work, $\frac{2}{11} < \alpha \le 1 - \frac{\sqrt 2}{2}$. They also proved that rebalancing then needs only $O(1)$ amortized rotations per update. The rotations at a node of weight $s$ are rare: they happen only after $\Omega(s)$ updates below it.

::: todo
- In the parameter range above, single and double rotations restore the invariant after an insertion or a deletion.
- Rebalancing uses $O(1)$ amortized rotations per update.
- The common lemma: a balanced subtree of weight $s$ needs $\Omega((\beta - \frac12)s)$ updates before it violates the invariant.

The height bound for BB[α] trees is the theorem above, with $\beta = 1 - \alpha$. Roadmap [entry 8](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#8-weight-balanced-and-scapegoat-trees).
:::

## Further results

Partial rebuilding is a general technique for making static structures dynamic [@overmars1983]. The weight-balanced trees of @adams1993, the basis of the ordered sets in Haskell's containers library and in Mathlib's `Ordnode`, are a variant of BB[α] trees with integer parameters.
