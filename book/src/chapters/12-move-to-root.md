# Move-to-root

Part III describes algorithms. Each chapter defines an algorithm as an executable Lean function and then states the bounds it satisfies. The definitions of Part I (what an [online algorithm](online.html#online-algorithms) is and what it pays) and the benchmarks of Part II are fixed beforehand, so every theorem here is a statement about a specific function in a model already explained.

The simplest self-adjusting rule comes first. **Move-to-root** (Allen and Munro, 1978) serves a request by finding $x$ and then rotating it over its parent, again and again, until it is the root. Recently requested keys stay near the top, which is the intuition behind every self-adjusting tree. Under independent random requests, Allen and Munro showed that its expected cost is within a constant factor of the optimal static tree. In the worst case it is poor: a sequential scan costs $\Theta(n)$ rotations per request, forever. Splaying ([Chapter 13](splay.html)) repairs exactly this defect by rotating in pairs.

What the library proves about move-to-root is that it is correct: it really performs an access in the rotation model, and it reports its rotation count truthfully. It proves no amortized bound, in either direction. The poor behaviour on scans is shown at the end of the chapter as a measurement.

```headline move-to-root
title: Move-to-root performs a legal access with fewer than $n$ rotations
source: Allen and Munro, *Self-organizing binary search trees* (1978)
theorems: MoveToRoot.Results.correct

Let $t$ be any binary search tree on $n$ keys and $x$ any of its keys. Move-to-root returns a tree $u$ and a count $k$ such that $k$ rotations turn $t$ into $u$, the key $x$ is the root of $u$, and $k < n$.

In Lean, the algorithm is the function [[RotationBST.moveToRoot]], which returns the pair $(u, k)$. The conclusion is [[RotationBST.Access]] from [Chapter 3](accesses.html#root-accesses): a sequence of exactly $k$ rotations from $t$ to $u$, with $x$ at the root of $u$.
```

In the library, move-to-root plays a second role. It is the constructive witness for the existence results of the rotation model ([Chapter 3](accesses.html#which-requests-can-be-served)): every existing key can be brought to the root, with fewer rotations than there are nodes.

## The algorithm

@decl RotationBST.moveToRoot

`moveToRoot t x` returns the new tree and the number of rotations performed. It follows the three-way search on ranks of [Chapter 1](shapes.html#implicit-keys):

- If `x < l.size`, the key is in the left subtree. The recursive call returns a tree `u` with `x` at its root, `u = node a b`. One right rotation at the root of `node u r` then lifts `x` above its parent: `node (node a b) r` becomes `node a (node b r)`. The cost is the recursive cost plus one.
- If `x = l.size`, the key is already the root, and nothing happens.
- Otherwise the key is in the right subtree, at rank `x - l.size - 1` there, and the mirror-image left rotation lifts it.

The rotations are performed on the way back from the recursion, so the deepest one comes first. Each is a rotation at the root of the current subtree, which in the whole tree is a [[RotationBST.Rotate]]`.right` or `.left` wrapped in `inLeft`/`inRight` constructors. The number of rotations is the depth of $x$.

::: check
- The two branches `| .nil => (.node l r, 0)` cannot occur for a valid rank: when `x < l.size`, the left subtree is nonempty and its recursive result has a root. They make the function total, as does the arbitrary result for out-of-range ranks, which the docstring states explicitly.
- `x - l.size - 1` is truncated subtraction on `Nat`. It is only evaluated when `x > l.size`, so it never truncates.
- The function returns its own cost. Nothing in the definition prevents a wrong count; the theorem below ties it to an actual rotation sequence.
:::

## Correctness

**Theorem (correctness of move-to-root).** For every tree `t` and every rank `x < t.size`, the pair `(moveToRoot t x)` is a legal [root access](accesses.html#root-accesses): there is a sequence of exactly `(moveToRoot t x).2` rotations from `t` to the returned tree, and the returned tree has `x` at its root. Moreover the count is below `t.size`.

@decl RotationBST.MoveToRoot.Results.correct

The "statement reads only" line shows that this theorem depends on nothing but the rotation model and the definition above.

This is the witness behind [[RotationBST.access_exists_iff]]. The count is in fact exactly the depth of $x$, which is at most `t.size - 1`; the library states only the weaker bound, which is what the existence result needs.

## As an online algorithm

Packaged as an [`Algorithm`](online.html#online-algorithms), move-to-root ignores the request history:

@decl RotationBST.moveToRootAlgorithm

The certificate `correct` is the first conjunct of the theorem above. All the definitions of [Chapter 5](online.html) and Part II therefore apply to it: `moveToRootAlgorithm.cost`, its total cost, and the properties `HasWorkingSetBound` and the others of [Chapter 10](bounds.html). The library proves none of those properties for move-to-root, and they fail: on the repeated scans below, the cost per request grows linearly in $n$, while every benchmark of Part II charges a scan request $O(\log n)$.

## Why it is not enough

Start from a left path on $n$ keys, the tree whose root is $n-1$ and whose every node has only a left child, and request $0, 1, \dots, n-1$. Key $0$ is at depth $n-1$; moving it to the root costs $n-1$ rotations and leaves keys $1, \dots, n-1$ in a path hanging from its right child. Each later request is again at the bottom of that path. The scan ends in a left path again, so the next scan costs the same. The figure measures $n(n+1)/2 - 1$ rotations per scan, $\Theta(n)$ per request.

The reason is that move-to-root brings $x$ to the top but pushes every other node of the access path down by one level. The path does not get shorter, it just changes which node is at its top. Splaying differs from move-to-root in one case only. When $x$ and its parent are both left children, or both right children, it rotates the parent over the grandparent first and then $x$ over its parent (the zig-zig step). This roughly halves the depth of every node on the access path. The same scan then costs $O(n)$ in total, the [sequential access theorem](beyond.html#sequential-access).

@viz compare {"sequence": "sequential", "shape": "left-path", "n": 63, "m": 252}

::: exercise The two algorithms on other sequences
With **sequential scans** on a left path of $63$ keys, move-to-root pays $2015$ rotations per scan and splaying about $250$. Switch to **uniform random** requests: the two curves are close, in line with Allen and Munro's average-case analysis. The difference between the algorithms is in the worst case, and only splaying has the amortized guarantees of [Chapter 14](analysis.html).
:::

::: caveat Measured, not proved
The library proves no lower bound for move-to-root. The quadratic scan above is a measurement of the JavaScript port of `moveToRoot`, which the test suite checks against Lean on all shapes with at most five nodes and on random larger trees. It is not a theorem.
:::
