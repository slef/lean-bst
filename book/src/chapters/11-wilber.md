# Wilber's interleave bound

The bounds of [Chapter 10](bounds.html) are upper-bound benchmarks: explicit functions of the request sequence that a good algorithm should match. To show that an algorithm is *competitive*, one needs the other side as well, a lower bound on what every BST execution must pay. Dynamic optimality compares an algorithm with the offline optimum, and nobody knows how to compute that optimum in closed form. Wilber (1989) gave two lower bounds on it that are explicit functions of the sequence. Fifteen years later, Demaine, Harmon, Iacono and Pătraşcu (2004; journal version 2007) built Tango trees around the first one and obtained the first $O(\log \log n)$-competitive BST.

This chapter defines that first bound, the *interleave bound*. Fix any BST $P$ on the $n$ keys, called the reference tree, and count how often the requests alternate between the left and right side of each of its nodes. Wilber's theorem says that every BST execution pays at least a constant fraction of this count. The chapter states the bound against the three cost models of Part I: arborally satisfied point sets, rotation executions and pointer executions. It then explains the proof, which uses Wilber's transition points.

```headline wilber
title: Wilber's interleave bound is a lower bound on every BST execution
source: Wilber, *Lower bounds for accessing binary search trees with rotations* (1989)
key: yes
theorems: Wilber.Results.rotation_lower_bound

Let $P$ be any binary search tree on $n$ keys, and let $\mathrm{IB}_P(X)$ be the total number of left/right alternations of the sequence $X$ at the nodes of $P$ (defined in [Section 11.1](wilber.html#the-interleave-quantity)). Every execution that serves $X = x_1, \dots, x_m$ by rotations, starting from any initial tree on $n$ keys and using $r$ rotations in total, satisfies

$$\mathrm{IB}_P(X) \;\le\; 4r + 2m.$$

So the offline optimum costs at least $\mathrm{IB}_P(X)/4 - m/2$ rotations, for every choice of $P$.

In Lean, the execution is an [[RotationBST.Execution]] from Part I and $\mathrm{IB}_P$ is [[RotationBST.Wilber.interleave]]. The reference tree only needs the right size; it is unrelated to the trees the execution passes through.
```
 The definitions follow the convention of Demaine, Harmon, Iacono and Pătraşcu, written DHIP below. They are in `Bounds/Interleave/Definitions/Abstract.lean`. The theorems are in `Bounds/Interleave/Abstract.lean`.

## The interleave quantity

Fix a *reference tree* $P$ on the same $n$ keys as the BST being analysed. It is a thought experiment only: no algorithm needs to build it, and any shape will do. For a node $y$ of $P$, its subtree covers an interval of keys, which $y$ splits into two regions:

- the **left region**: $y$ itself and its left subtree;
- the **right region**: its right subtree.

Restrict the request sequence $X$ to the keys of $y$'s subtree, and label each remaining request $L$ or $R$ according to its region. The number of *alternations* at $y$ is the number of adjacent pairs of labels that differ. The interleave quantity $\mathrm{IB}_P(X)$ is the sum of the alternations over all nodes $y$ of $P$.

Take the perfect reference tree on the seven keys $0, \dots, 6$ (root $3$, children $1$ and $5$) and the sequence $0\ 4\ 2\ 6\ 1\ 5\ 3$.

- **Root $3$.** It sees every request. Its labels are $L\,R\,L\,R\,L\,R\,L$: the last request is $3$ itself, which belongs to its left region. That gives $6$ alternations.
- **Node $1$.** It sees $0, 2, 1$, labelled $L\,R\,L$: $2$ alternations.
- **Node $5$.** It sees $4, 6, 5$, also $L\,R\,L$: $2$ alternations.
- **Leaves.** Each leaf sees only its own key, which is in its left region, so it never alternates.

So $\mathrm{IB}_P(X) = 10$. The figure computes the same quantity for any sequence. Step through the requests, or click nodes to append requests.

@viz reference {"tree": "balanced", "n": 7, "requests": [0, 4, 2, 6, 1, 5, 3], "title": "Interleave of 0 4 2 6 1 5 3 on the perfect tree"}

The sequence above is the bit-reversal permutation, Wilber's standard hard example: list $0, \dots, 2^k - 1$ in the order of their reversed binary representations. On the perfect tree with $2^k - 1$ keys it makes nearly every node alternate on nearly every request it sees. The interleave quantity is $10$ for $n = 7$, $34$ for $n = 15$, $258$ for $n = 63$ and $8194$ for $n = 1023$, about $(\log_2 (n+1) - 2)\, n$. Requesting the same keys in increasing order gives only $(n-1)/2$. With the lower bound below, this shows that every BST needs $\Omega(n \log n)$ operations on the bit-reversal permutation, while a sequential scan is cheap ([Section 15.4](beyond.html#sequential-access)).

### In Lean

The definition recurses on the reference tree. As everywhere in the library, keys are inorder ranks, and a subtree works in its own local ranks $0, 1, \dots$:

@decl RotationBST.Wilber.regions RotationBST.Wilber.leftRequests RotationBST.Wilber.rightRequests RotationBST.Wilber.alternations RotationBST.Wilber.interleave

At a node `node l r` the local rank of the node itself is `l.size`. Its subtree contains the ranks below `size = l.size + 1 + r.size`.

- `regions leftSize size xs` keeps the requests below `size` and maps each to a Boolean, `true` for the left region (`x ≤ leftSize`, the node included) and `false` for the right.
- `leftRequests` passes the requests strictly below the node to the left subtree, unchanged.
- `rightRequests` passes those strictly above it to the right subtree, translated by `leftSize + 1` into the right subtree's local ranks.
- `alternations` counts adjacent unequal pairs. Lists of length at most one have none.
- `interleave t xs` adds the alternations at the root to those of the two subtrees on their filtered sequences.

::: check
- **Only the first bound.** The docstring of `interleave` says it plainly: the definition alone asserts nothing about BSTs. The lower bound is a separate theorem.
- **Which region holds the node.** Placing $y$ in its left region (`x ≤ leftSize`) is DHIP's convention. A request for $y$ is seen by $y$ and its ancestors, but by none of its descendants.
- **The filter in `regions`.** `· < size` matters only at the root, where it discards out-of-range requests. Further down, `leftRequests` and `rightRequests` have already restricted the sequence to the subtree. The theorems below never rely on it, since they all quantify over executions that can only exist for valid sequences.
- **Arbitrary reference trees.** `interleave` takes any `Tree`, balanced or not. A path gives a small bound; balanced trees give the useful ones.
:::

The bound can also be computed one request at a time. Appending a request $x$ adds a label at every node on the search path to $x$ in $P$, and costs one alternation wherever the new label differs from the previous one. A node's first label costs nothing:

@decl RotationBST.Wilber.switch

`switch past next` is $1$ exactly when `past` has a last element and it differs from `next`. In the proofs, `alternations (bs ++ [b]) = alternations bs + switch bs b`. Tango's vocabulary in [Chapter 18](preferred-paths.html) is built on this. There, the last label at a node is its *preferred child*, and a switch is a change of preferred child. The interleave quantity is exactly the total number of such changes over the whole sequence ([[Tango.Results.interleave_switches]]).

## The lower bound

Wilber's theorem: for every reference tree $P$, every BST execution serving $X$ costs at least a constant fraction of $\mathrm{IB}_P(X)$. The library proves it first in the geometric model of [Chapter 8](geometry.html), where the cost of a solution is its number of points, and transfers it to the two BST models through the equivalences of [Chapter 9](equivalence.html).

**Theorem (interleave bound, geometric form).** Let `reference` be any tree on `n` keys. Every arborally satisfied superset `E` of the request points of `xs` over `n` keys has at least half as many points as the interleave quantity: $\mathrm{IB}(xs) \le 2\,|E|$.

@decl RotationBST.Wilber.Results.interleave_lower_bound

The two BST versions follow by composing with the conversions from executions to point sets. A rotation execution with $r$ rotations yields a solution with at most $2r + m$ points ([[Geometric.Equivalence.Results.rotations_to_ass]]), and a pointer execution of cost $c$ yields one with at most $6c$ points ([[Geometric.Equivalence.Results.pointers_to_ass]]).

**Theorem (interleave bound, BST forms).** Let $P$ be any tree on $n$ keys and $X$ a sequence of $m$ requests. Every rotation execution serving $X$ from a tree on $n$ keys with $r$ rotations satisfies $\mathrm{IB}_P(X) \le 4r + 2m$. Every pointer-machine execution serving $X$ from a tree on $n$ keys at cost $c$ satisfies $\mathrm{IB}_P(X) \le 12c$.

@decl RotationBST.Wilber.Results.rotation_lower_bound RotationBST.Wilber.Results.pointer_lower_bound

Both quantify over all executions [[RotationBST.Execution]] and [[RotationBST.Pointer.Execution]] from every initial tree `s`. They therefore bound the offline optimum, which is the least cost of such an execution.

::: check
- **Two unrelated trees.** The reference tree only has to have the right size (`reference.size = s.size`). It is unrelated to the initial tree `s` of the execution, and to every tree the execution passes through.
- **No additive term.** DHIP state the bound as $\mathrm{OPT} \ge \mathrm{IB}/2 - n$. The versions here have no $-n$, because the potential used in the proof (below) is zero before the first request.
- **Constants.** The factors $2$, $4$, $12$ come from the proof's $2$ per touched node and the conversion constants of [Chapter 9](equivalence.html). They are not claimed to be sharp.
:::

The bound is used through division. If an algorithm costs at most $c \cdot (\mathrm{IB}_P(X) + m)$ plus a startup term, then it is $O(c)$-competitive, because the optimum is at least $\max(m, \mathrm{IB}_P(X)/2)$, up to the constants above. Tango trees achieve this with $c = O(\log \log n)$ for a balanced reference tree ([[Tango.Algorithm.Results.competitive]], [Chapter 19](tango.html)).

## Why it holds: transition points

The proof works in the touched-region model of [Chapter 7](regions.html). It is exactly equivalent to the geometric one ([[Geometric.Equivalence.Results.ass_iff_region_execution]]). There, each request touches a connected region of the current tree that contains the root and the requested key, rearranges it while keeping the hanging subtrees in place, and pays one unit per touched node. The library proves $\mathrm{IB}_P(X) \le 2 \cdot \mathrm{cost}$ for every such execution. The geometric statement then follows from the exact equivalence.

### The transition point of a cut

Fix a reference node $y$ with key interval $[\mathit{low}, \mathit{high})$, which it cuts after the key $\mathit{cut} = y$. Look at the keys of this interval in the *actual* tree at some moment. Exactly one of them is shallowest, and it is an ancestor of all the others, since a search for any key of the interval must pass through it. Call it the *top* of the interval. The top lies on one side of the cut. The **transition point** of $y$ is the top of the *other* side: the shallowest key in the region that does not contain the interval's top.

The proof defines these in `Bounds/Interleave/Transition/Defs.lean`. They are proof vocabulary, which no theorem statement mentions, so the book describes them without quoting the Lean. `topIn t lo low high` searches the tree `t`, whose inorder interval starts at `lo`, for the shallowest rank in the half-open interval `[low, high)`. The search goes right while the current node is below `low` and left while it is at or above `high`. It stops at the first node inside the interval, or returns `none` if the interval contains no key. `transition t low cut high` takes the top of the whole interval. If the top is at most `cut`, it returns the top of the right part `[cut + 1, high)`, and otherwise the top of the left part `[low, cut + 1)`. The left part includes `cut`, as in `regions`.

Three facts about the actual tree make transition points useful. They are proved in `Bounds/Interleave/Transition/` and `Bounds/Interleave/Wilber/Cut.lean`.

1. **Touching an interval means touching its top.** A touched region contains the root and is connected, so if it contains a key of an interval, it contains that interval's top.
2. **An untouched transition point stays put.** If a request's region does not contain $y$'s transition point, then after the rearrangement the transition point is the same key. The region only reorders touched nodes and keeps every hanging subtree, so the tops of both sides are unchanged.
3. **Without the transition point, a request lands on the top's side.** If a request inside $y$'s interval does not touch the transition point, the requested key is on the same side as the interval's top. Otherwise, by fact 1, the region would contain the top of the other side, which is the transition point.

The argument is a potential function. For each cut, let the potential be $1$ when the last label observed at $y$ differs from the side of the current top of $y$'s interval, and $0$ otherwise, including before any observation. Consider a request inside the interval.

- If it does not touch the transition point, then by fact 3 the new label is the top's side, so the potential becomes $0$. An alternation happens only if the previous label differed from that side, that is, only if the potential was $1$. By fact 2 the top's side does not change. So alternations plus potential do not increase.
- If it touches the transition point, the alternation count grows by at most $1$ and the potential is at most $1$. The sum grows by at most $2$.

So the interleave quantity plus the total potential grows by at most twice the number of reference nodes whose transition points are touched. The last ingredient is that different cuts have *different* transition points:

The proof collects them with `transitionKeys reference lo actual`, which lists the transition points in the tree `actual` of all cuts of the reference tree, in preorder. A node whose right region is empty has no transition point, since then `transition` returns `none`. The proof shows that this list has no duplicates. A touched region of $k$ nodes therefore contains at most $k$ transition points, and each request adds at most $2k$ to interleave plus potential. Summing over the execution, and using that the potential starts at $0$ and is never negative, gives $\mathrm{IB}_P(X) \le 2 \cdot \mathrm{cost}$.

::: details Where the potential is in the library
The potential and its accounting are internal. They are `cutPotential`, `potential` and `amortized_step` in `Bounds/Interleave/Wilber/Cut.lean` and `Potential.lean`, and `interleave_le_regions` in `Bound.lean`. None of them occurs in the statements above, which depend only on the definitions displayed in this chapter and the model definitions of Part I. The one-line proofs of those statements name the internal theorems (`Wilber.interleave_le_ass` and its siblings), which link to the source.
:::

### Absolute ranks

The argument is about intervals of the actual tree, which keeps changing. Its keys are global ranks, while `interleave` translates ranks into each subtree's local coordinates. The proof therefore uses a restatement in absolute ranks:

@decl RotationBST.Wilber.labels

`labels low cut high xs` keeps the requests in `[low, high)` and labels them `x ≤ cut`. The proof's internal `absoluteInterleave t lo xs` sums the alternations of these labels over the nodes of `t`, a node at global rank `lo + l.size` having the interval `[lo, lo + l.size + 1 + r.size)`. Every node sees the whole sequence `xs` and filters it itself; nothing is translated. For valid sequences the two quantities agree (the internal lemma `absoluteInterleave_eq`), so the bound proved for `absoluteInterleave` is the bound for `interleave`. Tango's preferred paths are defined from the same absolute labels ([[Tango.decomposePaths]]): the last label at a node is its preferred child.

Switch the figure above to *preferred paths* to preview them. Each node prefers the side of its most recent request, and following preferences from the root down gives the paths that Tango keeps as auxiliary trees.

::: caveat What is not formalized
- **Only the first bound.** Wilber's second lower bound, sometimes called the funnel bound, is not formalized. Neither are the later geometric lower bounds, such as the independent-rectangle bound of Demaine, Harmon, Iacono, Kane and Pătraşcu (2009).
- **No dynamic finger.** Among the upper-bound benchmarks of Part II, the dynamic finger bound (Cole et al., 2000) is not formalized either.
- **No compute time.** Like everything else in the library, the bound counts BST operations only, not the time needed to compute anything.
:::
