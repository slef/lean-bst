# The Tango BST

No online BST algorithm is known to be dynamically optimal, that is, within a constant factor of the best offline execution on every sequence. Any balanced tree is $O(\log n)$-competitive, and for twenty years after splay trees nothing better was proved. Tango trees were the first online BST with a better ratio: $O(\log\log n)$. This section formalizes them.

[Chapter 18](preferred-paths.html) did the counting. It followed the preferred paths of a fixed reference tree as requests arrive, and showed that the number of preference changes is Wilber's interleave quantity, up to an additive $n$ for first settings. This section builds the BST that tracks those paths, pays $O(\log\log n)$ per change, and so proves the competitive bound.

```headline tango
title: Tango trees are $O(\log\log n)$-competitive
source: @demaine2007
key: yes
theorems: Tango.Algorithm.Results.exists_competitive

For every $n$ there is an online BST algorithm, fixed before any request is known, with the following property. Start from any tree on $n$ keys and serve any sequence $X$ of keys from $\{0,\dots,n-1\}$. Every request is a legal access by rotations, and the total cost (rotations plus one per request) is at most

$$\bigl(56\,L + 16\bigr)\,(\mathrm{OPT} + |X|) \;+\; \bigl(14\,L + 6\bigr)\,n, \qquad L = \log_2(\lfloor\log_2 n\rfloor + 1),$$

where $\mathrm{OPT}$ is the number of rotations of *any* offline execution that serves $X$ from the same initial tree. So the algorithm is $O(\log\log n)$-competitive.

In Lean, the algorithm is an [[RotationBST.Algorithm]], the online algorithms of [Chapter 5](online.html): a step function that sees only the past requests, the current tree and the new request, certified to perform a legal [[RotationBST.Access]] at the cost it reports. The cost is its `totalCost`, and the comparator is any [[RotationBST.Execution]].
```

The section has two layers. To confirm the result, the box above is enough: its statement uses only the rotation model and the online algorithms of Part I, and the [checking page](checking.html) lists those definitions. You never need to know how Tango trees work. To see why the result holds, read on. The section describes the algorithm with its Lean definitions, and states the full theorem again, in English and in Lean, in [Section 19.7](#from-a-policy-to-an-algorithm). [Section 19.1](#auxiliary-trees-inside-a-bst) and [Section 19.2](#three-amortized-operations) build the auxiliary trees and their three operations, [Section 19.3](#marked-trees) the state of the data structure, [Section 19.4](#the-online-policy) the interface that any implementation must satisfy, [Section 19.5](#serving-a-request) the implementation itself, [Section 19.6](#competitiveness) the bound for every policy, and [Section 19.7](#from-a-policy-to-an-algorithm) how a policy becomes an ordinary online algorithm.

The construction is that of Demaine, Harmon, Iacono and Pătraşcu [-@demaine2007]. The BST is a tree of **auxiliary trees**, one per preferred path. Each auxiliary tree is a BST on the keys of its path, so it has at most $h$ nodes, where $h$ is the height of the reference tree. The empty subtrees of an auxiliary tree are not empty in the whole BST: each holds the auxiliary trees of the paths that hang below, in key order. A search for $x$ walks down through a sequence of auxiliary trees, one per preferred path it crosses. Crossing from one path to the next is a preference change. To keep the structure in sync with the preferences, Tango cuts and joins auxiliary trees, which takes $O(\log h)$ per change.

The library follows this plan with one difference. The original paper uses red-black trees with worst-case $O(\log h)$ split and concatenate. The library uses **splay trees** as auxiliary trees and analyses them with the splay potential, so the per-request bound is amortized. The definitions are in `Algorithms/Tango/Auxiliary/Definitions/Abstract.lean`, `State/Abstract.lean`, `Algorithm/Definitions/Abstract.lean`, `Algorithm/Request/Abstract.lean` and `Algorithm/Executable/Abstract.lean`; the theorems are in `Auxiliary/Abstract.lean` and `Algorithm/Abstract.lean`.

## Auxiliary trees inside a BST

An auxiliary tree, together with everything hanging below it, is exactly a rooted region of the BST in the sense of [Chapter 7](regions.html): a [[RotationBST.Region]] (the skeleton of [[RotationBST.Pointer.Lazy.Skeleton]]). Its `node`s are the active nodes, here the keys of one preferred path. Its holes hold the untouched subtrees below, here the other auxiliary trees. Rotations among the active nodes move the holes as blocks, so they are rotations of the whole BST that never enter a lower auxiliary tree.

Four small functions translate between a region and the plain binary tree of its active part:

@decl RotationBST.Region.shape RotationBST.Region.inflate RotationBST.Region.index

`shape` keeps the active nodes and turns every hole into `nil`. The result is the auxiliary tree itself, as an ordinary [[RotationBST.Tree]] whose ranks are ranks among the active keys. `inflate` goes back: it fills the external leaves of a shape, in inorder, with a list of fringe subtrees. It uses `headD .nil` and `drop` so that it is total on lists of the wrong length; the theorems below only apply it to the region's own fringe, which has exactly one subtree per leaf. `index s lo key` converts an absolute key of the whole BST into its rank among the active keys of `s`, by counting the active keys below it. The offset `lo` is the absolute rank of the region's first key, as usual.

@decl RotationBST.Region.auxiliaryRun RotationBST.Region.auxiliaryPotential

`auxiliaryRun s k` splays the active rank `k` with the ordinary [[RotationBST.Splay.run]] of [Chapter 13](splay.html) applied to `shape s`, then re-inflates the result with the original fringe. The rotation count is the count returned by the splay. Splaying the shape and splaying the active part of the full tree perform the same rotations, because a hole is never rotated. `auxiliaryPotential s` is the splay potential of [Chapter 14](analysis.html) with unit weights, applied to the active shape only: $\sum_v \log_2 |\text{active subtree of } v|$. Attached subtrees contribute no mass, because they belong to other auxiliary trees, whose potential is counted separately.

## Three amortized operations

Tango needs three operations on auxiliary trees: access a key, cut off a contiguous piece of keys as a separate auxiliary tree, and join an attached auxiliary tree back in. Each is a few splays, and the access lemma gives each an amortized cost of $3\log_2(\text{size}) + 1$. Since an auxiliary tree holds one preferred path, its size is at most the reference height $h$, so each operation costs $O(\log h) = O(\log\log n)$ amortized.

**Access.** Splaying a key of an auxiliary tree brings it to the root of the whole region, without disturbing anything attached below.

**Theorem (auxiliary access).** Let $s$ be a region with $|s|$ active keys, and let $x$ be one of them. Splaying $x$ within the auxiliary tree is a legal access of $x$ in the region's subtree, leaves every attached subtree in place, and has amortized cost at most $3\log_2|s| + 1$.

@decl RotationBST.Tango.Auxiliary.Results.access

For a region `s` and an active key `x`, where `s.keys 0` means the region's keys counted from offset $0$, the result of splaying `x`'s active rank:

1. has the same fringe, in the same order, so every attached auxiliary tree is intact;
2. is a legal [[RotationBST.Access]] of `x` in the rotation model, so `x` ends at the root and the count is an exact rotation count; and
3. satisfies the amortized bound $\text{cost} + \Phi' - \Phi \le 3\log_2 |s| + 1$, where $|s|$ counts active nodes only.

The bound is the access lemma ([[RotationBST.Splay.Results.access_lemma]]) with unit weights. The root's mass is $|s|$ and $x$'s subtree mass is at least $1$. It does not depend on the sizes of the attached subtrees.

**Split.** Cutting a preferred path at some depth turns its deeper part into a separate auxiliary tree. In key order, the keys of a path below a given depth form a contiguous interval of the path's keys, so a cut separates a prefix, a suffix, or an interior interval of the active keys. The library states the suffix case.

**Theorem (auxiliary split).** Let $s$ be a region and $0 < k \le |s|$. Rotations bring the $k$-th active key to the root of the region, with the earlier active keys in a region $a$ on its left and the later ones in a region $b$ on its right, and the attached subtrees unchanged. Counting $b$ from then on as a separate auxiliary tree, the amortized cost is at most $3\log_2|s| + 1$.

@decl RotationBST.Tango.Auxiliary.Results.split

For $0 < k \le |s|$, there are regions `a` and `b` such that rotations turn `s.tree` into `node a.tree b.tree`. The root of the result is the $k$-th active key, `a` holds the $k-1$ active keys before it and `b` the rest, and the fringe is unchanged. The potential afterwards treats `b` as a separate auxiliary tree: the root component is `node a (hole b.tree)`, in which `b` is a hole, and `b` carries its own potential. The amortized cost is again at most $3\log_2|s| + 1$. The proof splays the $k$-th key to the root. Detaching `b` only lowers the potential, since it removes `b`'s mass from the root's subtree. Prefix and interior cuts are symmetric, or take two such splays. They are internal operations, used by the policy below.

**Join.** The inverse operation merges an auxiliary tree back into the one above it.

**Theorem (auxiliary join).** Let $\mathit{right}$ be a region attached at the last hole of a region $\mathit{left}$. Rotations turn $\mathit{left}$'s subtree into a single region $u$ whose active keys are those of both, with the other attached subtrees unchanged, at amortized cost at most $3\log_2(|\mathit{left}| + |\mathit{right}|) + 1$.

@decl RotationBST.Tango.Auxiliary.Results.join

The hypothesis `attached` says that `right` hangs from the last hole of `left`, meaning it is the rightmost attached subtree. The result `u` has `left`'s fringe with that last hole replaced by `right`'s fringe, so `right`'s active nodes become active in `u`. It is reached from `left.tree` by legal rotations, at amortized cost at most $3\log_2(|left| + |right|) + 1$. The proof splays the maximum of `left`, which exposes `right` as its right subtree, and merges.

::: check
All three statements place the region at offset $0$ and conclude [[RotationBST.Access]] or [[RotationBST.Rotations]] on `s.tree`, the region's own subtree. Inside a larger BST, a region sits at some position, and the rotations are lifted there by `Rotations.inLeft` and `Rotations.inRight` at the same cost.
:::

## Marked trees

The state of the data structure is a BST with one extra bit per child edge, saying whether the edge leaves the current auxiliary tree. The library calls this a *marked tree*:

@decl RotationBST.Tango.MarkedTree RotationBST.Tango.MarkedTree.tree

The two booleans `cutLeft` and `cutRight` belong to the two child edges. A marked edge starts a new auxiliary tree, and an unmarked edge stays inside the current one. `tree` forgets the marks and returns the plain [[RotationBST.Tree]].

The **components** are the maximal pieces connected by unmarked edges. Each is viewed as a [[RotationBST.Region]] whose holes are the marked subtrees below it:

@decl RotationBST.Tango.MarkedTree.region RotationBST.Tango.MarkedTree.rootComponent RotationBST.Tango.MarkedTree.detached RotationBST.Tango.MarkedTree.components

`region` is the component containing the root: it follows unmarked edges and turns each marked subtree into a hole. `rootComponent s lo` is that region with its inorder offset `lo`, or nothing for an empty tree. `detached s lo` collects, in inorder, the root components of all marked subtrees and, recursively, everything below them, with their offsets. `components` is the root component followed by the detached ones, so every node lies in exactly one component.

@decl RotationBST.Tango.MarkedTree.potential RotationBST.Tango.MarkedTree.initial

The potential of a marked tree is the sum of [[RotationBST.Region.auxiliaryPotential]] over its components. `initial reference` is the reference tree with every edge marked. Every node is its own component, which matches the all-singleton preferred paths before any request, and the potential is $0$, since a singleton contributes $\log_2 1$.

The invariant ties the marked tree to [Chapter 18](preferred-paths.html). Its first half says that the components are the preferred paths:

@decl RotationBST.Tango.MarkedTree.Represents

The trees have the same size, the key sets of the components are exactly the key sets of [[RotationBST.Tango.preferredPaths]]` reference past` (as a permutation of lists of finite sets, since rotations change the order in which components are listed), and the root component holds the preferred path that starts at the reference root.

Its second half prescribes the *nesting* of the components: which component hangs in which hole of which other component, in key order. Shapes inside a component are deliberately forgotten, since splaying changes them.

@decl RotationBST.Tango.ComponentNesting RotationBST.Tango.ComponentNesting.fringe RotationBST.Tango.MarkedTree.nesting RotationBST.Tango.MarkedTree.canonical RotationBST.Tango.MarkedTree.Maintains

`nesting` keeps only the tree of components: a branch per component, whose children are the components in its holes, in inorder. `canonical reference lo past` is the reference tree with exactly the preferred edges left unmarked: at each node, the last label of the node's interval (from Wilber's [[RotationBST.Wilber.labels]]) says which child is preferred. `Maintains` asks that the components represent the preferred paths and that their nesting is the nesting of `canonical`.

Under this invariant the marks carry no information beyond the BST and the history: an edge is marked exactly when its two endpoints lie on different preferred paths. [Section 19.7](#from-a-policy-to-an-algorithm) uses exactly this to run Tango without storing the marks.

## The online policy

The library does not fix one implementation in its statements. It defines an interface that any Tango-style implementation must satisfy, and proves the competitive bound for every implementation of it:

@decl RotationBST.Tango.Policy

A `Policy reference` is a step function together with a certificate, in the style of [[RotationBST.Algorithm]]. The step receives the past requests, the current marked tree and the request, and returns the next marked tree and a rotation count. It receives nothing about the future. Its certificate `correct` says that whenever the invariant holds and all requests are valid ranks, the step:

1. is a legal root access of `x` in the rotation model, as in every algorithm of [Chapter 5](online.html);
2. re-establishes the invariant for the extended history `past ++ [x]`; and
3. has amortized cost at most
$$U \cdot (14\log_2 h + 4) + 3\log_2 h + 1,$$
where $U$ is the number of preference updates the request causes, `(preferenceUpdates reference 0 past x).length` from [Chapter 18](preferred-paths.html#the-update-log), and $h$ is the reference height.

Each preference update is repaired by a few auxiliary splays, cuts and joins, each with amortized cost $3\log_2 h + 1$ or less, and the final access of $x$ is one more splay. The constants $14$ and $4$ come from the library's case analysis of a single update.

@decl RotationBST.Tango.Policy.runFrom RotationBST.Tango.Policy.run

`runFrom` threads the marked tree and the history through a request sequence, exactly as [[RotationBST.Algorithm.runFrom]] does, and adds the counts. `run` starts from `MarkedTree.initial reference`, so **the policy starts from the reference tree itself**, with every node its own auxiliary tree.

::: check
`Policy` is not an [[RotationBST.Algorithm]]: its state is a marked tree, not a bare tree. Under the invariant the marks are determined by the tree and the history, so this is a matter of presentation, and the cost counts only rotations, as for algorithms. The library does not package a `Policy` as an `Algorithm`.
:::

## Serving a request

The executable implementation serves a request in two phases:

@decl RotationBST.Tango.MarkedTree.serve

First, `updatePreferences` replays the update log [[RotationBST.Tango.preferenceUpdates]] of the request. For each entry it locates the reference node in the current marked tree and changes the marks of its component. A first setting joins the newly preferred child's auxiliary tree into the node's. A switch cuts the old preferred side off as a new auxiliary tree and joins the new one. The `canonical` marking is passed along so that each edit can find the right component and the interval boundaries of the cut from the reference tree. After the log, the root component is the preferred path from the reference root, which passes through `x` ([Section 18.4](preferred-paths.html#the-preferred-path-partition)).

Second, `splayRoot` splays `x`, at its active rank in the root component, to the root of the whole BST. The cost is the sum of the two phases' rotation counts. The function only inspects the past, the current tree and the request.

@decl RotationBST.Tango.policy

`policy reference` packages `serve` as a `Policy`. Its certificate is the following theorem, which states the three conditions of the contract for `serve` itself.

**Theorem (serving a request).** Suppose the marked tree $s$ satisfies the invariant for the past requests, and all requests so far, and $x$, are keys of the reference tree. Then `serve` performs a legal access of $x$ in the rotation model, the new marked tree satisfies the invariant for the past requests followed by $x$, and the amortized cost is at most $U(14\log_2 h + 4) + 3\log_2 h + 1$, where $U$ is the number of preference updates that $x$ causes and $h$ is the reference height.

The library proves this as `Tango.Algorithm.Executable.Results.request`. Its statement unfolds `serve`, so it reads the internal definitions of the state machine (component paths, contexts, cuts, joins and splays). It is therefore an internal contract in `Algorithm/Executable/Results.lean`, not part of the reading interface: the theorems below need only the `Policy` interface, and [Section 19.7](#from-a-policy-to-an-algorithm) needs only that some policy exists. So the interface is not vacuous.

**Theorem (a policy exists).** For every reference tree there is a policy.

@decl RotationBST.Tango.Algorithm.Results.policy_exists

The witness is the executable `policy reference`. The proof `⟨policy reference⟩` is visible in the source.

## Competitiveness

Every policy, run on a valid sequence, performs a legal execution of the rotation model and ends with the preferred paths of the whole history.

**Theorem (Tango's runs are executions).** Let $p$ be a policy for a reference tree $P$, and let $X$ be a sequence of keys of $P$. The run of $p$ on $X$ is a legal execution of $X$ from $P$ whose rotation count is the count that $p$ reports. The final marked tree satisfies the invariant for $X$.

@decl RotationBST.Tango.Algorithm.Results.execution

The execution starts from `reference`, which is where `run` starts. Its cost is the policy's own count `(p.run xs).2`. This theorem is what gives meaning to that count in the bounds below: it is the exact number of rotations of an [[RotationBST.Execution]].

The main theorem compares the policy's total cost with every offline execution.

**Theorem (Tango is competitive).** Let $p$ be a policy for a reference tree of height $h$ on $n$ keys. Take any offline execution that serves a sequence $X$ of $m$ requests with $R$ rotations, starting from any tree on $n$ keys. Then $p$ serves $X$ with total cost, rotations plus $m$, at most $(56\log_2 h + 16)(R + m) + (14\log_2 h + 4)\,n$.

@decl RotationBST.Tango.Algorithm.Results.competitive

Write $L = \log_2 h$, $m$ for the number of requests, and $R$ for the rotations of any offline execution `comparator` of the same requests, from any start tree of the same size as the reference. Then
$$T_{\text{Tango}} \;=\; \text{rotations} + m \;\le\; (56L + 16)(R + m) + (14L + 4)\,n.$$
The left side is the conventional total cost. The right side is $O(\log h)$ times the comparator's total cost, plus an initialization term.

The proof composes three facts. Summing the per-request contract and telescoping the potential, which starts at $0$ and is never negative, gives at most $|\text{log}| \cdot (14L + 4) + m(3L + 1)$ rotations. The log has at most $\text{interleave} + n$ entries ([[RotationBST.Tango.Results.preference_settings]] and [[RotationBST.Tango.Results.interleave_switches]]). Wilber's bound gives $\text{interleave} \le 4R + 2m$ ([[RotationBST.Wilber.Results.rotation_lower_bound]]). Multiplying out, $R$ gets the coefficient $4(14L + 4) = 56L + 16$, and $m$ gets less than that.

::: check
- The comparator is arbitrary: any offline strategy, from any start tree of the right size, with any final tree. The bound holds against all of them at once, and in particular against the optimum.
- The theorem is about every `p : Policy reference`, not only the executable `policy`. The bound follows from the contract alone.
- The hypothesis `size` fixes the key universe. Validity of the requests is not assumed: it follows from the existence of the comparator ([[RotationBST.execution_exists_iff]]).
:::

For the classical reference trees the height is logarithmic, so the factor is doubly logarithmic.

**Corollary (perfect reference tree).** On $n = 2^h - 1$ keys, with the perfect reference tree, the bound holds with factor $56\log_2 h + 16$ and additive term $(14\log_2 h + 4)\,n$.

**Corollary (every $n$).** For every $n$, with the balanced reference tree on $n$ keys, the bound holds with $h$ replaced by $\lfloor\log_2 n\rfloor + 1$. With the reset of [Section 19.7](#from-a-policy-to-an-algorithm), this gives the result stated at the top of the section.

@decl RotationBST.Tango.Algorithm.Results.perfect_competitive RotationBST.Tango.Algorithm.Results.balanced_competitive

`perfect_competitive` is `competitive` for `perfect h`, rewritten with [[RotationBST.Tango.Results.perfect_reference]]: on $n = 2^h - 1$ keys the factor is $56\log_2 h + 16$, with $h = \log_2(n+1)$. `balanced_competitive` covers every $n$ with the executable [[RotationBST.Tango.balanced]] reference tree. Its height is at most $\lfloor\log_2 n\rfloor + 1$, so
$$T_{\text{Tango}} \le \bigl(56\log_2(\lfloor\log_2 n\rfloor + 1) + 16\bigr)(R + m) + \bigl(14\log_2(\lfloor\log_2 n\rfloor + 1) + 4\bigr)\,n.$$
This is the $O(\log\log n)$-competitiveness of Tango trees, with explicit constants.

::: caveat Compared with the paper
- **Initial tree.** A policy starts from its reference tree, while the comparator starts from any tree of the same size. The next section removes this difference.
- **Amortized auxiliary trees.** The bound is amortized over the whole sequence, through the splay potential. The original analysis with red-black auxiliary trees bounds each request separately. The competitive ratio is the same, $O(\log\log n)$.
- **Uncharged planning.** As everywhere in the rotation model, only rotations and requests are charged. Locating reference nodes, computing the update log and finding cut boundaries are computation on the history, and are free.
- **Constants.** The constants are explicit and not optimized. Only the order $O(\log\log n)$ is meaningful.
- **Not dynamic optimality.** The factor grows with $n$, so this is not a proof that any algorithm is [[RotationBST.TotallyDynamicallyOptimal]].
:::

## From a policy to an algorithm

A policy is not literally an online algorithm in the sense of [Chapter 5](online.html). Its state is a marked tree rather than a tree, it starts from its own reference tree, and its contract only holds while the invariant does. All three differences disappear in one construction.

- **The marks are recomputed.** An [[RotationBST.Algorithm]] sees the past requests, and the marks are a function of them: the run of the policy on the past requests ends in a marked tree that satisfies the invariant. So the algorithm replays the policy on the past requests to recover its marked tree. If the given tree is that marked tree's plain tree, the algorithm takes the policy's step. Otherwise it splays the request, which is always a legal access. In a run from the reference tree the first case always applies, so the algorithm performs exactly the policy's rotations. Replaying is free, like all planning in the rotation model.
- **The start is reset.** On the first request, the algorithm rotates whatever tree it is given into the reference tree, using at most $2n$ rotations ([[RotationBST.Geometry.reset]]), and then continues as above. This is the same wrapper that makes the geometric simulation of [Chapter 17](simulation.html) work from every initial tree.

With the balanced reference tree, the $2n$ rotations of the reset raise the additive term from $(14L + 4)\,n$ to $(14L + 6)\,n$.

**Theorem (Tango trees are $O(\log\log n)$-competitive).** For every $n$ there is an online algorithm such that, for every initial tree on $n$ keys and every offline execution that serves a sequence $X$ of $m$ requests from that tree with $R$ rotations, the algorithm's total cost on $X$ is at most $(56L + 16)(R + m) + (14L + 6)\,n$, where $L = \log_2(\lfloor\log_2 n\rfloor + 1)$.

@decl RotationBST.Tango.Algorithm.Results.exists_competitive

This is the result stated at the top of the section. The comparator now starts from the same tree as the algorithm, as in the definition of competitiveness ([[RotationBST.TotallyDynamicallyOptimal]], [Chapter 5](online.html#dynamic-optimality)), except that the factor is $O(\log\log n)$ instead of a constant. The statement mentions only the rotation model and the online algorithms of Part I. The proof is in `Algorithms/Tango/Algorithm/Online.lean`; the reset wrapper is in `Models/Online/Reset.lean`.

The startup term $(14L + 6)\,n$ is $O(n \log\log n)$. [Chapter 30](tango-linear.html) brings it down to $O(n)$ by updating preferences from the bottom of the search path upwards. That linear startup is what the combined bound of Iacono and Langerman needs ([Chapter 38](combined-finger.html)).
