# Preferred paths

This section proves the counting identity behind Tango trees. Fix a balanced reference tree on the keys and serve requests one at a time. Each node of the reference tree *prefers* the side of its subtree where the most recent request in that subtree fell. The number of times these preferences change turns out to be exactly Wilber's interleave quantity from [Chapter 11](wilber.html), which is a lower bound on the cost of every BST execution. So an algorithm that pays $O(\log\log n)$ for each preference change is $O(\log\log n)$-competitive. [Chapter 19](tango.html) builds such an algorithm.

```headline preference-interleave
title: Preference changes are Wilber's interleave bound
theorems: Tango.Results.interleave_switches Tango.Results.preference_settings

Fix a reference tree $P$ on $n$ keys and a sequence $X$ of requests. Serve $X$ one request at a time. After each request, every node on the search path to the requested key prefers the side of its subtree that holds that key: the left side if the key is the node itself or lies in its left subtree, the right side otherwise. Then:

- if every request is a key of $P$, the number of **switches**, where a node's preference changes from one side to the other, is exactly Wilber's interleave quantity $\mathrm{IB}_P(X)$ of [Chapter 11](wilber.html);
- the number of **settings**, meaning switches plus the first time each node receives a preference, is at most $\mathrm{IB}_P(X) + n$.

By Wilber's bound, both are $O(\mathrm{OPT} + |X|) + n$, where $\mathrm{OPT}$ is the rotation count of the best offline execution.
```

Splay trees are conjectured to be dynamically optimal, but the best proven competitive ratio for splaying is still $O(\log n)$, the trivial bound that any balanced tree achieves. Tango trees [@demaine2007], introduced at FOCS 2004, were the first online BST algorithm proved $O(\log \log n)$-competitive. Their key idea is to make an algorithm whose cost can be charged directly to a lower bound. They use Wilber's interleave bound from [Chapter 11](wilber.html), which is at most a constant times the cost of any offline execution.

The design uses a fixed balanced **reference tree** $P$ on the same keys. $P$ never changes and it is never stored as a search structure. It serves only as bookkeeping. Each node of $P$ has a **preferred child**: the child on the side where the most recent request in the node's subtree went. Following preferred children from a node gives a downward **preferred path**, and these paths partition the nodes of $P$. Tango stores each preferred path as a small auxiliary BST, of size at most the height $h \approx \log_2 n$ of $P$. The actual BST is made of these auxiliary trees hanging off one another.

A request for $x$ changes the preferred child of some nodes on the reference path from the root to $x$. Each change is repaired by a constant number of cuts and joins on auxiliary trees, at cost $O(\log h) = O(\log\log n)$ each. The total number of changes is essentially Wilber's interleave quantity. The algorithm therefore pays $O(\log\log n)$ per unit of a lower bound on the optimum.

This section covers the reference-tree side of the argument. Everything here is a function of the reference tree and the request sequence alone; no BST is restructured. [Chapter 19](tango.html) builds the actual data structure on top of it.

The box above states the result; checking it needs only Wilber's definitions and the two counts defined here. The section proceeds in order. [Section 18.1](#the-reference-tree) defines the reference trees. [Section 18.2](#preferences-and-switches) defines preferences and proves that switches are the interleave quantity. [Section 18.3](#counting-first-settings) adds the first settings. The last two sections describe the preferred paths themselves and the log of preference updates, which is what the data structure of [Chapter 19](tango.html) replays. The definitions are in `Algorithms/Tango/Definitions/Abstract.lean`, `Reference/`, `Preferences/` and `Paths/`. The theorems are in `Algorithms/Tango/Abstract.lean`.

## The reference tree

Only two properties of the reference tree matter: it has the right number of keys, and it is shallow. The library measures depth by [[RotationBST.Tree.height]] ([Chapter 1](shapes.html#height)), which counts the nodes on a longest root-to-leaf path, not the edges. So a preferred path, which is a set of nodes on one downward path, never has more nodes than the height.

Two families of reference trees are provided. Perfect trees are the classical choice when $n = 2^h - 1$:

@decl RotationBST.Tango.perfect

For every other $n$, the library uses the balanced tree [[RotationBST.Tree.balanced]] of [Chapter 18](static-trees.html#balanced-trees), which splits the remaining keys as evenly as possible, with the larger half on the left. For example, `balanced 7` is `perfect 3`, and `balanced 6` has a left subtree of size $3$ and a right subtree of size $2$. Its height is at most $\lfloor\log_2 n\rfloor + 1$, which is the bound used in the final theorem of [Chapter 19](tango.html). Tango's own names for these two definitions, `Tango.height` and `Tango.balanced`, are aliases.

A preferred path is a path in the ordinary sense. It starts at some node and repeatedly steps to a child:

@decl RotationBST.Tango.DownwardPath

`DownwardPath t path` says that the list of directions `path` (`true` for left, `false` for right) can be followed from the root of `t` without falling off the tree. The path visits `path.length + 1` nodes, counting the start. Two facts are used later.

**Theorem (paths are short).** A downward path of a tree $t$ visits at most `height t` nodes.

**Theorem (perfect trees).** `perfect h` has $2^h - 1$ keys and height $h$.

@decl RotationBST.Tango.Results.path_size RotationBST.Tango.Results.perfect_reference

`path_size` is what bounds the size of every auxiliary tree by `height t`. Every preferred path is a downward path that starts at some node of the reference tree, so it is a downward path of that node's subtree, whose height is at most `height t`. `perfect_reference` is stated with Lean's truncated subtraction; for $h = 0$ it reads $0 = 1 - 1$.

## Preferences and switches

The preference of a reference node is the region its subtree's most recent request fell in. The regions are those of Wilber's bound ([[RotationBST.Wilber.regions]]). A node $v$ splits its subtree into a **left region**, made of $v$ and its left subtree, and a **right region**, made of its right subtree. A request for $v$ itself therefore makes the left child preferred. This is the convention of Demaine, Harmon, Iacono and Pătraşcu, and it is fixed once and for all in Wilber's definitions.

Serving a request for $x$ changes the preference of exactly those nodes on the reference search path to $x$ whose new region differs from their last one. The library counts these changes:

@decl RotationBST.Tango.changes

`changes t past x` walks down the reference search path for `x`. At each node it compares the node's region history (`Wilber.regions … past`, the regions of the past requests that fell in this subtree, oldest first) with the region of `x`, using [[RotationBST.Wilber.switch]]. `switch` returns $0$ if the history is empty. **The first observation of a node sets its preference and is not counted as a change.** Otherwise it returns $1$ exactly when the last observed region differs from the new one. The recursion then continues into the subtree containing `x`, with requests translated to local ranks by [[RotationBST.Wilber.leftRequests]] and [[RotationBST.Wilber.rightRequests]], exactly as in the definition of [[RotationBST.Wilber.interleave]]. It stops at `x` itself.

Summed over a sequence, with each request appended to the history after it is served:

@decl RotationBST.Tango.changeCost

The two theorems below say that this online count is Wilber's quantity. Wilber's definition is offline: for each reference node, it takes the subsequence of requests in the node's subtree and counts how often consecutive ones alternate between the two regions. `changeCost` instead processes requests one at a time and charges each request for the switches it causes. The two agree, step by step and in total.

**Theorem (one step).** Let $x$ be a key of the reference tree $t$. Appending $x$ to any history increases $\mathrm{IB}_t$ by exactly the number of switches that $x$ causes, `changes t past x`.

**Theorem (switches are interleave).** If every request in $X$ is a key of $t$, then $\mathrm{IB}_t(X)$ equals the total number of switches when $X$ is served from the empty history, `changeCost t [] X`.

@decl RotationBST.Tango.Results.interleave_increment RotationBST.Tango.Results.interleave_switches

`interleave_increment` is the one-step identity: appending a valid request `x` to the history increases the interleave quantity by exactly `changes t past x`. Only the nodes on the search path to `x` see a new observation, and each gains an alternation exactly when its region switches. `interleave_switches` follows by induction from the empty history. Both theorems assume the requests are valid ranks of the reference tree. An out-of-range request falls in no region and is ignored by both sides, so the hypothesis is only needed for the step-by-step bookkeeping.

::: note Why this matters
[Chapter 11](wilber.html) proves that [[RotationBST.Wilber.interleave]] of any reference tree is at most $4R + 2m$ for every offline execution with $R$ rotations on $m$ requests ([[RotationBST.Wilber.Results.rotation_lower_bound]]). By `interleave_switches`, the total number of preference switches that Tango has to repair is bounded by the cost of the optimal offline execution, up to a constant. The whole competitive analysis rests on this identity.
:::

### A worked example

Take the perfect reference tree on seven keys, `perfect 3`: root $3$, children $1$ and $5$, leaves $0, 2, 4, 6$. Serve the requests $2, 5, 3, 0$.

| request | nodes whose preference is set for the first time | switches | `changes` |
|---|---|---|---|
| $2$ | $3$ (left), $1$ (right), $2$ (left) | none | $0$ |
| $5$ | $5$ (left) | $3$: left → right | $1$ |
| $3$ | none | $3$: right → left | $1$ |
| $0$ | $0$ (left) | $1$: right → left | $1$ |

`changeCost` is $3$. Computing `interleave` offline gives the same value. At the root, the regions of $2, 5, 3, 0$ are left, right, left, left, with two alternations. At node $1$, the requests $2, 0$ fall right then left, giving one alternation. No other node alternates. Node $3$'s preference is set by the first request and then switched twice. Node $5$ is set once and never switched. For node $5$, the request $5$ is itself, so its left child $4$ becomes preferred.

## Counting first settings

Tango has to pay for first settings as well as switches, because both change the preferred-path structure. The library counts the **runs** of a region trace, meaning the maximal blocks of equal consecutive labels. A nonempty trace with $a$ alternations has $a + 1$ runs:

@decl RotationBST.Tango.runs RotationBST.Tango.preferenceChanges RotationBST.Tango.initializations

`preferenceChanges t xs` is the total number of preference settings over the whole sequence: first settings plus switches, summed over all nodes. It has the same recursive structure as [[RotationBST.Wilber.interleave]], with `runs` in place of `alternations`. `initializations` counts the nodes whose region trace is nonempty, which are the nodes that ever receive a preference. As its docstring notes, this includes leaves, whose preferred "child" is an empty subtree. That only overcounts.

The difference between the two counts is at most one first setting per node.

**Theorem (settings).** For every reference tree $t$ on $n$ keys and every sequence $X$, the number of preference settings is at most $\mathrm{IB}_t(X) + n$.

@decl RotationBST.Tango.Results.preference_settings

This is the source of the additive $O(n \log\log n)$ initialization term in the competitive theorem. On the example above, `preferenceChanges` is $8$: three switches plus five first settings, for nodes $3, 1, 2, 5, 0$. Indeed $8 \le 3 + 7$.

::: check
`preference_settings` has no validity hypothesis. Out-of-range requests fall in no region, so they contribute to neither side.
:::

## The preferred-path partition

At any moment the preferences determine a partition of the reference nodes into downward paths. Start at a node whose parent does not prefer it, and follow preferred children until reaching a node with no preference (never observed) or an empty preferred subtree. The library computes the partition bottom-up:

@decl RotationBST.Tango.PathDecomposition RotationBST.Tango.PathDecomposition.parts

A `PathDecomposition` of a subtree is a pair. The first component is the path that starts at the subtree's root and is still open, because a preferred path may continue upward into the parent. The second component lists the paths that are already closed. `parts` returns all the paths, omitting the open one when it is empty (the empty subtree).

@decl RotationBST.Tango.decomposePaths RotationBST.Tango.preferredPaths

At a node `root = lo + l.size` (keys are absolute ranks here, so `lo` is the subtree's offset, as in [Chapter 1](shapes.html#implicit-keys)), `decomposePaths` reads the node's most recent region with [[RotationBST.Wilber.labels]], which works in absolute ranks.

- **No observation yet.** The node is a path by itself, and both children's paths are closed.
- **Left preferred.** The node is prepended to the left child's open path. The right child's paths are all closed.
- **Right preferred.** The same, with left and right exchanged.

Each path is listed from its shallowest node to its deepest. `preferredPaths reference past` is the resulting partition, with the root's path first.

On the example, after the requests $2, 5, 3, 0$ the paths are $[3, 1, 0]$, $[5, 4]$, $[2]$ and $[6]$. Before any request, all seven nodes are singleton paths. After the second request, $5$, the root path is $[3, 5, 4]$. It continues to $4$ although $4$ was never requested: node $5$ prefers its left region because $5$ itself was requested.

@viz reference {"mode": "paths", "tree": "balanced", "n": 7, "requests": [2, 5, 3, 0, 6, 4, 1], "title": "Preferred paths of perfect 3, continuing the example"}

::: check
- A preferred path is a downward path of the reference tree, so by [[RotationBST.Tango.Results.path_size]] it has at most `height reference` nodes. This bound is what makes the auxiliary trees of [Chapter 19](tango.html) small.
- After a request for $x$, every node on the reference search path to $x$ prefers the side containing $x$, and $x$ prefers its left region. So the root's preferred path passes through $x$. Tango relies on this: the requested key is always in the topmost auxiliary tree after the preferences are updated.
:::

## The update log

The data structure does not recompute the partition from scratch. It replays, for each request, the list of preference settings that the request causes:

@decl RotationBST.Tango.PreferenceUpdate RotationBST.Tango.preferenceUpdates RotationBST.Tango.preferenceLog

A `PreferenceUpdate` names a reference node by its absolute rank, `key`. It records the node's previous preference, `previous`, which is `none` for a first setting, and the new one, `next`, with `true` meaning left. `preferenceUpdates t lo past x` lists the updates for one request, from the reference root down toward `x`, skipping nodes whose preference does not change. It is `changes` with the count replaced by a log of what changed and with first settings included. `preferenceLog` concatenates the logs of a whole sequence, served online.

In the example, the log for the request $5$ is $\langle 3, \text{left}, \text{right}\rangle, \langle 5, \text{none}, \text{left}\rangle$.

The BST of [Chapter 19](tango.html) repairs each entry of the log with at most one cut and one join of auxiliary trees: a first setting only joins, and a switch cuts one subpath and joins another. Summed over a sequence, the log has one entry per preference setting, so its length is bounded by `preferenceChanges`, and hence by the interleave quantity plus $n$ ([[RotationBST.Tango.Results.preference_settings]]). The library proves this bound for the log internally, as part of the competitive theorem. On the reading surface, the per-request bound of [Chapter 19](tango.html) is stated in terms of `(preferenceUpdates reference 0 past x).length`.
