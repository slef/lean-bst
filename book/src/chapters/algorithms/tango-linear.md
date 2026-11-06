# Tango with linear startup

The Tango bound of [Chapter 29](tango.html) has two terms: a factor $O(\log\log n)$ on the cost of the best offline execution, and an additive startup term $(14L + 6)\,n$, where $L = \log_2(\lfloor\log_2 n\rfloor + 1)$. The startup term pays for the first time each reference node receives a preference, so it is $\Theta(n \log\log n)$. That is harmless for competitiveness, but not when Tango is used as one ingredient of a larger bound. Theorem 4.3 of Iacono and Langerman combines GreedyASS with Tango and claims a total cost of

$$O\Bigl(n + \min\bigl(\mathrm{WF}^*(X),\ \mathrm{OPT}(X)\log\log n\bigr)\Bigr),$$

with an additive $O(n)$, not $O(n\log\log n)$. When the optimum is small, an $n\log\log n$ startup on the Tango side would dominate. So the combination needs a Tango whose startup is linear.

This section proves that bound. The algorithm is the Tango of [Chapter 29](tango.html) with one change: within each request, the preference updates are applied **from the bottom of the search path upward** instead of from the top down. With that order, almost every first setting is paid by a credit local to the node's reference subtree, and the credits of a balanced reference tree sum to at most $42n$.

```headline tango-linear
title: Tango with a linear startup term
source: Demaine, Harmon, Iacono and Pătraşcu, *Dynamic optimality—almost* (2004)
key: yes
theorems: Tango.BottomUp.Results.balanced_policy Tango.Algorithm.Rotation.Results.rotation_algorithm

For every $n$ there is a Tango policy for the balanced reference tree on $n$ keys, fixed before any request is known, whose step applies each request's preference updates bottom-up, with the following property. Let $X$ be any sequence of $m$ requests, and take any offline execution that serves $X$ with $R$ rotations from **any** tree on $n$ keys. Then the policy, run from its reference tree, serves $X$ with total cost (rotations plus one per request) at most

$$42\,n \;+\; \bigl(70\,L + 20\bigr)\,(R + m), \qquad L = \log_2(\lfloor\log_2 n\rfloor + 1).$$

Compared with [Chapter 29](tango.html), the startup term $(14L+4)\,n$ of the policy becomes $42n$, and the factor $56L+16$ becomes $70L+20$.

A policy starts from its own reference tree. The second theorem turns any policy into an online algorithm in the sense of [Chapter 5](online.html) that performs exactly the policy's rotations when it starts from the reference tree. From any other tree of the same size it costs at most $m$, plus the policy's rotations, plus $2n$. Combining the two, which is immediate but not stated as one Lean theorem, gives an online BST of total cost at most $44n + (70L+20)(R+m)$ from every initial tree on $n$ keys, against every offline execution from that tree.

In Lean, the policy is a [[RotationBST.Tango.Policy]] whose step is [[Tango.BottomUp.serve]], its cost is that of [[RotationBST.Tango.Policy.run]], the comparator is any [[RotationBST.Execution]], and the online algorithm is an [[RotationBST.Algorithm]] with cost [[RotationBST.Algorithm.totalCost]].
```

```headline tango-linear-credit
title: First preference settings cost linear total
theorems: Tango.BottomUp.Results.startup_bound Tango.Initialization.Local.Results.balanced_localAllowance

Let $P$ be any reference tree of height $h$, and serve a sequence $X$ of $m$ keys of $P$ with bottom-up preference updates, starting from the all-singleton marking. Each preference update gets an amortized charge from its actual position in the evolving auxiliary trees. The charges of all **first settings** together are at most

$$\sum_{v \in P} \bigl(8\log_2 h(v) + 2\bigr) \;+\; m\,\bigl(14\log_2 h + 4\bigr),$$

where $h(v)$ is the height of $v$'s subtree in $P$. The first term is a one-time credit per node; the second is one *ancestor-attachment* charge per request. For the balanced reference tree on $n$ keys, the credit sum is at most $42n$.

In Lean, the first-setting charge is [[Tango.Initialization.firstLogCharge]] of the bottom-up log [[Tango.BottomUp.log]], and the credit sum is [[Tango.Initialization.localAllowance]].
```

If you only want to confirm the result, the first box is enough. Its statements use the rotation model, the online algorithms of Part I, and the `Policy` interface and marked trees of [Chapter 29](tango.html), and the [checking page](checking.html) lists those definitions. The rest of the section explains where the $n\log\log n$ came from and how the bottom-up order removes it. [Section 30.1](#overview) is an overview with a small example. [Section 30.2](#credit-on-the-reference-side) and [Section 30.3](#exact-charges-for-preference-updates) set up the accounting: a credit per reference node, and an exact charge per preference update, which also refines the top-down analysis of [Chapter 29](tango.html). [Section 30.4](#the-bottom-up-policy) defines the bottom-up policy and [Section 30.5](#the-linear-startup) proves the linear startup. [Section 30.6](#from-a-policy-to-an-algorithm) packages a policy as an online algorithm and points to the combination of [Chapter 38](combined-finger.html), which uses this section.

The definitions are in `Algorithms/Tango/Preferences/Initialization/`, `Algorithms/Tango/Algorithm/Initialization/` and `Algorithms/Tango/Algorithm/BottomUp/`, each with a `Definitions/Abstract.lean`; the online packaging is in `Algorithms/Tango/Algorithm/Rotation/Abstract.lean`.

## Overview

### Where the startup term comes from

Recall the accounting of [Chapter 29](tango.html). A request for $x$ produces an update log: one entry for each node on the reference search path to $x$ whose preference changes ([[RotationBST.Tango.preferenceUpdates]]). An entry is either a **switch**, where a node's preferred child changes sides, or a **first setting**, where a node that has never been observed receives a preference. The policy contract charges every entry $14\log_2 h + 4$, and every request $3\log_2 h + 1$ for the final splay. Switches total Wilber's interleave quantity, which is $O(\mathrm{OPT} + m)$. First settings number at most $n$, once per node, so they cost $(14\log_2 h + 4)\,n$. That is the startup term.

The flat charge for a first setting is pessimistic. A first setting at $v$ only *joins*: it merges the auxiliary tree of $v$'s newly preferred child into the auxiliary tree that contains $v$. In the library's analysis a join costs at most $8\log_2 s + 2$ amortized, where $s$ is the size of the merged auxiliary tree. The question is how large $s$ is.

In the original **top-down** order, the updates of a request run from the reference root toward $x$. When the update reaches $v$, every ancestor of $v$ on the search path already prefers the side toward $x$, so $v$ already lies in the root's auxiliary tree. The merged tree contains all of $v$'s ancestors, so $s \ge \mathrm{depth}(v)$. Most nodes of a balanced tree are deep, so most first settings really cost $\Theta(\log h) = \Theta(\log\log n)$.

### Bottom-up order

Apply the same updates in reverse, from $x$ up to the reference root. When the update reaches a node $v$ that is set for the first time, consider its parent $u$ on the path.

- **$u$ is new as well.** Then $u$'s update comes later, and $u$ has no preference yet, so the edge from $u$ to $v$ still leaves the auxiliary tree. The tree containing $v$ is a downward path that starts at $v$, so the merged tree lies inside $v$'s reference subtree: $s \le h(v)$, the height of that subtree. The join costs at most $8\log_2 h(v) + 2$, a credit that depends only on $v$.
- **$u$ was observed before.** Nothing on the search path below $u$ was ever requested, since $v$ is unobserved. So $v$ is the topmost new node of this request, and there is at most one such node per request. If $u$ prefers some other child, $v$ is again at the top of its auxiliary tree and the local bound applies. If $u$ already prefers $v$, then $v$ hangs in an existing auxiliary tree of ancestors. That happens only when $v$ is the left child of $u$ and the last request in $u$'s subtree was $u$ itself. This join is the **ancestor attachment**, charged the flat $14\log_2 h + 4$.

Switches are unchanged: each still costs $14\log_2 h + 4$ and is counted by the interleave quantity. Over a run, each node's local credit is spent at most once, and there is at most one attachment per request:

$$\text{first-setting charges} \;\le\; \sum_v \bigl(8\log_2 h(v) + 2\bigr) \;+\; m\,(14\log_2 h + 4).$$

The credit sum is linear for a balanced tree, because $\log_2 h(v) \le h(v) + 1$ and the subtree heights of a balanced tree sum to at most $4n$:

$$\sum_v \bigl(8\log_2 h(v) + 2\bigr) \;\le\; 8\cdot 4n + 10n \;=\; 42\,n .$$

The attachment charge goes into the per-request term, which is why the factor grows from $56L + 16$ to $(56L+16) + (14L+4) = 70L + 20$.

Two facts make the reordering safe. The updates of one request concern distinct nodes, and setting the preference of one node does not affect another, so the reversed log produces exactly the same final marking ([[Tango.BottomUp.Results.preferenceUpdates_reverse_canonical]]). And every intermediate marking is still a valid path marking, which is all that the edits of [Chapter 29](tango.html) need.

### An example

Take the reference tree `balanced 7` (root $3$, children $1$ and $5$, leaves $0, 2, 4, 6$) and the first request $0$. All three nodes $3, 1, 0$ on the path are set for the first time, each toward its left child. The library's regression tests compute the size of the merged auxiliary tree at node $1$:

| order | updates | merged tree at $1$ | charge at $1$ | local credit of $1$ |
|---|---|---|---|---|
| top-down | $3, 1, 0$ | $\{3, 1, 0\}$, size $3$ | $8\log_2 3 + 2 \approx 14.7$ | $8\log_2 2 + 2 = 10$ |
| bottom-up | $0, 1, 3$ | $\{1, 0\}$, size $2$ | $8\log_2 2 + 2 = 10$ | $10$ |

Top-down, node $1$ joins after its ancestor $3$, and its charge exceeds its credit. Bottom-up, it joins before, and the charge fits. Node $0$ is a leaf, and its first setting points toward an empty child. There is nothing to join, and the implementation now performs no rotation at all (see [the section on exact charges](#exact-charges-for-preference-updates)).

The attachment case is real. In the tree below, with past requests $4$ and then $3$, both prefer their left child. Node $1$ has never been observed, but it already hangs in the auxiliary tree $\{4, 3, 1\}$.

```
        4            past requests: 4, 3
       /             auxiliary tree {4, 3, 1}
      3
     /
    1                request 0: 1 is set for the first time,
   / \               and joins 0 into {4, 3, 1}
  0   2
```

The request $0$ sets $0$ and then $1$ for the first time. The join at $1$ produces a tree of size $4$ and is charged $8\log_2 4 + 2 = 18$, while the local credits of $0$ and $1$ are only $2 + 10 = 12$. The regression module checks both numbers. This is why a per-request attachment allowance is needed: local credit alone does not suffice.

::: note Compared with the papers
- Demaine, Harmon, Iacono and Pătraşcu bound Tango's running time by $O((\mathrm{OPT}(X) + n)(1 + \log\log n))$, with the $n\log\log n$ coming from first settings, as in [Chapter 29](tango.html). The bottom-up order and the local-credit argument are the library's. They change neither the data structure nor the order of magnitude of the competitive ratio.
- Combining Binary Search Trees (Demaine, Iacono, Langerman and Özkan) treats $O(\log\log n)$-competitiveness as a well-behaved bound with overhead $O(n\log\log n)$, in its Corollary 4. The additive $O(n)$ of Iacono and Langerman's Theorem 4.3 needs the Tango side to have overhead $O(n)$; the paper does not spell this step out. This section supplies it, and [Chapter 38](combined-finger.html) uses it.
:::

## Credit on the reference side

The first layer of accounting lives entirely in the reference tree, like [Chapter 28](preferred-paths.html): a weight per reference node, spent when the node is observed for the first time.

@decl Tango.Initialization.allowance Tango.Initialization.observedCharge Tango.Initialization.firstCharge

For a weight function $w$ on absolute ranks:

- `allowance t lo w` is the total weight of the nodes of `t`, a subtree at offset `lo`.
- `observedCharge t lo past w` is the total weight of the nodes that `past` has observed, meaning the nodes whose subtree contains at least one past request. It has the recursive shape of [[RotationBST.Tango.initializations]], which counts the same nodes.
- `firstCharge updates w` sums the weights of the first-setting entries of an update log, the entries whose `previous` is `none`.

The weight belongs to the node, whenever it happens to be observed. The following theorems say that first settings are exactly the newly observed nodes, so every node pays its weight at most once.

@decl Tango.Initialization.Results.allowance_eq_sum Tango.Initialization.Results.observed_step Tango.Initialization.Results.observed_log

`allowance_eq_sum` writes the allowance as a plain sum over the ranks `lo, …, lo + size - 1`. `observed_step` says that serving a valid request $x$ increases the observed charge by exactly the first-setting charge of $x$'s update log, and `observed_log` sums this over a sequence served online, with the log [[RotationBST.Tango.preferenceLog]] of [Chapter 28](preferred-paths.html).

**Theorem (one payment per node).** For nonnegative weights and any valid sequence $X$ following a history `past`, the first settings of $X$ cost at most the weight not yet observed: $\mathrm{firstCharge} \le \mathrm{allowance} - \mathrm{observedCharge}(\mathit{past})$. In particular, from the empty history, they cost at most the whole allowance.

@decl Tango.Initialization.Results.remaining_budget Tango.Initialization.Results.first_budget

The two counting identities behind [[RotationBST.Tango.Results.preference_settings]] also hold exactly for a continued history:

@decl Tango.Initialization.Results.first_count Tango.Initialization.Results.switch_count

`first_count` says that the first-setting entries of the log of $X$, added to the nodes observed by `past`, give the nodes observed by `past ++ X`. `switch_count` says the same for switches and Wilber's [[RotationBST.Wilber.interleave]]. Together they say that the log of $X$ consists of exactly $\mathrm{IB}(\mathit{past} \mathbin{+\!\!+} X) - \mathrm{IB}(\mathit{past})$ switches and as many first settings as newly observed nodes.

### Local credit

The weight used for the linear startup is the local join bound: $8\log_2 h(v) + 2$ for each node $v$, where $h(v)$ is the height of $v$'s subtree.

@decl Tango.Initialization.heightAt Tango.Initialization.heightSum Tango.Initialization.localCredit Tango.Initialization.localAllowance

`heightAt t key` is the height, in nodes as in [[RotationBST.Tango.height]], of the subtree of `t` rooted at the node of inorder rank `key`, and $0$ for ranks outside `t`. `heightSum t` is the sum of all subtree heights. `localCredit t key` is $8\log_2(\mathtt{heightAt}\ t\ \mathit{key}) + 2$, a function of the fixed reference tree only. Its docstring stresses that it is not the charge of the evolving components; the bounds below relate the two. `localAllowance t` sums the credits structurally, and `allowance_localCredit` identifies it with the allowance of the weight `localCredit`.

**Theorem (the credit of a balanced tree is linear).** The subtree heights of `balanced n` sum to at most $4n$, and its local credits sum to at most $42n$.

@decl Tango.Initialization.Local.Results.heightSum_cap Tango.Initialization.Local.Results.balanced_heightSum Tango.Initialization.Local.Results.allowance_localCredit Tango.Initialization.Local.Results.balanced_localAllowance

`heightSum_cap` is the general fact behind it. A tree of height at most $h$ has no more total subtree height than the complete tree of height $h$, whose height sum is $2^{h+1} - h - 2$. Since `balanced n` has height $\lfloor\log_2 n\rfloor + 1$ and $2^{\lfloor\log_2 n\rfloor} \le n$, this gives $\mathrm{heightSum} \le 4n$, including incomplete last levels and $n = 0$. The proof of `balanced_localAllowance` then uses $\log_2 h \le h + 1$ to get $\mathrm{localAllowance}\ t \le 8\,\mathrm{heightSum}\ t + 10\,|t|$, hence $42n$. The constant is not optimized.

@decl Tango.Initialization.Local.Results.balanced_firstCharge Tango.Initialization.Local.Results.balanced_remainingCharge

Specialized to the local credit of `balanced n`, the budget theorems read: the first settings of any valid sequence from the empty history are charged at most $42n$, and after a history `past`, at most $42n$ minus the credit that `past` has already spent. The second form applies to a run resumed after an arbitrary valid history.

## Exact charges for preference updates

The second layer charges each update for what it really costs in the BST. [Chapter 29](tango.html) used the flat bound $14\log_2 h + 4$ for every update. The library now has a refined charge that distinguishes first settings and records the actual size of the merged auxiliary tree.

@decl Tango.Initialization.componentCharge Tango.Initialization.updateCharge Tango.Initialization.logCharge

The charges are computed on the **reference marking**, the marked reference tree whose unmarked edges are the current preferred edges, like [[RotationBST.Tango.MarkedTree.canonical]]. The actual BST is a different marked tree with the same component nesting.

- `updateCharge reference key next` locates the reference node of rank `key` (with the internal `locateKey`, which returns the node and the list of frames on the path to it). If both child edges of the node are marked, the node has no preference yet and this is a first setting, charged by `componentCharge`. Otherwise it is a switch, charged $14\log_2 h + 4$ with $h$ the reference height. An out-of-range key is charged $0$; such keys do not occur in generated logs.
- `componentCharge fs l r next` is the join bound $8\log_2 s + 2$, where $s$ is the size of the auxiliary tree that contains the node after the update. That tree is computed by plugging the node, with its new marks, into the unmarked frames above it (`componentAddress`), so it includes every ancestor already in the node's component. If the newly preferred child is empty, the charge is $0$.
- `logCharge reference updates` adds the charges of a log, and advances the reference marking after each entry with the internal `setPreference`. Each entry is therefore classified and measured on the marking it actually meets, not by the `previous` label recorded in the log. This matters once logs are reordered.

The zero for empty children reflects a change of the implementation, the **redundant-splay skip**. When a first setting points toward an empty child, there is no auxiliary tree to join, and the auxiliary trees do not change. Only the mark changes. The executable edit (the internal `unmarkKnownInPath`, used by both the top-down and the bottom-up policy) now returns the tree unchanged with cost $0$ in that case, instead of performing the merge at the component boundary. For instance, the first time a leaf is requested, its first setting points toward its empty left child. The following theorems state the effect of a first-setting edit, with or without an empty target:

@decl Tango.Initialization.Results.empty_component Tango.Initialization.Results.empty_update_cost Tango.Initialization.Results.component_charge Tango.Initialization.Results.initial_component Tango.Initialization.Results.initial_update

These are statements about the internal edit `setMarksInPath`, which changes the marks of one node inside the auxiliary tree described by the frames `fs`, and about `updatePreference`, which locates the node from the reference marking and calls it.

- `empty_component` and `empty_update_cost`: a first setting toward an empty child returns the same tree and $0$ rotations, even when the node's component is nested below other components.
- `component_charge`: for a first setting, the edit produces the nesting of the updated marking, is a legal sequence of [[RotationBST.Rotations]], and has amortized cost (rotations plus the change of [[RotationBST.Tango.MarkedTree.potential]]) at most `componentCharge`: $0$ toward an empty child, $8\log_2 s + 2$ otherwise.
- `initial_component` is the same bound without the empty case, $8\log_2 s + 2$.
- `initial_update` is the version through `updatePreference`, with $s$ bounded by the reference height. Summed over $n$ first settings, this is the old $n\log\log n$ bound.

@decl Tango.Initialization.Local.Results.root_component_charge

`root_component_charge` is the local case in its simplest form. When the node is the root of the reference marking, with no frames above it, the amortized cost of its first setting is at most its own local credit. The bottom-up proof applies this at every *component boundary*, a node whose parent edge is marked.

### The charge of a single update and of a log

With the charges defined, the per-update contract reads as follows.

**Theorem (one update).** Let $s$ be a marked BST with the same component nesting as the reference marking, and let the reference marking give each node at most one preferred child (the internal predicate `PathMarked`). Updating the preference of a valid node produces the nesting of the updated marking, by legal rotations, at amortized cost at most `updateCharge`. The same holds for a whole log, with `logCharge`.

@decl Tango.Algorithm.Initialization.Results.update_spec Tango.Algorithm.Initialization.Results.log_spec Tango.Algorithm.Initialization.Results.logCharge_append

The hypothesis is only that $s$ and the reference marking agree on the nesting, not that the marking is canonical for some history. This is what allows applying the updates in any order: every intermediate marking of a reordered log still satisfies `PathMarked`. `logCharge_append` splits the charge of a concatenated log at the intermediate marking.

The refined charge is never worse than the flat one of [Chapter 29](tango.html):

@decl Tango.Algorithm.Initialization.Results.updateCharge_le Tango.Algorithm.Initialization.Results.logCharge_le

### First settings and switches, from the marks

To separate the two kinds of updates, the library classifies each entry by the marks it meets.

@decl Tango.Initialization.virginCount Tango.Initialization.firstAt Tango.Initialization.firstCount Tango.Initialization.laterCount Tango.Initialization.firstLogCharge

`virginCount` counts the nodes with both child edges marked, the nodes without a preference. Its docstring says it includes "empty-child marks": a leaf counts until it is first set, even though its preferred child is empty. `firstAt reference key` says that the node of rank `key` has no preference yet. Along a log, with the marking advanced after each entry, `firstCount` counts the entries that meet an unset node, `laterCount` the others, and `firstLogCharge` keeps only the charges of the first ones.

@decl Tango.Algorithm.Initialization.Results.virgin_step Tango.Algorithm.Initialization.Results.virgin_log Tango.Algorithm.Initialization.Results.virgin_canonical

Each first setting removes exactly one unset node (`virgin_step`, `virgin_log`), and the canonical marking of a history has exactly $n - \mathrm{initializations}$ unset nodes (`virgin_canonical`). So the classification by marks agrees with the reference-side counts:

@decl Tango.Algorithm.Initialization.Results.firstCount_generated Tango.Algorithm.Initialization.Results.laterCount_generated Tango.Algorithm.Initialization.Results.logCharge_split Tango.Algorithm.Initialization.Results.firstLogCharge_le Tango.Algorithm.Initialization.Results.generated_split

On the top-down log of a continued history, `firstCount` is the number of newly observed nodes and `laterCount` is the increase of the interleave quantity. `logCharge_split` splits any log's charge into its first-setting part and $14\log_2 h + 4$ per later entry. `firstLogCharge_le` bounds the first part by $14\log_2 h + 4$ per first setting, which is the old bound again. `generated_split` combines them for a run from the initial marking: the total charge is the first-setting charge plus $\mathrm{IB}(X)\,(14\log_2 h + 4)$.

### The top-down policy with exact charges

These charges sharpen the analysis of the existing top-down step [[RotationBST.Tango.MarkedTree.serve]] of [Chapter 29](tango.html). The request charge is the refined log charge of the request's update log, plus $3\log_2 h + 1$ for the final splay.

@decl Tango.Initialization.requestCharge Tango.Initialization.sequenceCharge

**Theorem (top-down Tango with exact charges).** Under the invariant [[RotationBST.Tango.MarkedTree.Maintains]] of [Chapter 29](tango.html), the top-down step is a legal access, preserves the invariant, and has amortized cost at most the refined request charge. Over a run from the reference tree, the rotations are at most the first-setting charge plus $\mathrm{IB}(X)(14\log_2 h + 4) + m(3\log_2 h + 1)$, and the total cost is at most the first-setting charge plus $(56\log_2 h + 16)(R + m)$ against any offline execution.

@decl Tango.Algorithm.Initialization.Results.request_spec Tango.Algorithm.Initialization.Results.sequenceCharge_eq Tango.Algorithm.Initialization.Results.runFrom_bound Tango.Algorithm.Initialization.Results.run_bound Tango.Algorithm.Initialization.Results.policy_exists Tango.Algorithm.Initialization.Results.separated_run_bound Tango.Algorithm.Initialization.Results.separated_competitive

`runFrom_bound` and `run_bound` hold for every policy `p` whose step is `MarkedTree.serve` (the hypothesis `steps`), and `policy_exists` provides one. `separated_competitive` separates the startup from the competitive part. In the top-down order, the only bound available for the first-setting charge is `firstLogCharge_le`, $(14\log_2 h + 4)$ per node. So this is where the top-down analysis stops: with an unresolved $n\log\log n$.

## The bottom-up policy

The new step differs from [[RotationBST.Tango.MarkedTree.serve]] in a single word: it applies the reversed update log.

@decl Tango.BottomUp.serve Tango.BottomUp.log

`serve s reference past x` computes the update log of $x$ from the history, reverses it, and replays it on the actual marked BST `s` with the internal `updatePreferences`, advancing the canonical reference marking `canonical reference 0 past` after each entry. Then it splays $x$ to the root within the root component, exactly as before. The cost is the sum of the two rotation counts. `log reference past xs` is the log that a run actually replays: the update log of each request, reversed, concatenated in request order. Only the updates within a request are reordered, so the run remains online.

### Reordering is harmless

@decl Tango.BottomUp.Results.setPreference_commute Tango.BottomUp.Results.applyPreferences_reverse Tango.BottomUp.Results.preferenceUpdates_reverse_canonical Tango.BottomUp.Results.log_canonical Tango.BottomUp.Results.log_append

Setting the preferences of two different nodes commutes (`setPreference_commute`), so a log with pairwise distinct keys gives the same marking in either order (`applyPreferences_reverse`). The update log of one request has distinct keys, one per node on the search path. Hence the reversed log turns the canonical marking of `past` into the canonical marking of `past ++ [x]` (`preferenceUpdates_reverse_canonical`), and the whole bottom-up log does the same for a sequence (`log_canonical`). `log_append` splits the log of a concatenated sequence.

### The contract

The bottom-up request charge is the refined log charge of the reversed log, measured on the marking each entry actually meets, plus the final splay:

@decl Tango.BottomUp.requestCharge Tango.BottomUp.sequenceCharge

Its docstring makes the point explicit: the charge uses the intermediate reference markings in bottom-up order, not those of the top-down execution.

**Theorem (serving a request bottom-up).** Under the invariant of [Chapter 29](tango.html), the bottom-up step performs a legal access of $x$, preserves the invariant for `past ++ [x]`, and has amortized cost at most the bottom-up request charge.

@decl Tango.BottomUp.Results.request_spec

This is the analogue of the internal contract of [Chapter 29](tango.html), stated here with the refined charge. Since the refined charge is at most the flat one, the step also satisfies the `Policy` contract, so it is a [[RotationBST.Tango.Policy]] (the internal `BottomUp.policy`).

@decl Tango.BottomUp.Results.sequenceCharge_eq Tango.BottomUp.Results.runFrom_bound Tango.BottomUp.Results.run_bound Tango.BottomUp.Results.policy_exists Tango.BottomUp.Results.runFrom_append

These are the run-level forms. `sequenceCharge_eq` rewrites the summed request charges as one log charge of `log reference past xs` plus $m(3\log_2 h + 1)$. `runFrom_bound` and `run_bound` telescope the potential, for every policy whose step is `BottomUp.serve`. `policy_exists` provides such a policy, with the run bound. `runFrom_append` is a general fact about policies: running on `xs ++ ys` is running on `xs` and then resuming on `ys` from the returned marked tree, with the counts added. A worker that is paused and resumed relies on it.

### The same counts in a different order

Reordering must not change *how many* first settings and switches there are. The bottom-up log is a permutation of the top-down log within each request, and the classification by marks still agrees with the reference-side counts:

@decl Tango.BottomUp.Results.firstCharge_log Tango.BottomUp.Results.firstCount_generated Tango.BottomUp.Results.laterCount_generated Tango.BottomUp.Results.generated_split Tango.BottomUp.Results.separated_competitive

`firstCharge_log` says that the bottom-up and the top-down log have the same first-setting charge for every weight function. `firstCount_generated` and `laterCount_generated` say that, measured on the marks, the bottom-up log of a continued history still has one first setting per newly observed node and one later entry per new unit of interleave. A regression test checks that reversing does not turn switches into first settings. `generated_split` and `separated_competitive` are the bottom-up versions of the top-down statements above: the run's total cost is at most the first-setting charge plus $(56\log_2 h + 16)(R + m)$.

## The linear startup

All that remains is the bound on the first-setting charge in bottom-up order.

**Theorem (local credit plus one attachment per request).** For any reference tree of height $h$ and any valid history and continuation $X$ of $m$ requests, the first-setting charge of the bottom-up log of $X$, measured on the evolving marking, is at most the local credit of the first-set nodes plus $m(14\log_2 h + 4)$. From the empty history, it is at most `localAllowance` plus $m(14\log_2 h + 4)$.

@decl Tango.BottomUp.Results.first_log_bound Tango.BottomUp.Results.startup_bound

The proof is the argument of the overview, by induction on the reference tree for one request. Inside a newly observed subtree, every first setting meets a component boundary, so `root_component_charge`, in an internal form plugged into the surrounding frames, bounds it by the node's local credit. Only the topmost first setting of the request may join an existing ancestor component, and that one is bounded by `updateCharge_le`. `startup_bound` then sums the local credits with `first_budget`: each node's credit is spent once.

@decl Tango.BottomUp.Results.balanced_remainingCharge Tango.BottomUp.Results.balanced_startup_remaining

For `balanced n`, the credit is at most $42n$, and a resumed run only has the credit not yet spent by its history: $42n - \mathrm{observedCharge}$, plus the attachment term.

**Theorem (linear-startup Tango).** For a policy whose step is the bottom-up step, the rotations of a run on $m$ valid requests are at most

$$\mathrm{localAllowance} + \mathrm{IB}(X)\,(14\log_2 h + 4) + m\,(17\log_2 h + 5),$$

and against any offline execution with $R$ rotations, from any tree of the same size, the total cost is at most $\mathrm{localAllowance} + (70\log_2 h + 20)(R + m)$.

@decl Tango.BottomUp.Results.linear_run_bound Tango.BottomUp.Results.linear_competitive

The factor $17\log_2 h + 5$ is the attachment charge $14\log_2 h + 4$ plus the final splay $3\log_2 h + 1$. In `linear_competitive`, Wilber's bound $\mathrm{IB} \le 4R + 2m$ ([[RotationBST.Wilber.Results.rotation_lower_bound]]) turns the interleave term into $(56\log_2 h + 16)(R + m)$, and the attachment term is absorbed as $(14\log_2 h + 4)(R + m)$. Validity of the requests follows from the comparator.

**Theorem (balanced reference).** With the balanced reference tree on $n$ keys, the bound is $42n + (70L + 20)(R + m)$ with $L = \log_2(\lfloor\log_2 n\rfloor + 1)$, and a policy with this bound exists.

@decl Tango.BottomUp.Results.balanced_competitive Tango.BottomUp.Results.balanced_policy

`balanced_competitive` applies to every policy whose step is `BottomUp.serve`, and uses $\mathrm{height}(\mathtt{balanced}\ n) \le \lfloor\log_2 n\rfloor + 1$. `balanced_policy` is the headline: one policy, chosen before the requests and the comparator, satisfying the bound for all of them. Its proof is `⟨policy (balanced n), …⟩`, the executable bottom-up policy.

::: check
- **Start tree.** As in [Chapter 29](tango.html), the policy's run starts from its reference tree, `MarkedTree.initial (balanced n)`, while the comparator starts from any tree of size $n$. The next section removes this asymmetry at the price of $2n$ rotations.
- **No hidden inputs.** The hypothesis `steps` is discharged by the witness, and none of the bounds assumes anything about the request sequence beyond what the comparator implies.
- **Constants.** $42$, $70$ and $20$ are explicit, unoptimized witnesses. The attachment term costs a larger multiplicative constant than [Chapter 29](tango.html); only the startup became smaller, from $(14L+4)\,n$ to $42n$.
:::

## From a policy to an algorithm

A policy becomes an ordinary online algorithm by the construction of [Chapter 29](tango.html): recompute the marks by replaying the policy on the past requests, which is free planning in the rotation model, and reset any other initial tree to the reference tree on the first request, with at most $2n$ rotations ([[RotationBST.Geometry.reset]]). The library states this once, for every policy.

**Theorem (a policy as an online algorithm).** For every policy $p$ with reference tree $P$, there is an online algorithm that, run from $P$ on valid requests, produces exactly the policy's final tree and rotation count, and whose total cost from any tree of the same size is at most $m + \mathrm{rotations}(p) + 2n$.

@decl Tango.Algorithm.Rotation.Results.rotation_algorithm

The first conjunct compares [[RotationBST.Algorithm.runFrom]] from the reference tree with the plain tree of the policy's run. The second bounds [[RotationBST.Algorithm.totalCost]] from any `saved` tree. With `balanced_policy`, it gives the online algorithm of the headline: total cost at most $44n + (70L+20)(R + m)$ against every offline execution from the same initial tree. The library does not state this composition as a separate theorem; the existing [[RotationBST.Tango.Algorithm.Results.exists_competitive]] still uses the top-down policy.

The real consumer is the combination of [Chapter 38](combined-finger.html). There the bottom-up policy, packaged by `rotation_algorithm`, becomes an interruptible Tango worker for the ComboBST machinery of [Chapter 33](combining.html), with startup $2816n$ ([[RotationBST.Tango.Combination.Results.linear_balanced_worker]]). Its linear startup is what lets the combined bound of Theorem 4.3, [[RotationBST.Geometric.GreedyASS.Combination.Deamortized.Results.combined]], keep an additive $O(n)$.
