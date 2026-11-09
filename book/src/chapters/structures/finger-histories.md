# Finger histories and simulation

Section 3 of Bose, Collette, Fagerberg and Langerman [-@bose2012] shows that any BST algorithm can be run inside another BST that stays balanced at all times. The original algorithm, the *source*, keeps a persistent finger. Each of its instructions moves the finger to a child or to the parent, or rotates the finger over its parent. The simulating BST, the *physical tree*, keeps its own cursor at the root between instructions, and the source finger's node sits at that root. The path from the root to the source finger is stored upside down as two weighted pop-tarts ([Chapter 44](pop-tarts.html), [Chapter 45](chocolate.html)), and the subtrees hanging off that path are stored recursively as heavy-path representations ([Chapter 46](heavy-paths.html), [Chapter 47](recursive-heavy-paths.html)). Every source instruction becomes a constant number of pop-tart operations. Every node of weight $w$ stays at physical depth $O(\log(W/w))$, where $W$ is the total weight. This is the paper's Theorem 5.

This section formalizes that simulation, as needed by the deamortization of [Chapter 37](deamortization.html). The representation of a source finger is a *finger history*: a state whose pop-tarts and payload layouts are whatever earlier instructions left behind, not a canonical rebuild of the current source tree. The section proves that each of the six source instructions maps one valid history to another at constant amortized cost and $O(\log n)$ worst-case cost. It then packages the steps into one online *policy*, runs it on instruction streams and on request sequences, and bounds the depth of every key at every intermediate physical configuration, including those in the middle of the response to one source instruction.

```headline finger-histories-simulation
title: Any finger can be simulated by a BST of weight-balanced depth
source: @bose2012
theorems: HeavyPath.Finger.History.Simulation.Results.policy_within_exists HeavyPath.Finger.History.Simulation.Results.initialized_run HeavyPath.Finger.History.Simulation.Interruption.Results.run_weighted_prefix HeavyPath.Finger.History.Simulation.Results.root_key HeavyPath.Finger.History.Simulation.Results.depth
skip: instDecidableEqLabelledTree | The derived decidable-equality instance for labelled trees only decides the tests `l = .nil` and `r = .nil` inside [[HeavyPath.extract]], which the recursive payload layouts use. Any two instances for the same proposition agree, so it cannot change which layouts are valid.

Fix a weight $w(a)$ for every label $a$. There is a policy $p$ with the following properties. To answer one source instruction, $p$ sees only the current source cursor, the current physical representation and that instruction.

Let the source finger point at a node of a labelled tree $T$ with $n$ nodes and positive weights. Let $W$ be the total weight, and let $w_i$ be the weight of the $i$-th label of $T$ in inorder. Then the physical tree, starting as $T$ itself with its cursor at the root, can be reshaped into a starting representation by a pointer-machine trace of cost $s_0$. The trace satisfies $s_0 + \Phi_0 \le 39n$, where $\Phi_0 \ge 0$ is the starting potential. Take any stream of $m$ source instructions that is legal from the source finger. Running $p$ instruction by instruction then succeeds and ends in a valid representation of the final source cursor, with the following guarantees:

- the startup and the responses together form one pointer-machine trace from $T$, of cost $s_0 + C$ with $s_0 + C + \Phi \le 39n + 62m$, where $\Phi \ge 0$ is the final potential;
- each source instruction is answered by at most $34 + 24\log_2 n$ physical instructions, which start and end with the physical cursor at the root;
- in every valid representation, between instructions, the physical root holds the source finger's node, and the node of rank $i$ is at depth at most $15 + 15\log_2(W/w_i)$;
- at *every* instruction boundary of the emitted physical program, even in the middle of a response, the node of rank $i$ is at depth at most

$$336 + 240\,\log_2 \frac{W}{w_i}.$$

In Lean, the per-instruction bound is part of [[HeavyPath.Finger.History.Simulation.PolicyBounded]], and [[HeavyPath.Finger.History.Simulation.PolicyWithin]] extends it. Depths count edges ([[Tree.depth]]), and a rank is an inorder position. The policy is obtained by choice from the existence of a response for each step, so the theorem asserts that a function with these properties exists, not that it is computable. It depends on the weights, because the physical layout does.
```

::: note Do you need this section?
Only if you want to see how the deamortization works inside. The theorems that other chapters quote are [[Deamortization.Weighted.Results.simulation]] and the scheduler results of [Chapter 37](deamortization.html), and the replay of source algorithms inside ComboBST workers ([Chapter 33](combining.html) and the sections after it) and in the combined finger BST ([Chapter 38](combined-finger.html)). Those statements mention the policy, the state and the request runs defined here. To check those results, you only need [Section 49.6](#policies) and [Section 49.10](#serving-requests): what a policy promises, and how a source algorithm is described. The rest is the simulation itself: the invariant, the six instruction lemmas, and the depth analysis.
:::

## Overview

Three objects are involved.

- The **source cursor** is a [[LabelledCursor.Config]] (a zipper): a focused labelled subtree `node left key right` together with its context frames `cs`, innermost first. The source finger is the node `key`. The source instructions are the six [[Multifinger.Opcode]]s, with the labelled semantics [[LabelledCursor.perform]]: move to the left or right child, move to the parent, or rotate the finger over its parent. A rotation keeps the finger on the same node. Labels travel with their nodes, and $w$ is a function of the labels.
- The **finger history** is a [[HeavyPath.Finger.History.State]]. It records one entry per source ancestor of the finger, a pair of Chocolate pop-tarts ([[Finger.Pair]], [Chapter 48](heavy-path-fingers.html)), and the physical layouts of the finger's two children.
- The **physical tree** is `s.pair.tree`, an unlabelled [[Tree]] with the same number of nodes, operated on by the single-cursor pointer machine of [Chapter 6](pointer.html).

The physical tree has this shape. It is Figure 5 of the paper with the lower side mirrored:

```text
                       key                      ← physical root = source finger
                 ╱              ╲
     lower pop-tart, mirrored     upper pop-tart
     leaves, left to right:       leaves, left to right:
       payload of a₁                right subtree of key
       payload of a₂                payload of b_j
       …                            …
       left subtree of key          payload of b₁

  a₁ … a_i : ancestors smaller than key (the cursor went right at them), root first
  b₁ … b_j : ancestors larger than key (the cursor went left at them), root first
```

The internal nodes of each pop-tart are the ancestor keys of its side. The leaves are the *payloads*: the off-path subtree of each ancestor, and, innermost, the corresponding child subtree of the finger. Each payload is itself stored as a recursive heavy-path layout ([[Recursive.History.Layout]], [Chapter 47](recursive-heavy-paths.html)). The stack top of each pop-tart is at the finger end. So the ancestors nearest the finger, and the finger's children, are near the physical root. A source instruction changes only that end:

- **Down.** The finger moves into one of its children. The old finger becomes an ancestor and is pushed onto one stack, its other child becomes that ancestor's payload, and the new finger's two children are exposed from the old child's layout.
- **Up.** The inverse: the innermost ancestor is popped and becomes the finger again.
- **Rotation.** The finger and its parent exchange roles. The parent leaves its stack, and the two payloads it separated are joined with it into one.

Each instruction is a constant number of pushes, pops and top replacements on Chocolate pop-tarts, plus local surgery on the recursive layouts. A pop-tart operation has $O(1)$ amortized and $O(\log n)$ worst-case cost (Lemma 4 of the paper), so a source instruction costs at most $62$ physical instructions amortized against the state potential, and at most $34 + 24\log_2 n$ in the worst case.

The depth bound is the paper's telescoping argument. A pop-tart stores a leaf of weight $w$ at depth $O(\log(W/w))$. A payload's weight is its whole subtree mass, and inside the payload the recursive heavy-path layout again stores a node of weight $w$ at depth $O(\log(\text{mass}/w))$. The logarithms telescope to $15 + 15\log_2(W/w)$.

**Why "history".** After a few instructions the pop-tarts and payload layouts are no longer the canonical ones that [[Finger.build]] would produce from the current source tree. A payload that was split and later rejoined may have a different shape, and the potential records its imbalance. The invariant therefore accepts *any* layout that a valid sequence of stack operations can produce, as [[Recursive.History.Layout]] does for heavy paths. Two equal source subtrees may be laid out differently at different places.

**Why intermediate depths.** Theorem 5 of the paper says that depths are "always" $O(\log(W/w))$, and its proof bounds them in the representation, that is, between simulated source instructions. Theorem 6 interrupts the simulated program every $c\log n$ physical operations to serve the next request. Such an interruption can fall in the middle of the $O(\log n)$ instructions that answer one source instruction. The formalization therefore also bounds the depth of every key at every physical instruction boundary ([Section 49.9](#interrupting-a-response)).

The section proceeds as follows. [Section 49.2](#the-representation) defines the state and its invariant. [Section 49.3](#what-a-valid-state-guarantees) lists what a valid state guarantees. [Section 49.4](#the-starting-state) builds the first state. [Section 49.5](#the-six-instructions) gives the six instruction lemmas. [Section 49.6](#policies) packages them as a policy and [Section 49.7](#running-a-policy) runs it. [Section 49.8](#cheapest-representations) shows that starting from the cheapest representation removes the potential from the cost bound. [Section 49.9](#interrupting-a-response) bounds depths inside responses, and [Section 49.10](#serving-requests) lifts everything to request sequences.

## The representation

The definitions are in `Structures/HeavyPath/Finger/History/Definitions/Abstract.lean`.

### Slots charged toward the finger

The leaves of a weighted pop-tart carry weights. The ancestor keys are internal nodes, which the pop-tarts of [Chapter 44](pop-tarts.html) do not weigh. So the weight of each ancestor key is moved onto the next leaf toward the finger:

@decl HeavyPath.Finger.History.sideSlots

`sideSlots weight boundary shape carry es` lists the leaves of one side, outermost first. Each ancestor entry `e` contributes its payload's physical shape `e.shape`, with weight `carry` plus the payload's mass. Then the ancestor's own key weight becomes the `carry` of the next leaf. The last leaf is the finger's child `boundary`, physically laid out as `shape`. It receives the key weight of the innermost ancestor on that side. The slot weights of both sides therefore add up to the total mass minus the finger's own weight ([[HeavyPath.Finger.History.Results.state_mass]]). This is the history version of [[Finger.sideSlots]] ([Chapter 48](heavy-path-fingers.html)). That function computes each payload's shape with the canonical rebuild, while this one takes the recorded shape of each [[Recursive.History.Entry]].

### States and potential

@decl HeavyPath.Finger.History.State HeavyPath.Finger.History.State.potential

A state has five components:

- `ancestors`: one [[Recursive.History.Entry]] per source ancestor, innermost first. An entry is the source frame (ancestor key, side, off-path subtree), the physical shape of that subtree, and its credit.
- `leftShape`, `rightShape`: the physical layouts of the finger's two children.
- `leftCredit`, `rightCredit`: their credits.
- `pair`: the two pop-tarts, a [[Finger.Pair]]. Its physical tree is the finger node with the mirrored lower pop-tart on the left and the upper pop-tart on the right. The leaves of the pop-tarts are the payload shapes.

The potential is the pop-tart potential of the pair ([[Finger.Pair.potential]]) plus the credits of the two children and of every ancestor payload. A credit is itself the potential of a recursive layout, so the potential counts every pop-tart nested anywhere in the physical tree. It is a natural number. The cost bounds below are amortized against it.

### The invariant

@decl HeavyPath.Finger.History.Valid

`Valid weight cs left key right s` says that `s` represents the source cursor with focus `node left key right` and context `cs`. Its eight fields are the whole invariant:

@decl HeavyPath.Finger.History.Valid.positive HeavyPath.Finger.History.Valid.context HeavyPath.Finger.History.Valid.pair HeavyPath.Finger.History.Valid.leftLayout HeavyPath.Finger.History.Valid.rightLayout HeavyPath.Finger.History.Valid.children HeavyPath.Finger.History.Valid.lower HeavyPath.Finger.History.Valid.upper

1. `positive`: every weight in the whole source tree is positive ([[HeavyPath.Positive]]). The depth bounds divide by weights.
2. `context`: the sources of the ancestor entries are exactly the context frames. So the state records the actual source path from the root to the finger.
3. `pair`: both Chocolate pop-tarts are valid (at level $0$).
4. `leftLayout`, `rightLayout`: the finger's children are laid out as recursive heavy-path histories with the recorded shapes and credits.
5. `children`: so is every ancestor's off-path payload.
6. `lower`, `upper`: the leaves of the two pop-tarts, read in inorder, are exactly the slots of the two sides. [[Recursive.History.lower]] selects the ancestors smaller than the finger, root first, and [[Recursive.History.upper]] those larger, innermost first. The latter list is reversed so that `sideSlots` again runs from the root toward the finger.

The path from the root to the finger is not required to be a heavy path. The whole path is held by one pair of pop-tarts, whatever its edges, and only the payloads use the heavy-path decomposition. Depth is not a field either: it is a consequence of the invariant ([[HeavyPath.Finger.History.Results.state_depth]]), so the instruction lemmas never need to re-establish it.

## What a valid state guarantees

These theorems are in `Structures/HeavyPath/Finger/History/Abstract.lean`. Each assumes `Valid weight cs left key right s`, and writes $T$ = `plug cs (node left key right)` for the whole source tree.

**Theorem (same keys, finger at the root).** The physical tree has as many nodes as $T$. The physical root has the inorder rank of the source finger. If the labels are ordered by a preorder and $T$ is a search tree, there is exactly one labelling of the physical tree that has $T$'s inorder and is a search tree. The finger's weight plus the slot masses of the pair is the total mass of $T$. Each side has the size of its blocks: the ancestors on that side with their payloads, plus the finger's child on that side.

@decl HeavyPath.Finger.History.Results.state_size HeavyPath.Finger.History.Results.state_root_key HeavyPath.Finger.History.Results.state_labels HeavyPath.Finger.History.Results.state_mass HeavyPath.Finger.History.Results.state_side_sizes

`state_root_key` compares [[Pointer.Config.key?]] at the physical root with the rank of the source cursor ([[LabelledCursor.Config.erase]]). So the pointer machine, whose searches start at the root, finds the source finger there at no cost. `state_labels` says that the physical tree is a BST on the same keys. The physical tree is unlabelled, and `state_labels` says how its nodes inherit the source labels.

**Theorem (depth).** The node of inorder rank $i$ in $T$, with weight $w_i$, has physical depth at most $15 + 15\log_2(W/w_i)$, where $W$ is the total weight. Consequently, the pointer machine can walk from the root to that node and back, with the same cost $k$ each way, such that $1 + 2k \le 31 + 30\log_2(W/w_i)$.

@decl HeavyPath.Finger.History.Results.state_depth HeavyPath.Finger.History.Results.state_depth_at HeavyPath.Finger.History.Results.state_search_walk

`state_depth` names the node by an occurrence in the inorder list (`before ++ target :: after`, of rank `before.length`), and `state_depth_at` by a rank in `Fin`. The walk in `state_search_walk` is navigation only: it never rotates, and it returns to the same tree with the cursor at the root. The $1$ is the unit charge of the request.

**Theorem (potential).** The potential of a valid state is at most $20n - 20$, where $n$ is the size of $T$.

@decl HeavyPath.Finger.History.Results.potential_bound

The bound holds for every valid history, not only for freshly built ones. [Section 49.10](#serving-requests) uses it to bound the work on any window of requests without assumptions about the starting potential.

## The starting state

A valid state always exists, and the canonical one is reachable cheaply. Given positive weights, there is a valid state whose pair is the canonical [[Finger.build]] of [Chapter 48](heavy-path-fingers.html). Its potential is at most $23n$. Starting from the source tree itself, read as an unlabelled tree with the cursor at the root, the pointer machine reaches the physical tree of some valid state in at most $16n$ instructions, and that state can be chosen with potential at most $23n$, so that startup cost plus potential is at most $39n$.

@decl HeavyPath.Finger.History.Results.build_state HeavyPath.Finger.History.Results.build_state_bounded HeavyPath.Finger.History.Results.state_initialization HeavyPath.Finger.History.Results.state_initialization_bounded

The source finger may be anywhere in $T$. The startup trace begins from $T$'s own shape, which is how the physical machine starts: before the simulation begins, the physical and source trees coincide. The constant $23n$ is the one the initialization proof produces, and [[HeavyPath.Finger.History.Results.potential_bound]] improves it to $20n - 20$ after the fact. The $39n$ is what enters every startup-inclusive bound below.

## The six instructions

Each source instruction has a lemma in three strengths. The plain version gives a valid successor state, reached by a [[Pointer.Trace]] from the physical root to the physical root, and an amortized bound $\text{cost} + \Phi' \le K + \Phi$. The `_bounded` version adds a worst-case bound $\text{cost} \le a + 24\log_2 n$, where $n$ is the physical size. The `_within` version replaces the trace by a [[Pointer.TraceWithin]] ([Chapter 12](replay.html)). That trace keeps the size and satisfies, at every one of its instruction boundaries, $\mathrm{depth}(x) \le 16\cdot\mathrm{depth}_0(x) + b$ for every rank $x$, where $\mathrm{depth}_0$ is the depth in the starting physical tree. Each lemma also says exactly how the list of ancestor entries changes.

| instruction | amortized $K$ | worst case | intermediate depth |
|---|---|---|---|
| move down | $54$ | $26 + 24\log_2 n$ | $16\,d + 64$ |
| move up | $62$ | $34 + 24\log_2 n$ | $16\,d + 96$ |
| rotate | $50$ | $22 + 24\log_2 n$ | $16\,d + 56$ |

The policy below uses the worst row of each column: $62$, $34 + 24\log_2 n$ and $16d + 96$.

### Moving down

**Theorem (move down).** Suppose the finger `key` has a nonempty left child `node l x r` and right subtree `sibling`. Then there is a valid state for the finger `x`, whose new innermost ancestor is `key` with payload `sibling`. That payload keeps the old physical shape and credit of the right child. The cost satisfies the bounds of the table. The right move is the mirror image.

@decl HeavyPath.Finger.History.Down.Results.downLeft HeavyPath.Finger.History.Down.Results.downRight HeavyPath.Finger.History.Down.Results.downLeft_bounded HeavyPath.Finger.History.Down.Results.downRight_bounded HeavyPath.Finger.History.Down.Results.downLeft_within HeavyPath.Finger.History.Down.Results.downRight_within

The equation for `next.ancestors` shows the history at work. The old right child is not rebuilt. Its layout is reused as the payload of a new entry, so equal source subtrees can end up with different layouts. Physically, the top leaf of the lower pop-tart, the layout of the old left child, is opened at `x`. Its place is taken by `x`'s left child `l`. The old finger becomes an internal node of the upper pop-tart, its old right child stays there as a leaf, and `x`'s right child `r` is pushed as the new top leaf. On the pair this is the transfer [[Finger.Pair.downLeft]] of [Chapter 48](heavy-path-fingers.html).

### Moving up

**Theorem (move up).** Suppose the finger `key`, with children `l` and `r`, is the left child of `parent`, whose right subtree is `sibling`. Then there is a valid state for the finger `parent`, with left child `node l key r` and right child `sibling`. Its ancestors are the old ones without the innermost entry, and the cost satisfies the bounds of the table. The case of a right child is symmetric.

@decl HeavyPath.Finger.History.Up.Results.upLeft HeavyPath.Finger.History.Up.Results.upRight HeavyPath.Finger.History.Up.Results.upLeft_bounded HeavyPath.Finger.History.Up.Results.upRight_bounded HeavyPath.Finger.History.Up.Results.upLeft_within HeavyPath.Finger.History.Up.Results.upRight_within

Moving up is the most expensive instruction. The parent is popped from its stack, and the old finger with both its children must be merged back into one payload with a valid recursive layout.

### Rotating at the finger

**Theorem (rotation).** Suppose the finger `key`, with children `l` and `r`, is the left child of `parent`, whose right subtree is `sibling`. Then there is a valid state for the rotated cursor: the finger is still `key`, now in the parent's position, with left child `l` and right child `node r parent sibling`. Its ancestors are the old ones without the innermost entry, and the cost satisfies the bounds of the table. The case of a right child is symmetric.

@decl HeavyPath.Finger.History.Rotation.Results.rotateLeftChild HeavyPath.Finger.History.Rotation.Results.rotateRightChild HeavyPath.Finger.History.Rotation.Results.rotateLeftChild_bounded HeavyPath.Finger.History.Rotation.Results.rotateRightChild_bounded HeavyPath.Finger.History.Rotation.Results.rotateLeftChild_within HeavyPath.Finger.History.Rotation.Results.rotateRightChild_within

Together with the moves, these are the six cases of [[LabelledCursor.perform]]. The physical tree is not rotated like the source. The physical root stays the finger, the parent leaves its stack, and the two payloads it separated, the finger's old right child `r` and the parent's payload `sibling`, are joined with it into the single payload `node r parent sibling`.

## Policies

The definitions are in `Structures/HeavyPath/Finger/History/Simulation/Definitions/Abstract.lean`. A policy turns the instruction lemmas into a program: for each source instruction, it emits a concrete list of physical instructions.

@decl HeavyPath.Finger.History.Simulation.ConfigValid HeavyPath.Finger.History.Simulation.Output HeavyPath.Finger.History.Simulation.Output.cost HeavyPath.Finger.History.Simulation.Policy

`ConfigValid weight c s` is [[HeavyPath.Finger.History.Valid]] at a source cursor `c`. When the focus is empty it is `False`: an empty focus is not a finger, and no instruction can be performed at it. An `Output` is a response: the new source cursor, the new state, and the emitted physical instructions. Its cost is their number, one per pointer instruction. A `Policy` is a function of the current source cursor, the current state and the next opcode only. It cannot see later instructions or requests, so a run of a policy is online by construction. It may return `none`.

@decl HeavyPath.Finger.History.Simulation.PolicyValid HeavyPath.Finger.History.Simulation.PolicyBounded HeavyPath.Finger.History.Simulation.PolicyWithin

These are three levels of contract:

- `PolicyValid weight p`: from any valid pair `(c, s)`, an illegal instruction is rejected (`none`). A legal one is answered by an output whose source cursor is the true successor `perform op c`, whose state is valid for it, whose instructions replay ([[Multifinger.replay]]) from the physical root to the new physical root, and whose cost satisfies $\text{cost} + \Phi' \le 62 + \Phi$.
- `PolicyBounded`: in addition, every response costs at most $34 + 24\log_2 n$.
- `PolicyWithin`: in addition, for every cut point of a response there is an intermediate pointer configuration `middle`, possibly with the cursor away from the root. The first `cut` instructions lead to `middle`, the remaining ones lead from `middle` to the final configuration, and every rank $x$ has depth at most $16\,\mathrm{depth}_0(x) + 96$ in `middle`. This is a certificate about the emitted program itself, not just about some trace with the same endpoints.

### One step

**Theorem (one step).** From a valid pair $(c, s)$ and a legal source instruction, there is a valid state for the successor cursor, reached from the physical root by a trace back to the physical root, of amortized cost at most $62$ and worst-case cost at most $34 + 24\log_2 n$. Along the trace the size is constant, and every depth stays at most $16$ times its old value plus $96$. Recording such a trace gives a response with all three properties. Hence policies of all three strengths exist.

@decl HeavyPath.Finger.History.Simulation.Results.step HeavyPath.Finger.History.Simulation.Results.step_bounded HeavyPath.Finger.History.Simulation.Results.step_within HeavyPath.Finger.History.Simulation.Results.response_exists_within

@decl HeavyPath.Finger.History.Simulation.Results.policy_exists HeavyPath.Finger.History.Simulation.Results.policy_bounded_exists HeavyPath.Finger.History.Simulation.Results.policy_within_exists

The `step` lemmas are a case analysis on the opcode, using the six lemmas of [Section 49.5](#the-six-instructions). `response_exists_within` turns the trace into an explicit instruction list with the prefix certificate. The policy behind `policy_within_exists` picks, by choice, one such response at each valid configuration and legal opcode, and returns `none` otherwise. Since `PolicyWithin` contains `PolicyBounded`, which contains `PolicyValid`, a single policy has all three properties. As elsewhere in the abstract online model, the policy's internal computation is not charged. Only emitted pointer instructions count.

## Running a policy

@decl HeavyPath.Finger.History.Simulation.sourceRun HeavyPath.Finger.History.Simulation.run

`sourceRun c ops` is the reference semantics of a source instruction stream: it applies [[LabelledCursor.perform]] in turn and fails at the first illegal instruction. `run p c s ops` answers the same stream with the policy, one instruction at a time. It concatenates the emitted programs, and it fails as soon as the policy does. The final state carries the remaining potential, and the output's cost is only the emitted instructions.

**Theorem (runs are online).** Running on `xs ++ ys` is running on `xs` and then continuing from the output on `ys`. If the run on `xs ++ ys` succeeds, then so does the run on `xs`, and its program is a prefix of the whole program.

@decl HeavyPath.Finger.History.Simulation.Results.run_append HeavyPath.Finger.History.Simulation.Results.run_prefix

These two facts need no validity assumption. They hold for any policy, because a policy never sees the future.

**Theorem (correct simulation).** Let $p$ satisfy `PolicyValid`, and let $(c, s)$ be valid. If a stream of $m$ source instructions is legal from $c$ and ends at $c'$, then the run succeeds and ends at $c'$ in a valid state. Its program replays from the physical root to the final physical root, and $\text{cost} + \Phi' \le 62m + \Phi$. The run fails exactly when the source stream is illegal.

@decl HeavyPath.Finger.History.Simulation.Results.run_spec HeavyPath.Finger.History.Simulation.Results.run_none_iff

**Theorem (initialized run).** For a valid policy and a source finger in a positively weighted tree $T$ with $n$ nodes, there is a starting state, reached from $T$ by a startup trace of cost $s_0$ with $s_0 + \Phi_0 \le 39n$. For every legal stream of $m$ instructions, the run from it ends at the right source cursor in a valid state. The startup and the run form a single pointer trace from $T$ of cost $s_0 + C$, and $s_0 + C + \Phi \le 39n + 62m$.

@decl HeavyPath.Finger.History.Simulation.Results.initialized_run

The starting state is chosen before the instruction stream, in the same `∃ … ∀` order as the statement. So one physical start serves every future stream.

**Theorem (between instructions).** In any valid configuration, the physical root holds the source finger's rank. The node of rank $i$ is at depth at most $15 + 15\log_2(W/w_i)$, and a round trip to it from the root costs $1 + 2k \le 31 + 30\log_2(W/w_i)$.

@decl HeavyPath.Finger.History.Simulation.Results.root_key HeavyPath.Finger.History.Simulation.Results.depth HeavyPath.Finger.History.Simulation.Results.search_walk

These restate [Section 49.3](#what-a-valid-state-guarantees) for a cursor `c`, with `c.tree` the whole source tree.

## Cheapest representations

The bound $\text{cost} + \Phi' \le 62m + \Phi$ charges the starting potential to the simulation. [[Deamortization.Weighted.Results.simulation]] instead bounds the cost by a multiple of $m$ alone, with no additive potential term. The tool is the cheapest representation of each source cursor. The definitions are in `Simulation/Minimum/Definitions/Abstract.lean`.

@decl HeavyPath.Finger.History.Simulation.Minimum.potential HeavyPath.Finger.History.Simulation.Minimum.excess

`potential weight c` is the least potential of any valid state for the source cursor `c`. It is an infimum over natural numbers, which is attained whenever some valid state exists. When none exists, for instance when the focus is empty, the infimum is $0$: a totalized value that the theorems never use. It depends on `c` and the weights only, not on the history that led to `c`. `excess weight c s` is the credit of `s` above that minimum.

**Theorem (minimum).** For a valid pair $(c, s)$: the minimum is at most $\Phi(s)$, it is attained by some valid state, and $\Phi(s)$ is the excess plus the minimum.

@decl HeavyPath.Finger.History.Simulation.Minimum.Results.potential_le HeavyPath.Finger.History.Simulation.Minimum.Results.attained HeavyPath.Finger.History.Simulation.Minimum.Results.excess_add

**Theorem (the minimum moves slowly).** Suppose a stream of $m$ source instructions leads from $c$ to $c'$ and $c'$ has a valid state. Then the minimum potential at $c$ is at most $186m$ plus the minimum at $c'$. Consequently, a run of a valid policy satisfies

$$\text{cost} + \mathrm{excess}(c', s') \;\le\; 248m + \mathrm{excess}(c, s).$$

@decl HeavyPath.Finger.History.Simulation.Minimum.Results.potential_drop HeavyPath.Finger.History.Simulation.Minimum.Results.run_excess

The first bound runs the simulation backwards. Every source instruction can be undone by at most three source instructions ([[Multifinger.Opcode.inverse]]), each of amortized cost $62$, and $3 \cdot 62 = 186$. Adding this to the forward bound of $62$ gives $248$. Starting from an `attained` minimum, the excess is $0$, so the run costs at most $248m$. This is the constant $248$ in [[Deamortization.Weighted.Results.simulation]].

## Interrupting a response

The theorems of this section, in `Simulation/Interruption/Abstract.lean`, bound the physical tree at an arbitrary cut point of the emitted program, as Theorem 6 requires. A cut point is a natural number `cut`: the configuration `middle` is reached by the first `cut` instructions, and the remaining instructions lead from `middle` to the end. Cuts beyond the end give the final configuration.

**Theorem (interrupted response, worst-case route).** For a bounded policy and a valid pair $(c, s)$, every cut of one response reaches a configuration in which the node of rank $i$ has depth at most

$$49 + 15\log_2 \frac{W}{w_i} + 24\log_2 n.$$

With unit weights this is $49 + 39\log_2 n$, at every cut of a single response and of a whole run.

@decl HeavyPath.Finger.History.Simulation.Interruption.Results.response HeavyPath.Finger.History.Simulation.Interruption.Results.response_uniform HeavyPath.Finger.History.Simulation.Interruption.Results.run_uniform_prefix

The argument is elementary. One pointer instruction changes any depth by at most one, a response has at most $34 + 24\log_2 n$ instructions, and the response starts from a valid state, where depths are at most $15 + 15\log_2(W/w_i)$. For a whole run, the cut falls inside one response, and that response starts from the valid state left by the previous ones. The bound is in terms of the *starting* tree `c.tree`: rotations change neither the total weight nor the inorder, so rank $i$ names the same label throughout. The deamortization with unit weights uses `run_uniform_prefix` (via `Deamortization.Finger`, [Chapter 37](deamortization.html)).

**Theorem (interrupted response, weighted).** For a policy with the `PolicyWithin` certificate, every cut of a response, and every cut of a whole run, reaches a configuration in which the node of rank $i$ has depth at most

$$336 + 240\log_2 \frac{W}{w_i}.$$

@decl HeavyPath.Finger.History.Simulation.Interruption.Results.response_weighted HeavyPath.Finger.History.Simulation.Interruption.Results.run_weighted_prefix

Here $336 = 16 \cdot 15 + 96$ and $240 = 16 \cdot 15$. The certificate's multiplicative form avoids the $\log_2 n$ term, which a weighted bound cannot afford: a heavy key must stay shallow even while a response deep in the tree is executed. This is the depth clause of [[Deamortization.Weighted.Results.simulation]].

**Theorem (detours).** With unit weights, at any cut of a run and for every key $x$, there is a navigation-only detour from the interrupted configuration to $x$ and back, of total length (plus one for the request) at most $197 + 156\log_2 n$. The detour is empty if the cursor is already on $x$. Inserting it at the cut leaves the program legal with the same final tree, and the tree does not change during the detour.

@decl HeavyPath.Finger.History.Simulation.Interruption.Results.run_detour

This is the paper's "access this element by moving the finger to it and back": go up to the root and down to $x$, then return, each leg bounded by the interrupted depth $49 + 39\log_2 n$. The interrupted cursor may be anywhere in the tree. The conclusion `middle.focus ≠ .nil` says that it is on a node, not on an empty subtree, so a detour can start there.

**Theorem (a search window).** Use unit weights. Suppose a source stream serves a request for rank `target` (in the sense of [[HeavyPath.Finger.History.Simulation.Requests.Serves]] below), and let `budget` be at least $49 + 39\log_2 n$. Then the run of the stream succeeds with the usual amortized bound, and the physical machine has a *window* for the request: a number `consumed` $\le$ `budget` of the run's instructions, and a walk from the physical root that visits `target` and ends exactly where those `consumed` instructions end. The walk has length at most $5 \cdot$ `consumed`, so at most $5 \cdot$ `budget`. Either the whole budget is consumed, or the cursor is on `target` after the consumed instructions.

@decl HeavyPath.Finger.History.Simulation.Interruption.Results.search_window

This is [[Deamortization.Window.Results.serve]] ([Chapter 37](deamortization.html)) specialized to this simulation, whose interruption depths satisfy that theorem's height hypothesis. A scheduler can answer every request within $1 + 5\cdot$`budget` physical instructions while making progress on the pending simulated work.

## Serving requests

So far the source has been a stream of instructions. A source BST *algorithm* turns requests into such streams. The definitions are in `Simulation/Requests/Definitions/Abstract.lean`.

@decl HeavyPath.Finger.History.Simulation.Requests.Serves

`Serves c ops key final` says that the source stream `ops` from cursor `c` visits the node of rank `key` at some instruction boundary and ends at `final`. The stream splits as `before ++ after`, the cursor after `before` is on `key`, and `after` is arbitrary further work. The source finger persists between requests: a search starts wherever the previous one ended, as in the paper's BST model, and `before` may be empty if the finger already is on the key.

@decl HeavyPath.Finger.History.Simulation.Requests.Algorithm HeavyPath.Finger.History.Simulation.Requests.Algorithm.correct HeavyPath.Finger.History.Simulation.Requests.Algorithm.runFrom

An `Algorithm` has a `step` that sees the past requests, the current source cursor and the next requested rank. It returns a source instruction stream and the resulting cursor. Its `correct` field requires, for a nonempty focus and an in-range rank, that the stream serve the request and end at the returned cursor. Correctness constrains legality and the visit, not the cost, and an algorithm may do arbitrary work after the visit. `runFrom past c keys` concatenates the streams over a request list and returns the final cursor. The source cost of a request sequence is the length of this concatenated stream. This is a persistent-finger counterpart of the online algorithms of [Chapter 5](online.html). [Chapter 37](deamortization.html) connects the two.

@decl HeavyPath.Finger.History.Simulation.Requests.run

`Requests.run p a past c s keys` lifts the policy request by request. For each key it runs the policy on the algorithm's stream for that key. No step sees a future key.

**Basic facts.** Erasing labels commutes with running: a labelled source stream is a legal pointer program on the unlabelled tree with the same result, so source costs are pointer-model costs. Algorithms exist, so the `correct` obligation is satisfiable. Both the source algorithm and the lifted run are compositional and prefix-preserving. A request-by-request run equals the instruction-by-instruction run on the concatenated stream, which is legal. Every valid state has potential at most $20n - 20$.

@decl HeavyPath.Finger.History.Simulation.Requests.Results.source_erase HeavyPath.Finger.History.Simulation.Requests.Results.algorithm_exists HeavyPath.Finger.History.Simulation.Requests.Results.source_requests_append HeavyPath.Finger.History.Simulation.Requests.Results.run_append HeavyPath.Finger.History.Simulation.Requests.Results.run_prefix HeavyPath.Finger.History.Simulation.Requests.Results.flatten HeavyPath.Finger.History.Simulation.Requests.Results.config_potential_bound

`flatten` is what lets the results for instruction runs apply to request runs: [[HeavyPath.Finger.History.Simulation.Minimum.Results.run_excess]] and [[HeavyPath.Finger.History.Simulation.Interruption.Results.run_weighted_prefix]] are both applied to the flattened run in the proof of [[Deamortization.Weighted.Results.simulation]].

**Theorem (one request).** For a valid policy and a valid pair $(c, s)$, if a source stream serves rank `key`, then the simulated run serves it on the pointer machine. In the sense of [[Pointer.Serves]], the physical program starts at the physical root, visits `key`, and ends in the final physical tree, at cost $1 + C$, where $C$ is the number of emitted instructions. The amortized bound $C + \Phi' \le 62m + \Phi$ holds, and the visit happens at a recorded cut of the emitted program.

@decl HeavyPath.Finger.History.Simulation.Requests.Results.serves HeavyPath.Finger.History.Simulation.Requests.Results.serves_recorded

The physical visit happens between two responses. When the source finger is on `key`, the physical root is the node of rank `key` ([[HeavyPath.Finger.History.Simulation.Results.root_key]]), so the visit needs no extra instructions. The recorded cut in `serves_recorded` is the visit hypothesis of [[Deamortization.Window.Results.serve]].

**Theorem (request sequences).** For a valid policy, any source algorithm, a valid pair $(c, s)$ and in-range requests, the lifted run succeeds and ends at the algorithm's final cursor in a valid state. It is a [[Pointer.Execution]] of the request list from the physical tree, of cost $|\text{keys}| + C$ (one unit per request plus the emitted instructions), and $C + \Phi' \le 62m + \Phi$, where $m$ is the algorithm's total source cost. Without any assumption on $\Phi$, the work on any window of requests is at most $62(|\text{keys}| + m) + 20n$.

@decl HeavyPath.Finger.History.Simulation.Requests.Results.run_spec HeavyPath.Finger.History.Simulation.Requests.Results.interval_work

`interval_work` combines `run_spec` with [[HeavyPath.Finger.History.Simulation.Requests.Results.config_potential_bound]]. It applies to any segment of a longer run, starting from whatever history the earlier requests left.

**Theorem (initialized request sequences).** For a valid policy and any source algorithm, starting from a source finger in a positively weighted tree $T$ with $n$ nodes, there is a starting state, reached from $T$ by a startup trace of cost $s_0$ with $s_0 + \Phi_0 \le 39n$, such that for every request history `past` and every list of in-range requests:

- the lifted run succeeds and ends at the algorithm's final cursor in a valid state;
- it is a pointer-machine execution of the requests from the starting physical tree at cost $|\text{keys}| + C$, and, for a nonempty request list, an execution from $T$ itself at cost $s_0 + |\text{keys}| + C$;
- $s_0 + |\text{keys}| + C + \Phi \le 39n + 62(|\text{keys}| + m)$, where $m$ is the algorithm's source cost.

@decl HeavyPath.Finger.History.Simulation.Requests.Results.initialized_run

The empty request list is excluded from the second execution because a [[Pointer.Execution]] of no requests has cost $0$ and cannot absorb a nonzero startup. Up to constants, this is Theorem 5's $|A'(S)| = O(|A(S)|)$ for every online source algorithm, with the startup made explicit. [[Deamortization.Weighted.Results.simulation]] replaces the start by a cheapest representation, as in [Section 49.8](#cheapest-representations), to get the purely multiplicative bound $C \le 248m$.
