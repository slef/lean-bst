# Recursive heavy paths

[Chapter 46](heavy-paths.html) stores one heavy path of a weighted tree as a pair of Chocolate pop-tarts. The endpoint of the path is the root, the path nodes smaller than the endpoint are in the left pop-tart, the larger ones in the right pop-tart, and every subtree hanging off the path is an opaque leaf of one of the two pop-tarts. This section applies the construction recursively: each of those opaque subtrees is itself stored by its own heavy path and its own pair of pop-tarts, and so on down to the leaves. This is the representation of Section 3 of Bose, Collette, Fagerberg and Langerman (2012), drawn in their Figure 4, and it is what gives the deamortized BSTs of [Chapter 37](deamortization.html) their logarithmic depth.

A Chocolate pop-tart keeps a leaf of weight $w$ at depth $O(\log(M/w))$, where $M$ is the total weight of the pop-tart ([Chapter 45](chocolate.html)). A key is reached by descending into one pop-tart per heavy path on its source path. Each light edge at least halves the weight, and the depths telescope into a single logarithm:

```headline recursive-heavy-paths-depth
title: Every key of a recursive heavy-path representation has logarithmic weighted depth
source: Bose, Collette, Fagerberg and Langerman, *De-amortizing binary search trees* (2012)
theorems: HeavyPath.Recursive.Results.rebuild_labels HeavyPath.Recursive.Results.rebuild_depth_at HeavyPath.Recursive.Results.rebuild_unit_depth HeavyPath.Recursive.History.Results.layout_depth_at HeavyPath.Recursive.Results.rebuild_initialization

Let $t$ be a labelled tree with $n$ nodes and positive node weights $w$, and let $W$ be its total weight. The canonical recursive representation `rebuild w t` is a tree shape with the same $n$ nodes. If $t$ is ordered, `rebuild w t` has exactly one ordered labelling with the inorder of $t$, so it is a BST on the same keys. Whether or not $t$ is ordered, the node of inorder rank $i$, whose label in $t$ is $x_i$, lies at depth

$$\mathrm{depth}(i) \;\le\; 7 + 15\log_2\frac{W}{w(x_i)} .$$

With unit weights this is $7 + 15\log_2 n$ for every rank $i < n$. The same bound holds in every *history layout*, that is, whatever valid stack shapes the pop-tarts of the representation have reached after pushes and pops. The pointer machine turns $t$ into `rebuild w t` in at most $16n$ instructions.

This is the depth part of the paper's Theorem 5, for a finger at the root, with explicit constants. Depth counts edges ([[Tree.depth]]), so the root has depth $0$. In Lean, `rebuild_labels` gives the unique ordered labelling, `rebuild_depth_at` and `rebuild_unit_depth` are the two depth bounds, `History.Results.layout_depth_at` is the bound for an arbitrary history layout ([[HeavyPath.Recursive.History.Layout]]), and `rebuild_initialization` is the setup trace.
```

::: note Do you need this section?
This section is proof machinery for the deamortization theorem of [Chapter 37](deamortization.html) and for the combined finger bound of [Chapter 38](combined-finger.html). No headline result of those chapters mentions a recursive layout in its statement. What they use is the depth bound above, and the cost of moving the source tree's root in and out of the representation. If you only want to know why the deamortized trees have depth $O(\log n)$, the headline and the overview below are enough. [Chapter 48](heavy-path-fingers.html) and [Chapter 49](finger-histories.html) build the simulation of a moving finger on top of the history layouts of this section.
:::

The definitions are in `Structures/HeavyPath/Recursive/Definitions/Abstract.lean` and its `Exposure`, `History` and `History/Interruption` subdirectories, and the theorems in the `Abstract.lean` files next to them.

## Overview

Fix a *source tree* $t$: a labelled tree with positive node weights. Its heavy-path decomposition ([Chapter 46](heavy-paths.html)) starts at the root and follows the heavier child at every node, with ties going left, until it reaches a leaf $x$, the *endpoint*. Every node of that path has a second child, possibly empty, the root of an off-path subtree, called a *payload*. The *physical tree* represents $t$ as follows:

```text
                 x                 the endpoint is the physical root
               /   \
       pop-tart     pop-tart       path nodes < x on the left, > x on the right;
      L(root, x)    R(root, x)     each pop-tart leaf is one payload, stored as
       /  |  \        /  |  \      a recursive representation of that payload
     [P1][P2]...    ...[P5][P6]
```

The separators of the left pop-tart are the path nodes smaller than $x$, and its leaves are the payloads between them, in key order. The right pop-tart is the mirror image. Each payload leaf is charged the weight of its subtree plus the weight of the separator next to it. The physical tree has exactly the nodes of $t$, in the same inorder. This section has four layers:

1. **The canonical layout** (`Recursive.Layout`, `rebuild`). Every pop-tart has the shape produced by pushing the path nodes in order, from the endpoint up. The layout is unique, and its depth bound is the telescoping argument of the paper.
2. **Exposure** (`Recursive.Exposure`). The finger of the source algorithm starts at the root of $t$. Moving it down to a child of the root removes that root from its heavy path. Physically, the root is popped from its pop-tart and becomes the physical root, with the two children of the source root as its physical children. The heavy child comes back as a residual pair of pop-tarts, and the light child as its canonical payload.
3. **Histories** (`Recursive.History`). After a few pops and pushes, the pop-tarts no longer have the canonical shapes, and the payloads inside them have their own histories. A history layout records, for every off-path occurrence, its actual physical shape and a *credit*, the potential stored in it. The depth bound survives, and exposing or joining a source root costs $O(1)$ amortized and $O(\log n)$ worst case.
4. **Interruption** (`Recursive.History.Interruption`). The deamortization interrupts the simulation between any two physical instructions. The last layer bounds the depth of every key in every *intermediate* tree of an exposure or a join.

| Paper (Section 3) | Here |
|---|---|
| heavy path from $y$ to $x$, pop-tarts $L(y,x)$, $R(y,x)$ (Figure 4) | [[HeavyPath.Paired.Stacks]] built by [[Stacks.buildWith]], [[HeavyPath.Recursive.rootPair\|rootPair]] |
| "the subtrees contained in those leaves will be structured in the same manner, recursively" | [[HeavyPath.Recursive.Layout\|Layout]], [[HeavyPath.Recursive.rebuild\|rebuild]] |
| depth of $x$ is a telescoping sum $O(\log(W/w))$ | [[HeavyPath.Recursive.Results.depth_telescope\|depth_telescope]], [[HeavyPath.Recursive.Results.rebuild_depth\|rebuild_depth]] |
| $y$ moves down the path (finger moves down from the root) | [[HeavyPath.Recursive.Exposure.Results.expose_view\|expose_view]], [[HeavyPath.Recursive.History.Results.layout_expose\|layout_expose]] |
| $y$ moves up the path | [[HeavyPath.Recursive.History.Results.layout_join\|layout_join]] |
| pop-tarts in arbitrary reachable states, amortized by their potential | [[HeavyPath.Recursive.History.Layout\|History.Layout]] |

The finger in general position, Figure 5 of the paper, with the path from the root to the finger stored upside down, is the subject of [Chapter 48](heavy-path-fingers.html) and [Chapter 49](finger-histories.html). They reuse the history layouts of this section for every subtree that the finger is not in.

## The canonical layout

### Inorder bookkeeping

The heavy path of $t$ is described by the cursor [[HeavyPath.extract]]` w t`: its focus is the endpoint, and its context is a list of [[LabelledCursor.Frame]]s from the endpoint up to the root. A frame `.left x r` says that the path went left at `x` and that `r` is the payload; `.right l x` is the mirror case. The first four definitions say where each frame's nodes appear in the inorder of $t$.

@decl HeavyPath.Recursive.lowerFrames HeavyPath.Recursive.upperFrames HeavyPath.Recursive.lowerBlock HeavyPath.Recursive.upperBlock

`lowerFrames cs` keeps the `.right` frames, whose separators are smaller than the endpoint, and reverses them so that they appear root first, in increasing key order. `upperFrames cs` keeps the `.left` frames in endpoint-first order, which is again increasing key order. A lower frame contributes its payload followed by its separator (`lowerBlock`), and an upper frame its separator followed by its payload (`upperBlock`). The cursor's inorder is the concatenation of these blocks around the focus:

@decl HeavyPath.Recursive.Results.context_inorder

Here [[LabelledCursor.plug]]` cs t` rebuilds the tree from the context. The statement holds for every context, heavy or not.

@decl HeavyPath.Recursive.RanksSatisfy

`RanksSatisfy P offset xs` says that `P (offset + i) x` holds for every occurrence `x` at position `i` of `xs`. It speaks of occurrences, not of values, so it remains meaningful when labels repeat. It is used in the proofs of the depth bounds below, which never assume distinct or ordered labels.

### Building the representation

@decl HeavyPath.Recursive.rebuildFuel HeavyPath.Recursive.rebuild HeavyPath.Recursive.rootPair

`rebuildFuel w n t` extracts the heavy path of `t` and builds its pair of pop-tarts with [[Stacks.buildWith]], which pushes the frames of the context one after the other, starting from the frame next to the endpoint. The payload of each frame is replaced by its own recursive representation `rebuildFuel w n'` before being pushed as an opaque leaf. The pop-tart charges, though, are computed from the original labelled payloads: the leaf of frame `.left x r` is charged $w(x) + W(r)$, where $W$ is [[HeavyPath.mass]]. The fuel `n` only makes the recursion structural. With fuel at least the number of nodes, every recursive call on a nonempty tree takes the paired branch (`rebuildFuel_eq`). The fallback `t.erase`, which leaves a subtree unchanged, is reached only when fuel runs out, or when the endpoint is not a leaf, which positive weights rule out. `rebuild w t` uses fuel `t.erase.size`. `rootPair w t` is the outermost pair, the one whose `tree` is `rebuild w t` when `t` is nonempty (`rootPair_source`).

The pop-tart pair [[HeavyPath.Paired.Stacks]] has a `lower` and an `upper` Chocolate layer. Its physical tree is `.node lower upper.mirror`: the endpoint is the root, and the upper stack is stored in mirrored coordinates. The pairs and their pushes are defined in [Chapter 46](heavy-paths.html), and the Chocolate layers in [Chapter 45](chocolate.html).

The canonical layout is also given as an inductive relation, which is the form the proofs use:

@decl HeavyPath.Recursive.Layout

`Layout w t shape` holds when `t` is empty and `shape` is empty, or when `t` is nonempty with positive weights, its heavy path ends at a leaf, `shape` is the tree of the pair built by `buildWith w payload` from its context, and every payload occurrence `framePayload frame` has a full layout `payload (framePayload frame)`. The function `payload` matters only at the payload occurrences of the path. No depth estimate is part of the definition: depth is a theorem.

### Basic facts

The recursion is well founded because every payload is strictly smaller than the tree, and positivity is inherited by the payloads:

@decl HeavyPath.Recursive.Results.extract_payload_size HeavyPath.Recursive.Results.extract_payload_positive

`rebuild` produces a layout, the layout is unique, and the fuel has no effect once it is large enough:

@decl HeavyPath.Recursive.Results.rebuildFuel_layout HeavyPath.Recursive.Results.rebuild_layout HeavyPath.Recursive.Results.layout_unique HeavyPath.Recursive.Results.rebuildFuel_eq

`layout_unique` says that two layouts of the same labelled tree are the same shape. Together with `rebuild_layout`, every `Layout w t shape` has `shape = rebuild w t`. The recursion can be unfolded one level, either for an arbitrary layout or for `rebuild` itself:

@decl HeavyPath.Recursive.Results.layout_unfold HeavyPath.Recursive.Results.rebuild_eq HeavyPath.Recursive.Results.rebuild_pair HeavyPath.Recursive.Results.rootPair_source

In both cases the outer pair is valid in the sense of Chocolate pop-tarts, and the endpoint's weight plus the pair's mass is the mass of $t$: the frame charges partition the weights of $t$. `rebuild_pair` also gives the two fringes, that is, the leaves of each pop-tart from left to right with their charges. The lower fringe lists the lower payloads root first, and ends with an empty slot `(.nil, 0)` next to the endpoint, which stands for the endpoint's empty left child. The upper fringe, read in physical orientation, starts with the endpoint's empty right child and lists the upper payloads. `rootPair_source` says the same with the weaker `≤` on the mass.

The representation keeps the nodes, the inorder and the root key:

@decl HeavyPath.Recursive.Results.layout_size HeavyPath.Recursive.Results.rebuild_size HeavyPath.Recursive.Results.rebuild_labels HeavyPath.Recursive.Results.rebuild_root_key

[[Tree]] shapes carry no labels, so `rebuild_labels` states the inorder property by relabelling. If `t` is ordered ([[LabelledTree.Ordered]]), there is exactly one ordered labelled tree whose shape is `rebuild w t` and whose inorder is that of `t`. `rebuild_root_key` says that the physical root has the inorder rank of the endpoint of the outer heavy path.

Building the representation from scratch is cheap:

@decl HeavyPath.Recursive.Results.rebuild_initialization

::: check
- The bound $16n$ does not come from the pushes. It is the library's generic reshaping theorem, `Pointer.reshape`, which transforms any tree into any other tree of the same size with at most $16n$ pointer instructions. Any target shape on the same nodes would have the same bound.
- The trace starts and ends with the cursor at the root (context `[]`), and it counts every move and every rotation, as [[Pointer.Trace]] does.
:::

## The depth bound

The paper's argument has two ingredients. A light edge at least halves the weight, and a Chocolate pop-tart puts a leaf of charge $c$ at depth at most $7 + 7\log_2(M/c)$ inside a pop-tart of mass $M$ ([Chapter 45](chocolate.html)). One more edge, from the endpoint to the pop-tart, gives $8 + 7\log_2(M/c)$.

@decl HeavyPath.Recursive.Results.extract_payload_half HeavyPath.Recursive.Results.extract_charge_bounds

`extract_payload_half` is the halving: every payload of the heavy path has at most half the mass of $t$. This holds even far down the path, since the payload's sibling, the next path node, is at least as heavy. `extract_charge_bounds` relates a frame's charge [[HeavyPath.frameMass]] to the two things it pays for: the separator [[HeavyPath.frameKey]] has positive weight at most the charge, and so does the payload's mass. These bridge the pop-tart weights, which are charges, with the node weights, which appear in the final bound.

The telescoping step is a statement about real numbers:

@decl HeavyPath.Recursive.Results.depth_telescope

Let the whole tree have mass $W$, a payload have mass $C$ with $2C \le W$, and a key in it have weight $k \le C$. If the key's depth $d$ is at most the depth of the payload in the outer pair, $8 + 7\log_2(W/C)$, plus the inductive bound inside the payload, $7 + 15\log_2(C/k)$, then $d \le 7 + 15\log_2(W/k)$. Since $\log_2(W/C) \ge 1$, the additive $8$ is absorbed into $8\log_2(W/C)$, and $7 + 8 = 15$. This is how a constant per light edge disappears into the logarithm. It is also why the coefficient $15$ is roughly twice the pop-tart's $7$.

The three induction steps apply this to the three kinds of nodes found below the endpoint: a key inside a payload, the separator following a lower payload, and the separator preceding an upper payload.

@decl HeavyPath.Recursive.Results.payload_depth_step HeavyPath.Recursive.Results.successor_depth_step HeavyPath.Recursive.Results.predecessor_depth_step

The hypothesis `slot` locates the payload's physical occurrence inside the outer pair: [[PopTart.WeightedTree.LocatedSlot]] records its inorder offset and its edge depth. `payload_depth_step` lifts a bound for rank `x` inside the payload to rank `offset + x` in the whole representation. `successor_depth_step` bounds the rank right after a lower payload, which is the frame's separator (`lowerBlock` is the payload followed by its key). `predecessor_depth_step` bounds the rank right before an upper payload. The separators get the bound for their own weight, without induction. The endpoint is the root, at depth $0$.

Strong induction on the size of $t$ then covers every rank:

**Theorem (depth of the canonical layout).** Let $t$ have positive weights and total weight $W$. Every occurrence of a label $x$ in the inorder of $t$, at position $i$, is at depth at most $7 + 15\log_2(W/w(x))$ in `rebuild w t`. With unit weights, every rank $i < n$ is at depth at most $7 + 15\log_2 n$.

@decl HeavyPath.Recursive.Results.rebuild_depth HeavyPath.Recursive.Results.rebuild_depth_at HeavyPath.Recursive.Results.rebuild_unit_depth

The three forms say the same thing. `rebuild_depth` names the occurrence by a split `t.inorder = before ++ key :: after`, so its rank is `before.length`. `rebuild_depth_at` indexes by a rank in `Fin t.inorder.length`. `rebuild_unit_depth` specializes to unit weights, where $W = n$ and $w(x) = 1$. It needs no positivity hypothesis, since unit weights are positive.

A depth bound gives a search walk. Visiting rank $i$ and returning to the root costs one unit for the request plus two walks of $\mathrm{depth}(i)$ moves:

@decl HeavyPath.Recursive.Results.rebuild_search_walk

The constants are doubled, $15 + 30\log_2(W/w)$, because both walks are counted. The walk does not change the tree, and it does not simulate any work of the source algorithm. It is only a sanity check that the depth bound is reachable with pointer moves.

## Exposing the root of the source tree

The source algorithm's finger starts every request at the root of $t$. When it moves down to a child, the source root leaves the heavy path it was the top of. Physically, it is popped from its pop-tart. One rotation sequence then makes it the physical root, with a representation of each child of the source root as its physical children. The heavy child keeps a *residual* pair, the old pair with one fewer path node. The light child is a payload, already a separate subtree in canonical form.

@decl HeavyPath.Recursive.Exposure.View HeavyPath.Recursive.Exposure.View.leftTree HeavyPath.Recursive.Exposure.View.rightTree HeavyPath.Recursive.Exposure.View.potential HeavyPath.Recursive.Exposure.View.Valid

A `View` is what one finds below the source root `node l x r` after exposure. In `.leaf` both children are empty. In `.left rest` the heavy child is `l`, it is represented by the residual pair `rest`, and the right child is the canonical `rebuild w r`. `.right rest` is the mirror case. `leftTree` and `rightTree` are the two physical subtrees, and `potential` is the potential of the residual pair, which is all the potential that remains. `Valid` says that the case matches the heavy choice of [[HeavyPath.LeftHeavy]], that the heavy child is nonempty, and that `rest` [[Stacks.Represents]] the heavy child's own path with canonical payloads.

Representation is weaker than equality with a canonical pair. `Represents` asks only for valid Chocolate stacks with the correct fringes: popping need not recover the shape that the pushes would have built. The canonical pair represents its path, and any pair that represents the path of $t$ has the size of $t$:

@decl HeavyPath.Recursive.Exposure.Results.rootPair_represents HeavyPath.Recursive.Exposure.Results.represented_size

**Theorem (root exposure).** Let `node l x r` have positive weights, with canonical representation $P$ of potential $\Phi(P)$. There is a pointer trace, from root to root, that turns $P$ into `node a b` with `a` and `b` representing `l` and `r`. Its cost $c$ satisfies $c + \Phi' \le 24 + \Phi(P)$, where $\Phi'$ is the potential of the residual pair, and the new root has the rank of $x$.

@decl HeavyPath.Recursive.Exposure.Results.expose_left HeavyPath.Recursive.Exposure.Results.expose_right HeavyPath.Recursive.Exposure.Results.expose_view HeavyPath.Recursive.Exposure.Results.expose_pair_view HeavyPath.Recursive.Exposure.Results.root_exposure

`expose_left` and `expose_right` are the two cases. The cost is [[Stacks.exposeCost]]: one pop from the stack that holds $x$, plus four instructions to enter the stack, return and rotate. The mass identity says that the charge removed from the pair is exactly the frame charge of $x$. `expose_view` packages both cases, and the leaf case, as a `View`. `expose_pair_view` starts from any pair that represents the path, not only the canonical one. It is the form used by the finger simulation of [Chapter 48](heavy-path-fingers.html). `root_exposure` forgets the structure, keeping the sizes, the root rank and the amortized cost.

The constant $24$ is an amortized bound: the cost is paid by a drop of the Chocolate potential ([[PopTart.Chocolate.Layer.potential]]). The heavy child's residual pair is a represented pair, not a canonical one, so a second exposure cannot simply apply `expose_view` again. This is why histories are needed.

## Histories

### Entries and paths

A history layout drops the requirement that payloads are canonical. Each off-path occurrence is recorded with its actual physical shape and its own stored potential.

@decl HeavyPath.Recursive.History.Entry HeavyPath.Recursive.History.Entry.slot HeavyPath.Recursive.History.Entry.lowerBlock HeavyPath.Recursive.History.Entry.upperBlock HeavyPath.Recursive.History.Entry.wrap

An `Entry` has the source frame, the physical `shape` of its payload, and the `credit` of that payload. Two equal source subtrees at different positions may have different shapes and credits, since they have had different histories. `slot` is the pop-tart leaf it occupies: the shape with the frame's charge. `lowerBlock` and `upperBlock` are the inorder blocks of the source frame. `wrap e child` puts the separator back above the rest of the path: for a `.left` frame it is `node child e.shape`, the separator node with the path below it on the left and the payload on the right.

@decl HeavyPath.Recursive.History.lower HeavyPath.Recursive.History.upper

`lower` and `upper` select the entries of each pop-tart in physical key order, exactly as `lowerFrames` and `upperFrames` do for frames.

@decl HeavyPath.Recursive.History.PathValid HeavyPath.Recursive.History.PathValid.pair HeavyPath.Recursive.History.PathValid.lower HeavyPath.Recursive.History.PathValid.upper

`PathValid w es p` says that the pair `p` is valid and that its two fringes, read in physical orientation, are the slots of the entries, with the endpoint's empty slot at the inner end. This is a condition on the current state only. It does not say how the pair was built, and it does not assume a height bound. The pair's mass is the sum of the frame charges, and with the endpoint's weight it is the mass of the source tree:

@decl HeavyPath.Recursive.History.Results.path_mass HeavyPath.Recursive.History.Results.path_partition

### History layouts

@decl HeavyPath.Recursive.History.Layout

`Layout w t shape credit` is the recursive invariant. The empty tree has the empty shape and credit $0$. A nonempty tree with positive weights is represented by any pair `p` with entries `es` whose sources are the context of its heavy path, such that `PathValid w es p` holds and every entry's shape is itself a layout of its payload with the entry's credit. The credit of the whole is the potential of `p` plus the credits of all entries. Summed over the recursion, it is the total Chocolate potential of all the pop-tarts of the representation, and it is the potential function of the amortized analysis.

A history layout has the expected size, positivity and labels:

@decl HeavyPath.Recursive.History.Results.layout_positive HeavyPath.Recursive.History.Results.layout_size HeavyPath.Recursive.History.Results.layout_labels

The canonical layout is a history layout, with credit at most $23n$, and every history layout has credit at most $20n$:

@decl HeavyPath.Recursive.History.Results.of_canonical HeavyPath.Recursive.History.Results.rebuild_history HeavyPath.Recursive.History.Results.of_canonical_bounded HeavyPath.Recursive.History.Results.rebuild_history_bounded HeavyPath.Recursive.History.Results.path_potential_bound HeavyPath.Recursive.History.Results.layout_potential_bound

`path_potential_bound` bounds one pair by $20$ per entry. `layout_potential_bound` adds this over the recursion. A source tree with $n$ nodes has fewer than $n$ entries in total, so its credit is at most $20n$. The $23n$ of the two `_bounded` theorems is therefore not the best constant: `layout_potential_bound` applied to `rebuild_history` gives $20n$. Either bound means that starting from a fresh canonical layout costs at most a linear amount of potential.

The depth bound and the search walk carry over unchanged, with the same constants:

@decl HeavyPath.Recursive.History.Results.layout_depth HeavyPath.Recursive.History.Results.layout_depth_at HeavyPath.Recursive.History.Results.layout_search_walk

The reason is that the depth argument only used two facts about each pair: valid Chocolate stacks, and the payload charges in the fringe. Both are part of `PathValid`. The shapes the stacks happen to have, and the history of the payloads, do not matter.

### Popping, exposing and joining

One pop removes the topmost source ancestor of a path, the last entry of `es`, and makes it the physical root above the rest of the path:

@decl HeavyPath.Recursive.History.Results.pop_path

Exposing a source root for an arbitrary history layout is the same operation, followed by the observation that the residual pair and the light payload are again history layouts. Joining is the converse: given layouts of `l` and `r` and a positive weight for `x`, it builds a layout of `node l x r`, pushing the light child into the heavy child's pair.

**Theorem (exposing and joining).** Let `shape` be a history layout of `node l x r` with credit $\Phi$. A root-to-root trace of cost $c$ turns it into `node a b`, where `a` and `b` are history layouts of `l` and `r` with credits $\Phi_l$ and $\Phi_r$, with $c + \Phi_l + \Phi_r \le 24 + \Phi$ and $c \le 10 + 10\log_2 n$. Conversely, from layouts `a`, `b` of `l`, `r`, a trace of cost $c \le 10 + 14\log_2 n$ produces a layout of `node l x r` with credit $\Phi$ and $c + \Phi \le 24 + \Phi_l + \Phi_r$.

@decl HeavyPath.Recursive.History.Results.layout_expose HeavyPath.Recursive.History.Results.layout_join HeavyPath.Recursive.History.Results.layout_expose_bounded HeavyPath.Recursive.History.Results.layout_join_bounded

The amortized bound $24$ is the Chocolate pop-tart's. The worst-case bounds come from the depth of the stack being popped or pushed into. Here $n$ is the size of the physical tree, `shape.size` or `(node a b).size`. Only the outer pair changes: every payload keeps its shape and its credit.

The deamortization also needs to know that no intermediate tree is deep. [[Pointer.TraceWithin]]` holds` is a trace whose tree satisfies `holds` at every instruction boundary.

@decl HeavyPath.Recursive.History.Results.push_path_within HeavyPath.Recursive.History.Results.pop_path_within HeavyPath.Recursive.History.Results.layout_expose_within HeavyPath.Recursive.History.Results.layout_join_within

In every intermediate tree of a pop or an exposure, the size is unchanged and every rank $y$ is at depth at most $4\,\mathrm{depth}_{\text{start}}(y) + 10$. For a push or a join, the constant is $16$, measured against the tree before the push. A pop-tart push or pop restructures only a few nodes on the stack's spine, so it can at most multiply depths by a constant. The `_within` versions imply the plain ones, which are kept as projections. [Chapter 49](finger-histories.html) uses `layout_join_within` for the finger's moves and rotations.

## Interruption

The deamortization of [Chapter 37](deamortization.html) runs the simulation as a stream of single-finger instructions and may cut that stream between any two instructions to serve the next request with a fresh search; in the proof of the paper's Theorem 6 this happens every $c\log n$ instructions. That search runs in the intermediate tree, possibly in the middle of an exposure or a join. The last module states the exposure and the join as explicit instruction lists, a list of [[Multifinger.Opcode]]s replayed by [[Multifinger.replay]] on the pointer configuration, and bounds the depth of every key in every intermediate configuration.

The starting tree of a join, a source root above two layouts, already has a weighted depth bound with respect to the whole source subtree:

@decl HeavyPath.Recursive.History.Interruption.Results.node_depth_at

**Theorem (interruptible exposure and join).** Let $W$ be the mass of `node l key r` and $n$ the size of the physical tree before the operation. Exposure and join can be written as instruction lists with the amortized and worst-case costs above, such that, for every cut point, the instructions before the cut replay to an intermediate configuration, the remaining ones replay from there to the result, and in that intermediate tree every rank $i$, with label $x_i$, has depth at most

$$17 + 15\log_2\frac{W}{w(x_i)} + 10\log_2 n \quad\text{(exposure)}, \qquad 17 + 15\log_2\frac{W}{w(x_i)} + 14\log_2 n \quad\text{(join)}.$$

Purely weighted versions give $38 + 60\log_2(W/w(x_i))$ for exposure and $48 + 60\log_2(W/w(x_i))$ for join. With unit weights, the bounds are $17 + 25\log_2 n$ and $17 + 29\log_2 n$.

@decl HeavyPath.Recursive.History.Interruption.Results.expose HeavyPath.Recursive.History.Interruption.Results.join

The mixed bounds of `expose` and `join` combine the depth of a complete layout with the length of the operation. During an exposure, a key's depth is at most its depth in the starting layout plus the number of instructions performed so far. A join is bounded backwards from its final layout across the remaining suffix.

@decl HeavyPath.Recursive.History.Interruption.Results.expose_uniform HeavyPath.Recursive.History.Interruption.Results.join_uniform HeavyPath.Recursive.History.Interruption.Results.expose_weighted HeavyPath.Recursive.History.Interruption.Results.join_weighted

The weighted versions instead use the multiplicative bounds of the `_within` theorems: $4(7 + 15L) + 10 = 38 + 60L$ for exposure, and, from `node_depth_at`, $4(8 + 15L) + 16 = 48 + 60L$ for join, where $L = \log_2(W/w(x_i))$. Only these have no dependence on $n$.

::: check
- In all four theorems the cut is an arbitrary natural number. A cut beyond the end of the list gives the final configuration.
- The depth bound covers every rank of the source subtree `node l key r`, in the physical tree `middle.tree` of the intermediate configuration, wherever its cursor is.
- These theorems are a self-contained statement about one exposure or join of a source root. The deamortized simulation of [Chapter 37](deamortization.html) does not cite them directly: it goes through the finger simulation of [Chapter 49](finger-histories.html), which proves its own interruption bound, $336 + 240\log_2(W/w)$, from the `_within` theorems of this section.
:::
