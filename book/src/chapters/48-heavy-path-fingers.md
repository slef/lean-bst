# Fingers on heavy paths

The deamortization of [Chapter 37](deamortization.html) runs a *source* algorithm inside a tree of logarithmic depth. The source works in the BST model of Bose, Collette, Fagerberg and Langerman: it has one persistent finger, which it moves to a parent or a child, or rotates over its parent, at unit cost per operation. In the library the source finger is a labelled cursor ([[LabelledCursor.Config]], operated by [[LabelledCursor.perform]]; see [Chapter 12](replay.html)). The simulating structure is a pointer machine in the sense of [Chapter 6](pointer.html). Its cursor returns to the root, and every operation of the source must become a short pointer trace from the root back to the root.

Section 3 of the paper does this with heavy paths stored in pop-tarts. When the source finger is at the root of its tree, every heavy path is a pair of pop-tarts hung below the path's endpoint. That is the representation of [Chapter 46](heavy-paths.html), applied recursively in [Chapter 47](recursive-heavy-paths.html). When the finger $f$ is elsewhere, the paper stores the path from the root $r$ down to $f$ *upside down*, as a second kind of pair of pop-tarts, with $f$ at the physical root (Figure 5 of the paper). This chapter formalizes that inverted pair. It covers three things:

- **Building.** A finger pair can be built from any source cursor. The setup costs a linear number of pointer instructions, and every node lies at logarithmic weighted depth.
- **Population.** Stack operations inside the pair cost $O(\log n)$ in the worst case, where $n$ is the number of nodes.
- **Transfer.** Moving the source finger down to a child moves one node from one stack to the other, at constant amortized cost and $O(\log n)$ worst-case cost.

[Chapter 49](finger-histories.html) completes the picture. It wraps the pair in a state that also records the recursive layouts of all off-path subtrees, adds the upward moves and the rotations, and assembles the simulation that [Chapter 37](deamortization.html) schedules.

```headline heavy-path-fingers-build
title: A finger pair built from any cursor has linear setup and logarithmic weighted depth
source: Bose, Collette, Fagerberg and Langerman, *De-amortizing binary search trees* (2012)
theorems: HeavyPath.Finger.Results.build_initialization HeavyPath.Finger.Results.build_labels HeavyPath.Finger.Results.build_root_key HeavyPath.Finger.Results.build_depth
skip: instDecidableEqLabelledTree | The derived decidable-equality instance for labelled trees only decides the test `l = .nil` inside [[HeavyPath.extract]]. Any two instances for the same proposition agree, so it cannot change the extracted path or the built pair.

Let $t$ be a labelled tree with $n$ nodes and a cursor at one of its nodes, the finger $f$. The cursor's path to the root is arbitrary; it need not be heavy. Give every node $x$ a weight $w(x) > 0$, and let $W$ be the total weight. Build the finger pair of this cursor with [[HeavyPath.Finger.build]]. Then:

1. **Setup.** Starting with the pointer at the root of $t$, at most $16n$ pointer instructions turn $t$ into the pair's tree, and end with the pointer at its root.
2. **Same keys.** If $t$ is a BST, the pair's tree carries exactly one labelling with the inorder of $t$, and that labelling is a BST.
3. **Finger at the root.** The root of the pair's tree has the rank of $f$ in $t$.
4. **Weighted depth.** The node of $t$ at inorder rank $i$, with weight $w_i$, has depth at most $15 + 15\log_2(W/w_i)$ in the pair's tree.

This is the depth claim of the paper's Theorem 5 at a single moment, for a finger in general position, with explicit constants. The bound holds for the pair as built; that it survives the source's operations is the subject of [Chapter 49](finger-histories.html).
```

::: note Do you need this chapter?
No headline result of the deamortization mentions a finger pair. The definitions here lie on the proof path of the transformation in [Chapter 37](deamortization.html): the bounded-depth simulation [[Deamortization.Weighted.Results.simulation]] runs on the finger states of [Chapter 49](finger-histories.html), and those states consist of one finger pair plus recursive payloads. Read this chapter to see how the source finger is kept at the physical root, where the setup cost $16n$ and the depth constants come from, and why a downward move has constant amortized cost. A reader who only wants to check Theorem 6 can skip it.
:::

## Overview

### The inverted path

Let the finger $f$ be at depth $k$ in the source tree. Its ancestors split into two monotone sequences. The *lower* ancestors are smaller than $f$, and they increase on the way down. The *upper* ancestors are larger than $f$, and they decrease on the way down. Each ancestor contributes its key, a *separator*, and the subtree that hangs off the path at that ancestor, a *payload*. The two children of $f$ are payloads too. In inorder the source tree reads

$$\ell_1\; x_1\; \ell_2\; x_2 \cdots \ell_j\; x_j\;\; L\;\; f\;\; R\;\; y_i\; r_i \cdots y_2\; r_2\; y_1\; r_1,$$

where $x_1 < \dots < x_j$ are the lower ancestors from the root down, $\ell_1, \dots, \ell_j$ their left subtrees, $y_1 > \dots > y_i$ the upper ancestors from the root down, $r_1, \dots, r_i$ their right subtrees, and $L$ and $R$ the subtrees of $f$.

A finger pair stores the left half in one Chocolate pop-tart and the right half in another, and puts $f$ between them:

```
                         f                    (physical root)
               /                   \
      mirrored lower pop-tart     upper pop-tart
      slots  l1 l2 ... lj L       slots  R ri ... r2 r1
      separators x1 ... xj        separators yi ... y1
      top slot: L (next to f)     top slot: R (next to f)
```

The payloads are the pop-tarts' fringe slots ([Chapter 44](pop-tarts.html)), and the ancestors are their internal nodes. The *top* of each stack, the slot most recently pushed, is the payload next to $f$ in inorder: $L$ on the lower side and $R$ on the upper side. The bottom slots, $\ell_1$ and $r_1$, belong to the ancestors nearest the source root. A Chocolate pop-tart pushes new nodes on the smaller side of its stack, which suits the upper ancestors directly. The lower stack is stored in mirrored coordinates and reflected when it is decoded. The heavy-path pair of [Chapter 46](heavy-paths.html) uses the opposite orientations. There the endpoint of a downward path is the physical root and the stacks grow at their outer ends, where the top of the path is. Here they grow next to the finger.

Inside each payload, the source subtree is represented recursively by the heavy-path pairs of [Chapter 47](recursive-heavy-paths.html). The finger pair is the one place where a path is stored upside down. The structure is *weighted*: a slot of weight $w$ in a pop-tart of total weight $M$ sits at depth $O(\log(M/w))$. This is the paper's Lemma 4, [[PopTart.Chocolate.Results.weighted_depth]] in [Chapter 45](chocolate.html). Telescoping it through the nested payloads gives the depth bound of the headline.

### Charges

A pop-tart weighs only its fringe slots; its internal nodes have no weight. (The paper's pop-tarts give internal nodes unit weight by convention, and its weighted simulation does not spell out where the weights of path nodes go.) The library charges each ancestor's weight to the adjacent payload on the side of the finger. With weights $w$ and $\mathrm{mass}$ the total weight of a subtree, the lower slots carry

$$\mathrm{mass}(\ell_1),\quad w(x_1) + \mathrm{mass}(\ell_2),\quad \dots,\quad w(x_j) + \mathrm{mass}(L),$$

and symmetrically on the upper side. The two stacks together therefore weigh $W - w(f)$. Only the finger's own weight is outside them. A separator sits next to the slot that carries its weight, so the depth bound for slots also bounds separators.

### Moves and costs

A move of the source finger to a child transfers one node. When the finger moves to its left child $c$, the payload $L$ must first have $c$ at its physical root. Then two or four instructions rotate $c$ above $f$, and $f$ becomes a separator of the upper stack, with the right subtree of $c$ as its new top slot. That is one Chocolate push. The lower stack keeps its shape, and its top slot shrinks from $L$ to the left subtree of $c$. The paper describes a move as "one push and one pop". In the library a downward move is a push and a replacement of the top payload. Upward moves pop, and they are in [Chapter 49](finger-histories.html).

All costs are counted as pointer instructions ([[Pointer.Trace]]) from the root configuration $\langle t, []\rangle$ to the root configuration of the result, and $N$ below is the number of nodes in the pair's tree (equal to $n$).

| operation | bound | lemma |
|---|---|---|
| build from the source tree | at most $16n$ instructions | `build_initialization` |
| depth of a node of weight $w$ in a fresh pair | at most $15 + 15\log_2(W/w)$ | `build_depth` |
| push onto either stack | at most $6 + 14\log_2 N$ | `lower_push`, `upper_push` |
| pop from either stack | at most $6 + 10\log_2 N$ | `lower_pop`, `upper_pop` |
| move down, child already exposed | amortized at most $26$ | `downLeft_amortized` |
| move down, given an exposure of cost $e$ | amortized at most $e + 30$; actual at most $e + \text{push} + 10$ | `downLeft_exposed_bounded` |
| move down into a recursive payload | amortized at most $54$, the payload's potential included | `downLeft_pair`, `downLeft_recursive`, `downLeft_source` |
| same, arbitrary layout histories | amortized at most $54$; actual at most $26 + 24\log_2 N$; intermediate depths at most $16d + 64$ | `Transfer.History.Results.downLeft_within` |

Each `downLeft` lemma has a `downRight` mirror image with the same constants.

## The finger pair

@decl RotationBST.HeavyPath.Finger.Pair RotationBST.HeavyPath.Finger.Pair.tree RotationBST.HeavyPath.Finger.Pair.mass RotationBST.HeavyPath.Finger.Pair.Valid

A `Pair` is two Chocolate stacks ([[PopTart.Chocolate.Layer]], [Chapter 45](chocolate.html)). Its physical tree is a root node, the finger, whose left subtree is the decoded `lower` stack mirrored ([[Tree.mirror]]) and whose right subtree is the decoded `upper` stack. The finger node carries no data of its own. Its key is determined by its position, as for every node of an unlabelled [[RotationBST.Tree]]. The `mass` is the total weight of the fringe slots of both stacks, excluding the finger. `Valid` asks only that both stacks satisfy the Chocolate invariant at level $0$. It says nothing about which source cursor the pair represents. That correspondence is stated by the fringe equations of the build theorems below, and maintained by the state invariant [[HeavyPath.Finger.History.Valid]] of [Chapter 49](finger-histories.html).

## Building a pair from a cursor

A source cursor is a context `cs` of labelled frames ([[LabelledCursor.Frame]]), innermost first, and a focus `node left key right`. The whole source tree is `plug cs (.node left key right)`. The lower frames, in inorder, are [[HeavyPath.Recursive.lowerFrames]]` cs`, and the upper ones are [[HeavyPath.Recursive.upperFrames]]` cs`, from the finger outward.

### Slots and their charges

@decl RotationBST.HeavyPath.Finger.sideSlots

`sideSlots weight payload boundary carry fs` lists one side's slots, outermost first, as pairs of a physical payload and its charge. Each frame `f` of `fs` contributes the slot `payload (framePayload f)` ([[HeavyPath.Paired.framePayload]]), charged with its subtree's mass plus `carry`. The `carry` is the weight of the previous frame's separator, [[HeavyPath.frameKey]]. The last slot is the finger's child `boundary`, which carries the weight of the innermost separator. The first slot has no preceding separator, so the build starts with `carry = 0`. The physical payloads are given by a function, so the same list can describe raw subtrees or recursively rebuilt ones. The build uses [[HeavyPath.Recursive.rebuild]], the canonical recursive layout of [Chapter 47](recursive-heavy-paths.html).

@decl RotationBST.HeavyPath.Finger.Results.sideSlots_nonempty RotationBST.HeavyPath.Finger.Results.sideSlots_nonnegative RotationBST.HeavyPath.Finger.Results.sideSlots_mass RotationBST.HeavyPath.Finger.Results.sideSlots_span RotationBST.HeavyPath.Finger.Results.frame_mass_partition

These five facts are the bookkeeping. A side always has at least one slot, the finger's child. With positive weights and a nonnegative carry, every charge is nonnegative. The charges add up to the carry plus the mass of the boundary plus the masses [[HeavyPath.frameMass]] of the frames, each frame's mass being its separator's weight plus its payload's mass. The `fringeSpan` ([[PopTart.WeightedTree.fringeSpan]]) of the slots, one plus the size of each payload, counts the keys of the payloads together with the separators that follow them. The lower and upper frames partition the frames of the context, so their masses add up to the total.

### Assembly by pushes

@decl RotationBST.HeavyPath.Finger.assemble

`assemble slots` builds a Chocolate stack whose fringe is `slots`, read top first. It starts from the last slot as the stack's only leaf and pushes the others in turn with the real Chocolate push ([[PopTart.Chocolate.Layer.push]]), so the result is an actual stack history, not a stack written down directly. The value on the empty list is only a totalization.

@decl RotationBST.HeavyPath.Finger.Results.assemble_valid_fringe RotationBST.HeavyPath.Finger.Results.assemble_mass

On a nonempty list of nonnegative charges, the assembled stack is valid, its fringe ([[PopTart.WeightedTree.fringe]]) is exactly the list, and its mass is the sum of the charges.

### The build

@decl RotationBST.HeavyPath.Finger.reflectSlot RotationBST.HeavyPath.Finger.build

`build weight cs left right` assembles both stacks. The lower slots are mirrored with `reflectSlot`, which mirrors the payload and keeps its charge, and are reversed so that the finger's child `left` is on top. The upper frames are reversed so that the slots are computed from the root inward, as the charging rule needs, and the slot list is reversed back so that `right` is on top. The key of the focus is not an argument: the finger is the pair's root node, and its key is implicit in the position.

@decl RotationBST.HeavyPath.Finger.Results.build_valid_fringe RotationBST.HeavyPath.Finger.Results.build_mass RotationBST.HeavyPath.Finger.Results.build_side_sizes RotationBST.HeavyPath.Finger.Results.build_size RotationBST.HeavyPath.Finger.Results.lower_blocks_offset RotationBST.HeavyPath.Finger.Results.build_root_key

With positive weights on the whole source tree:

- the pair is valid, and its two fringes, in physical inorder, are the slot lists of the two sides (`build_valid_fringe`);
- the finger's weight plus the pair's mass is the total weight of the source tree (`build_mass`);
- the lower side has as many nodes as the lower blocks ([[HeavyPath.Recursive.lowerBlock]]: each lower payload with its separator) plus `left`, the upper side likewise, and the whole pair has as many nodes as the source tree (`build_side_sizes`, `build_size`);
- the lower blocks contain exactly [[Pointer.offset]] of the erased context keys, the number of keys before the focus (`lower_blocks_offset`), so the root of the pair has the rank of the finger in the source (`build_root_key`, stated with [[Pointer.Config.key?]]).

@decl RotationBST.HeavyPath.Finger.Results.build_labels

If the source tree is a BST ([[LabelledTree.Ordered]]), the pair's tree has exactly one labelling with the same inorder, and that labelling is a BST. The physical tree therefore stores the same keys in the same order. Only the shape differs.

### Setup cost

**Theorem (setup).** For positive weights, the pointer machine turns the source tree into the finger pair, from root configuration to root configuration, with at most $16n$ instructions, where $n$ is the number of nodes.

@decl RotationBST.HeavyPath.Finger.Results.build_initialization

The proof does not follow the construction. Any two trees with the same number of nodes are at most $16n$ pointer instructions apart, by the generic reshaping theorem [[Pointer.Results.reshape]] of [Chapter 6](pointer.html), and `build_size` says the sizes agree. The constant is therefore that of reshaping, and the same argument gives the setup of a heavy-path layout, [[HeavyPath.Recursive.Results.rebuild_initialization]]. This is the $16n$ setup term that the deamortization charges once, before any request.

## Depth

The depth bound has two levels. The first bounds the depth of a slot or separator within the pair, in terms of the pair's mass. The second adds the depth inside the slot's payload, which [Chapter 47](recursive-heavy-paths.html) bounds by the payload's mass. The two logarithms telescope.

### Inside the pair

The theorems below locate a slot in the pair's outer weighted tree, `node lower.mirror upper`, whose physical tree is the pair's tree. A [[PopTart.WeightedTree.LocatedSlot]] records the slot's payload, its charge, the inorder offset of its first key, and its edge depth ([Chapter 44](pop-tarts.html)).

@decl RotationBST.HeavyPath.Finger.Results.located_mass RotationBST.HeavyPath.Finger.Results.located_depth RotationBST.HeavyPath.Finger.Results.located_key_bound RotationBST.HeavyPath.Finger.Results.located_predecessor_bound RotationBST.HeavyPath.Finger.Results.located_successor_bound

In a valid pair of mass $M$, a slot of charge $w > 0$:

- has $0 \le w \le M$ (`located_mass`);
- sits at depth at most $8 + 7\log_2(M/w)$, which is one edge below the finger plus the Chocolate bound $7 + 7\log_2$ (`located_depth`);
- puts the key of rank $i$ of its payload at depth at most $8 + 7\log_2(M/w)$ plus that key's depth inside the payload (`located_key_bound`);
- has its two neighbouring separators, the keys just before and just after it in inorder, at depth at most $7 + 7\log_2(M/w)$, when they exist (`located_predecessor_bound`, `located_successor_bound`).

Neighbouring separators are the reason for the charging rule. Every ancestor is the immediate predecessor or successor of the slot that carries its weight, so its depth is at most $7 + 7\log_2(M/w(x))$. The finger itself is at depth $0$.

### Telescoping

@decl RotationBST.HeavyPath.Finger.Results.payload_estimate

`payload_estimate` is pure arithmetic. Consider masses $k \le c \le C \le P \le W$: a key's weight $k$, the mass $c$ of the payload containing it, that payload's charge $C$, the pair's mass $P$ and the whole weight $W$. Suppose a depth $d$ is at most $8 + 7\log_2(P/C)$, for the slot, plus $7 + 15\log_2(c/k)$, the recursive bound of [[HeavyPath.Recursive.Results.rebuild_depth]] inside the payload. Then $d \le 15 + 15\log_2(W/k)$. The constant $15$ absorbs the outer constant $8 + 7$, and the coefficient $15 \ge 7$ absorbs the outer logarithm. This is the telescoping sum at the end of the paper's Section 3. The heavy-path pairs of [Chapter 47](recursive-heavy-paths.html) telescope in the same way ([[HeavyPath.Recursive.Results.depth_telescope]]), and the finger pair costs $8$ more in the constant.

### Depth of a fresh pair

**Theorem (weighted depth).** With positive weights and total weight $W$, every node occurrence of weight $w$ in the source tree has depth at most $15 + 15\log_2(W/w)$ in the built pair. With unit weights, the bound is $15 + 15\log_2 n$.

@decl RotationBST.HeavyPath.Finger.Results.build_depth RotationBST.HeavyPath.Finger.Results.build_depth_at RotationBST.HeavyPath.Finger.Results.build_unit_depth

`build_depth` names an occurrence by splitting the source inorder as `before ++ target :: after`; its rank is `before.length`. Labels may repeat, so this form refers to one occurrence and not to a key. `build_depth_at` is the same statement indexed by a rank. `build_unit_depth` takes all weights equal to $1$, so $W = n$, and needs no positivity hypothesis. None of the three assumes that the ancestor path of the finger is heavy: the bound holds for every cursor.

@decl RotationBST.HeavyPath.Finger.Results.build_search_walk

The search walk turns depth into cost. For every rank there is a configuration with the cursor on that rank and the tree unchanged, reached from the root and left back to the root by traces of the same length `cost`. One unit for the request plus the walk down and back costs at most $31 + 30\log_2(W/w)$. This is the form in which the deamortization uses the depth bound: it serves a pending request by walking to the key and back.

## Population

The Chocolate worst-case bounds of [Chapter 45](chocolate.html), [[PopTart.Chocolate.Results.push_worst_case]] and [[PopTart.Chocolate.Results.pop_worst_case]], are stated in terms of a stack's number of slots, its [[PopTart.WeightedTree.leafCount]]. The simulation needs them in terms of $N$, the number of nodes of the pair's tree, which does not change as the finger moves.

@decl RotationBST.HeavyPath.Finger.Population.Results.pair_population

Each stack of any pair has between $1$ and $N$ slots. A stack with $s$ slots has $s - 1$ separators, and the finger is outside both stacks, so this holds with no validity hypothesis.

@decl RotationBST.HeavyPath.Finger.Population.Results.lower_push RotationBST.HeavyPath.Finger.Population.Results.upper_push RotationBST.HeavyPath.Finger.Population.Results.lower_pop RotationBST.HeavyPath.Finger.Population.Results.upper_pop

In a valid pair, the rebalancing cost of a push onto either stack ([[PopTart.Chocolate.Layer.pushCost]]) is at most $6 + 14\log_2 N$, and that of a pop ([[PopTart.Chocolate.Layer.popCost]]) at most $6 + 10\log_2 N$. These are the bounds of [Chapter 45](chocolate.html) with the slot count replaced by $N$.

@decl RotationBST.HeavyPath.Finger.Population.Results.lower_payload_size RotationBST.HeavyPath.Finger.Population.Results.upper_payload_size

The top payload of either stack ([[PopTart.Chocolate.Layer.top]]), a single slot holding a subtree `shape`, has at most $N$ nodes. Exposures inside that payload are bounded in terms of its size, so these lemmas express their worst-case costs in terms of $N$ too.

## Moving the finger down

### The transfer

@decl RotationBST.HeavyPath.Finger.Pair.potential RotationBST.HeavyPath.Finger.Pair.downLeft RotationBST.HeavyPath.Finger.Pair.leftExposeCost RotationBST.HeavyPath.Finger.Pair.downLeftCost

The potential of a pair is the sum of the Chocolate potentials of its stacks ([[PopTart.Chocolate.Layer.potential]]). `p.downLeft a b lowerCharge upperCharge` is the pair after the finger moves to its left child, assuming that child is the root of the top lower payload, with subtrees `a` and `b`. The lower stack keeps its structure. [[PopTart.Chocolate.Layer.replaceTop]] swaps its top payload for `a`, mirrored, with a new charge. The upper stack receives `b` by a real push, and the old finger becomes the separator of that push. The new charges are parameters, so the caller decides how the two moving weights are booked. The `_source` and history lemmas below fix them.

The cost has three parts. Reaching the new finger and rotating it to the root costs $2$ instructions if the lower stack's top layer has no separator above the top payload ([[PopTart.Chocolate.Layer.topTail]] is `none`), and $4$ if one separator stands between: two descents and two rotations. Then the upper push costs its Chocolate rebalancing cost plus $2$ for entering the stack and returning.

@decl RotationBST.HeavyPath.Finger.Pair.flip RotationBST.HeavyPath.Finger.Pair.downRight RotationBST.HeavyPath.Finger.Pair.downRightCost

`flip` swaps the stacks, which mirrors the whole tree. The move to the right child is defined as the move to the left child in the flipped pair, with the subtrees mirrored and the charges swapped, flipped back. Its cost is defined in the same way. Every `downRight` lemma is the corresponding `downLeft` lemma transported through `flip`, using the three facts below.

@decl RotationBST.HeavyPath.Finger.Transfer.Results.flip_tree RotationBST.HeavyPath.Finger.Transfer.Results.flip_mass RotationBST.HeavyPath.Finger.Transfer.Results.flip_potential

### Local guarantees

**Theorem (transfer).** Suppose the top payload of the lower stack is the subtree `node a b`, mirrored, with some charge. Then the move costs exactly `downLeftCost` pointer instructions, root to root. Validity is preserved for nonnegative new charges. The amortized cost, actual cost plus potential change, is at most $26$. The mass changes by exactly the new charges minus the old one. The new root has the rank of the old top payload's root. The right-hand move is symmetric.

@decl RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_trace RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_valid RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_amortized RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_mass RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_root_key RotationBST.HeavyPath.Finger.Transfer.Results.downLeft_fringe

The trace, the mass equation, the root key and the fringe need the exposure hypothesis `exposed`. Validity and the amortized inequality are about the defined result and its defined cost, so they hold without it. `downLeft_fringe` describes the move on the fringes. The last lower slot `(node a b, oldCharge)` becomes `(a, lowerCharge)`, and `(b, upperCharge)` becomes the first upper slot. All other slots are unchanged.

@decl RotationBST.HeavyPath.Finger.Transfer.Results.downRight_trace RotationBST.HeavyPath.Finger.Transfer.Results.downRight_valid RotationBST.HeavyPath.Finger.Transfer.Results.downRight_amortized RotationBST.HeavyPath.Finger.Transfer.Results.downRight_mass RotationBST.HeavyPath.Finger.Transfer.Results.downRight_root_key RotationBST.HeavyPath.Finger.Transfer.Results.downRight_fringe

The mirror images. Here `a` is pushed onto the lower stack, so the new root's rank is the old lower size plus `a.size + 1` whatever the top payload was. `downRight_root_key` has no exposure hypothesis, unlike its left counterpart, whose rank depends on the size of the replaced payload.

### Exposing the new finger

In a real pair the new finger is usually not at the physical root of its payload. A payload holds a recursive heavy-path representation, whose physical root is the *endpoint* of the subtree's heavy path, while the subtree's source root is near the top of one of its stacks. Before the transfer, the payload must be restructured to bring its source root to the top. That is an *exposure*, [[HeavyPath.Recursive.Exposure.View]] of [Chapter 47](recursive-heavy-paths.html). The lemmas below compose an exposure with the transfer. The cost counted includes every descent into the payload and every return, through the separator that may stand between the finger and its top slot.

@decl RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downLeft_exposed RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downRight_exposed RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downLeft_exposed_bounded RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downRight_exposed_bounded

These are generic. If some pointer trace of cost $e$ turns the top payload `old` into `node a b`, root to root, then some trace performs the whole move, with amortized cost at most $e + 30$, the validity, mass and root-key conclusions as before, and, in the `_bounded` forms, actual cost at most $e$ plus the receiving stack's push cost plus $10$.

@decl RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downLeft_pair RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downRight_pair RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downLeft_recursive RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downRight_recursive

These specialize the exposure to recursive payloads. Let the top payload be the tree of a heavy-path pair `child` ([[HeavyPath.Paired.Stacks]]) that represents the heavy path of the source subtree `node l x r`, in the sense of [[HeavyPath.Paired.Stacks.Represents]]. Then there is an exposure view, valid for `l` and `r` ([[HeavyPath.Recursive.Exposure.View.Valid]]). The view keeps the residual heavy path of the heavy child as an actual pair, with its own potential, and the light child in its rebuilt layout. The move to `x` with `a` and `b` taken from the view ([[HeavyPath.Recursive.Exposure.View.leftTree]] and `rightTree`) satisfies

$$\text{cost} + \Phi(\text{next}) + \Phi(\text{view}) \;\le\; 54 + \Phi(p) + \Phi(\text{child}).$$

The child pair's potential pays for its exposure, and the residual pair's potential is handed on to the view. The `_pair` forms allow `child` to be any valid representation, including one left behind by earlier exposures. The `_recursive` forms take the canonical rebuilt payload, whose pair is [[HeavyPath.Recursive.rootPair]].

@decl RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downLeft_source RotationBST.HeavyPath.Finger.Transfer.Exposure.Results.downRight_source

The `_source` forms fix the charges to keep the charging rule. Suppose the top payload of `node l x r` is charged `carry` plus its mass, where `carry` is the weight of the separator before it. After the move, the slot of `l`, which stays on the same side, is charged `carry` plus the mass of `l`. The slot of `r`, now on the other side behind the old finger, is charged the old finger's weight plus the mass of `r`. Then the new finger's weight plus the new mass equals the old mass plus the old finger's weight. So the invariant of `build_mass`, finger weight plus pair mass equals $W$, is preserved.

### With arbitrary histories

After a few moves, the payloads are no longer canonical. A payload may hold a residual path, a pair rebuilt by pops, or a subtree whose stacks have any valid history. [[HeavyPath.Recursive.History.Layout]] of [Chapter 47](recursive-heavy-paths.html) describes all of these, together with a repair *credit*, the potential of the pairs it contains. The final transfer lemmas are stated for such layouts, and these are the ones that [Chapter 49](finger-histories.html) uses.

@decl RotationBST.HeavyPath.Finger.Transfer.History.Results.downLeft RotationBST.HeavyPath.Finger.Transfer.History.Results.downRight

**Theorem (downward move).** Suppose the top lower payload is a layout of the source subtree `node l x r` with credit $c$, charged `carry` plus its mass. Then there are layouts of `l` and `r`, with credits $c_l$ and $c_r$, such that the move with the charges of the `_source` forms is a root-to-root trace of some cost, keeps the pair valid, preserves the mass invariant, puts the right rank at the root, and satisfies

$$\text{cost} + \Phi(\text{next}) + c_l + c_r \;\le\; 54 + \Phi(p) + c.$$

The symmetric statement holds for the right child.

@decl RotationBST.HeavyPath.Finger.Transfer.History.Results.downLeft_bounded RotationBST.HeavyPath.Finger.Transfer.History.Results.downRight_bounded

The `_bounded` forms add the worst case: the actual cost is at most $26 + 24\log_2 N$. It combines the worst-case cost of the exposure inside the payload, which [Chapter 47](recursive-heavy-paths.html) bounds by the logarithm of the payload's size, the push onto the receiving stack, and a constant number of moves. The population bounds above turn both logarithms into $\log_2 N$.

@decl RotationBST.HeavyPath.Finger.Transfer.History.Results.downLeft_within RotationBST.HeavyPath.Finger.Transfer.History.Results.downRight_within

The `_within` forms strengthen the trace to a [[Pointer.TraceWithin]]: at every instruction boundary of the move, the intermediate tree has $N$ nodes, and every rank's depth is at most $16$ times its depth in the starting tree plus $64$. The deamortization may interrupt the simulation in the middle of a source operation to serve a request. It then needs a depth bound for the tree as it stands, and this invariant provides it. The bound is relative: it combines with the logarithmic depth of the starting pair, which [Chapter 49](finger-histories.html) maintains, to give a logarithmic bound for every intermediate tree.

## What is not here

The upward moves and the two rotations of the source finger are proved in [Chapter 49](finger-histories.html), on the full finger state. An upward move pops the separator next to the finger from one stack and joins it, with the finger's child, into a payload on the other side. A rotation exchanges a constant number of slots. The local pair-level lemmas behind them live in the proof files `Transfer/Up`, `Transfer/Rotation` and `Transfer/Interruption` and are not part of the reading interface. The paper's remark that $O(1)$ bits per node suffice to store the roles of the nodes belongs to Theorem 7's storage clauses. The library does not formalize it.
