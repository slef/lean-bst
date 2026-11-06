# Pop-tarts

The deamortization of Bose, Collette, Fagerberg and Langerman ([Chapter 37](deamortization.html)) stores every heavy path of the simulated tree as two stacks, and each stack is itself a binary search tree. Section 2 of their paper calls such a BST a *pop-tart*. Nodes are pushed in decreasing key order: the new node arrives as the parent of the current root, with the old stack as its right subtree and a leaf as its left subtree. A pop removes the root, whose left child is a leaf. Between operations the structure may rebalance with finger moves and rotations, and it must end with the finger back at the root.

Leaves carry weights. In the paper's terms, a pop-tart is *good* if push and pop take $O(1)$ amortized and $O(\log n)$ worst-case time, and *crazy good* if moreover every leaf of weight $w$ has depth $O(\log W/w)$, where $W$ is the total weight of the leaves. The paper describes three pop-tarts. *Vanilla* never rebalances; it is crazy good when each new leaf outweighs the rest of the stack. *Cherry* is a 2-4 tree laid out along the right spine; it is crazy good for unit weights, and for weights that only increase. *Chocolate* adds frozen *icing* layers, built as Vanilla stacks, and is crazy good for arbitrary weights. Chocolate is the one the deamortization uses. It is the subject of [Chapter 45](chocolate.html).

This chapter covers the common vocabulary, Vanilla and Cherry, and two variants used by the heavy-path chapters: slots *located* by their physical rank, and *mirrored* pop-tarts that push in increasing key order.

```headline pop-tarts-vanilla
title: Vanilla pop-tarts are crazy good when pushed weights dominate
source: Bose, Collette, Fagerberg and Langerman, *De-amortizing binary search trees* (2012)
theorems: PopTart.Vanilla.Results.push_valid PopTart.Vanilla.Results.pop_valid PopTart.Vanilla.Results.operation PopTart.Vanilla.Results.depth_log

A Vanilla pop-tart is a right spine whose left children are its weighted leaves, and whose last right child is the leaf of the initial empty stack. It is *valid* if the bottom leaf has nonnegative weight and every pushed leaf has weight at least the total weight of the leaves below it on the spine. Pushing a leaf of weight $w \ge W$ onto a valid stack of total weight $W$ gives a valid stack, and popping a valid stack gives a valid stack. Each push and pop is realized by a pointer trace of **zero** instructions, root to root, under any context. In a valid stack of total weight $W$, a leaf of weight $w > 0$ at depth $d$ satisfies

$$d \;\le\; 1 + \log_2 \frac{W}{w}.$$

This is Lemma 1 of the paper, with its constant. Depth counts edges from the root, and the weights of internal nodes are not part of $W$. A leaf may hold a whole subtree, frozen as one *fringe slot* of a [[PopTart.WeightedTree]]. The decreasing key order of pushes is built into the shape of the operations and is not a hypothesis.
```

```headline pop-tarts-cherry
title: Cherry pop-tarts are good, and crazy good under increasing weights
source: Bose, Collette, Fagerberg and Langerman, *De-amortizing binary search trees* (2012)
theorems: PopTart.Cherry.Results.empty_sequence PopTart.Cherry.Results.worst_case PopTart.Cherry.Results.depth_log PopTart.Cherry.Results.key_depth PopTart.Cherry.Results.weighted_sequence

Start a Cherry pop-tart from the empty stack, and apply any sequence of $n$ pushes and pops of single leaves. Then every operation is realized by a pointer trace, root to root, and the total number of instructions is at most $10n$. A stack with $L$ leaves has every leaf at depth at most $4\log_2 L$. Its next push costs at most $10\log_2 L$ instructions, and its next pop at most $6\log_2 L$. In an ordinary pop-tart, whose leaves are empty, with $n$ nodes, every node has depth less than $4\log_2(n+1)$. This is Lemma 2 of the paper, with explicit constants.

Suppose in addition that the bottom leaf has nonnegative weight and that each pushed leaf weighs at least as much as every leaf currently in the stack. Then the leaves stay sorted by nonincreasing weight in inorder, the total cost is still at most $10n$, and in the final stack of total weight $W$ every leaf of weight $w > 0$ has depth

$$d \;\le\; 3 + 4\log_2 \frac{W}{w}.$$

This is Lemma 3 of the paper. The lemma is stated with $O(\cdot)$; its proof ends with $4\log_2(W/w)$, which drops an additive constant: the heaviest leaf is at depth $1$, while $\log_2(W/w)$ can be $0$. The Lean bound adds $3$ for the spine nodes. The costs are those of [[PopTart.Cherry.Program.cost]], and `empty_sequence` and `weighted_sequence` write the cost bound as $n + \text{cost} \le 11n$, which is $\text{cost} \le 10n$.
```

The two boxes state what the library proves of the paper's Lemmas 1–3. The rest of the chapter gives the definitions in reading order and the theorems again, each with its Lean statement. [Section 44.1](#overview) compares the paper's conventions with the library's, and summarizes the bounds.

::: note Do you need this chapter?
These results support others. Outside this chapter, Vanilla appears only in one theorem of the next chapter, and Cherry nowhere. Chocolate ([Chapter 45](chocolate.html)) builds on the weighted trees, slots and crumbs of this chapter, and proves its icing bound by viewing each icing as a Vanilla stack ([[Chocolate.Results.icing_vanilla]]). The paired stacks of heavy paths ([Chapter 46](heavy-paths.html)) use mirrored pop-tarts for the ancestors larger than the endpoint, and located slots to translate slot depths into key depths. Cherry pop-tarts are used nowhere else in the library, as in the paper, where they are a warm-up for Chocolate. Read the sections on weighted trees and Vanilla before [Chapter 45](chocolate.html), and the sections on located slots and mirrored pop-tarts before [Chapter 46](heavy-paths.html). The Cherry section can be skipped.

The definitions are in `Structures/PopTart/Definitions/Abstract.lean` and the `Definitions/Abstract.lean` files of `Vanilla`, `Cherry`, `Located` and `Mirror` below it. The theorems are in the `Abstract.lean` files of the same directories.
:::

## Overview

All pop-tarts of the library are values of one type, [[PopTart.WeightedTree]]: a binary tree whose internal nodes are the stack's nodes and whose leaves are *fringe slots*. A slot holds a weight and an arbitrary [[RotationBST.Tree]], its *payload*. An ordinary pop-tart has empty payloads. The Chocolate pop-tart and the heavy paths need nonempty ones: Chocolate freezes whole crumbs inside its icing, and a heavy-path stack stores each off-path subtree as one slot. The physical BST is the weighted tree with every slot replaced by its payload.

A Cherry pop-tart, drawn with its layers, looks like this, with `c` the crumbs and `⊥` the bottom slot of the empty stack:

```text
s₁ ─ s₂ ─ s₃ ─ s₄ ─ s₅ ─ … ─ ⊥       the right spine; s₁ is the root
│    │    │    │    │
c    c    c    C    C                 c = 0-crumb (one slot), C = 1-crumb (two slots)
└─ layer 0 ┘   └ layer 1 ┘
```

Each spine node $s_j$ is a separator whose left subtree is its crumb. A Vanilla pop-tart is the same picture with only one-slot crumbs and no layers.

The paper's model and the library's differ in a few conventions:

| paper | library |
|---|---|
| leaves, possibly empty pointers | fringe slots of a [[PopTart.WeightedTree]], each with a payload subtree and a real weight |
| internal nodes have weight $1$ | internal nodes carry no weight; [[PopTart.WeightedTree.mass]] sums slot weights only |
| depth of a leaf | outer depth of a slot, [[PopTart.WeightedTree.SlotAt]], the number of separator nodes above it |
| keys pushed in decreasing order | structural: a push receives the tree `node t stack`, with the old stack on the right |
| the finger returns to the root | costs are [[RotationBST.Pointer.Trace]]s from root to root ([Chapter 6](pointer.html)) |
| time | pointer instructions, one unit each for moves and rotations |
| inserting or removing the root | the caller's business, outside the operation's cost |

The last line matters. A push starts from the tree in which the new node is already the parent of the stack, and a pop ends with the popped node as the root above the rest. Moving the node between the stack and its caller is charged by whoever uses the pop-tart, such as the heavy-path stacks of [Chapter 46](heavy-paths.html).

The bounds proved in this chapter are:

| structure | cost per operation | depth of a slot of weight $w$ | hypothesis |
|---|---|---|---|
| Vanilla | $0$ instructions | $\le 1 + \log_2(W/w)$ | each push dominates the mass below |
| Cherry | $\le 10$ amortized; $\le 10\log_2 L$ (push), $\le 6\log_2 L$ (pop) worst case | $\le 4\log_2 L$ | one-slot pushes |
| Cherry, weighted | $\le 10$ amortized | $\le 3 + 4\log_2(W/w)$ | each push weighs at least every current slot |

Here $W$ is the total weight of the slots and $L$ their number.

## Weighted trees

### The type

@decl PopTart.WeightedTree

A weighted tree is either a slot `leaf subtree weight` or a separator node `node left right`. The separator nodes are the pop-tart's active nodes. Equal payloads may occur in several slots with different weights, and the type never inspects a payload.

@decl PopTart.WeightedTree.skeleton PopTart.WeightedTree.tree

`skeleton` forgets the weights and gives a [[Pointer.Lazy.Skeleton]] of [Chapter 6](pointer.html#reshaping-a-connected-region): the separators become the skeleton's nodes and the slots become holes. `tree` fills the holes in, and is the physical BST in which the pointer machine runs. So a slot whose payload has $k$ keys contributes $k$ keys to `tree` and none to the skeleton's size.

@decl PopTart.WeightedTree.mass PopTart.WeightedTree.Nonnegative PopTart.WeightedTree.leafCount PopTart.WeightedTree.fringe

`mass` is the total weight $W$ of the slots. `Nonnegative` says that every slot weight is nonnegative. `leafCount` is the number $L$ of slots, independent of payloads. `fringe` lists the slots in inorder as pairs (payload, weight). Equal pairs remain distinct list entries, so the fringe records occurrences, not a set.

@decl PopTart.WeightedTree.height PopTart.WeightedTree.EmptyFringe

`height` counts separator levels only: a slot is a leaf of height $0$, whatever its payload. `EmptyFringe` says that every payload is `nil`. That is the ordinary pop-tart of the paper, in which the slots are the external leaves of the physical tree.

### Slots

@decl PopTart.WeightedTree.SlotAt

`SlotAt t subtree weight depth` says that `t` has a slot with this payload and weight at outer depth `depth`. It is a path from the root, so two equal slots at different places are two different witnesses. The depth bounds of this chapter and the next are stated for `SlotAt` witnesses, or for the located slots below.

The basic facts say that a slot's depth is the cost of reaching it, that slots are fringe entries, and that weights are bounded by the mass:

@decl PopTart.WeightedTree.Results.slot_context PopTart.WeightedTree.Results.slot_trace PopTart.WeightedTree.Results.slot_split PopTart.WeightedTree.Results.slot_le_mass

`slot_context` gives the zipper path ([[Pointer.Frame]]s) of the slot: it has exactly `depth` frames, and plugging the payload back in gives `t.tree`. `slot_trace` adds that, when the payload is nonempty, the pointer machine walks from the root to the payload's root in exactly `depth` instructions. The payload must be nonempty because the cursor never moves onto `nil`. `slot_split` places the slot in the fringe list, and `slot_le_mass` bounds its weight by $0 \le w \le W$ in a nonnegative tree.

@decl PopTart.WeightedTree.Results.height_slot PopTart.WeightedTree.Results.empty_count PopTart.WeightedTree.Results.key_depth_lt_height

Some slot lies at depth exactly `height`, so a bound on all slot depths bounds the height. When every payload is empty, there is one slot more than keys, and every key is strictly shallower than the height. These two facts turn slot bounds into the key bounds of an ordinary pop-tart, as in [[PopTart.Cherry.Results.key_depth]].

@decl PopTart.WeightedTree.Results.fringe_length PopTart.WeightedTree.Results.fringe_mass PopTart.WeightedTree.Results.fringe_nonnegative PopTart.WeightedTree.Results.mass_nonnegative

The fringe has `leafCount` entries, its weights sum to `mass`, and the tree is nonnegative exactly when every fringe weight is. Hence a nonnegative tree has nonnegative mass.

### Crumbs

@decl PopTart.WeightedTree.Perfect

A *crumb* of level $i$, an $i$-crumb in the paper, is a perfect weighted tree of height $i$. Its slots are arbitrary: Cherry fills them with single leaves, and Chocolate may fill them with frozen subtrees.

@decl PopTart.WeightedTree.Results.perfect_count PopTart.WeightedTree.Results.perfect_depth

An $i$-crumb has $2^i$ slots, all at depth $i$.

### Ordered fringes

@decl PopTart.WeightedTree.Ordered

`Ordered t` says that `t` is nonnegative and that its fringe weights are nonincreasing in inorder, ties allowed. The condition concerns all occurrences, including the bottom slot. It is the invariant behind the weighted Cherry bound: the most recently pushed slots are the heaviest and come first.

@decl PopTart.WeightedTree.Results.ordered_append PopTart.WeightedTree.Results.ordered_prefix_mass

`ordered_append` says that a fringe split into two parts is ordered exactly when both parts are ordered and every weight of the first part is at least every weight of the second. `ordered_prefix_mass` is the step from ranks to weights in the paper's proof of Lemma 3. If the slot of weight $w$ is the $k$-th entry of an ordered fringe, the $k$ entries up to it each weigh at least $w$, so

$$k\,w \;\le\; W .$$

## Vanilla pop-tarts

A Vanilla pop-tart performs no rebalancing at all. The stack is a right spine: each push adds a node above the root, with its slot on the left.

@decl PopTart.Vanilla.Valid

`Valid` is the paper's weight condition. The empty stack is one slot of nonnegative weight. A push of slot weight $w$ onto a valid stack `tail` is valid when $W(\mathit{tail}) \le w$, that is, when the new slot weighs at least as much as all the others together. Equality is allowed, as in Lemma 1.

@decl PopTart.Vanilla.push PopTart.Vanilla.pop

`push t w stack` is the node whose left slot holds `t` with weight `w` and whose right child is `stack`. `pop` exposes the top slot and the stack below. It fails on a single slot, and on a node whose left child is not a slot, which no valid stack has.

@decl PopTart.Vanilla.Operation PopTart.Vanilla.Operation.input PopTart.Vanilla.Operation.output PopTart.Vanilla.Operation.Realizes

An `Operation stack tail` is a push, or a pop that is known to succeed. `input` and `output` are the physical trees at the operation's boundaries. A push starts from `node t stack.tree`, the new node already above the old stack, and ends at the pushed stack. A pop starts from the stack and ends with the top node above the rest, `node t tail.tree`. `Realizes op cost` asks for a pointer trace from input to output, root to root, with `cost` instructions. In both cases input and output are the same tree, which is why Vanilla costs nothing.

### Validity

@decl PopTart.Vanilla.Results.push_valid PopTart.Vanilla.Results.pop_valid

Pushing a dominating slot preserves validity, and popping a valid stack returns a valid stack together with the popped slot, which is nonnegative and dominates the rest.

@decl PopTart.Vanilla.Results.pop_push PopTart.Vanilla.Results.cases_valid PopTart.Vanilla.Results.nonnegative

A pop undoes a push. A valid stack is either a single nonnegative slot or a dominating push onto a valid stack. Valid stacks are nonnegative.

@decl PopTart.Vanilla.Results.push_fringe PopTart.Vanilla.Results.pop_fringe

A push adds its payload at the front of the fringe, and a pop removes it. So the fringe of a Vanilla stack is the list of payloads from the most recent to the oldest, ending with the bottom.

### Cost

**Theorem (Vanilla operations).** Every Vanilla push and pop is realized by a pointer trace of zero instructions, under any context.

@decl PopTart.Vanilla.Results.operation

The context `cs` places the pop-tart anywhere inside a larger tree. Since input and output coincide, the empty trace works. The paper's "$O(1)$ time per operation" is, in this accounting, the caller's transfer of the node into or out of the stack.

### Depth

**Theorem (Lemma 1, depth).** In a valid Vanilla stack of mass $W$, a slot of weight $w$ at depth $d$ satisfies $2^d w \le 2W$. If $w > 0$, then $d \le 1 + \log_2(W/w)$.

@decl PopTart.Vanilla.Results.depth_mass PopTart.Vanilla.Results.depth_log

The proof is the paper's induction. The top slot is at depth $1$ and weighs at least $W/2$. Every other slot lies in the tail, whose mass is at most $W/2$, one level deeper. The base case, a single slot at depth $0$, gives $w \le 2W$.

@decl PopTart.Vanilla.Results.access_slot

`access_slot` combines this bound with [[PopTart.WeightedTree.Results.slot_trace]]: a slot with a nonempty payload is reached from the root by exactly $d$ pointer moves, with $d \le 1 + \log_2(W/w)$. Chocolate's icing access lemma, [[Chocolate.Results.icing_access]], is this theorem applied to the icing viewed as a Vanilla stack.

## Cherry pop-tarts

The Cherry pop-tart is a 2-4 tree laid along the right spine. The spine is cut into *layers* of consecutive nodes. Layer $i$ holds one to three $i$-crumbs as the left subtrees of its nodes, and the last node of a layer has the first node of the next layer as its right child. The last layer ends in the bottom slot of the empty stack. A push adds a $0$-crumb to layer $0$. When a layer would hold four crumbs, one rotation joins its last two crumbs into a crumb of the next level, which is pushed onto the next layer. A pop removes the first $0$-crumb; when a layer becomes empty, one rotation splits the first crumb of the next layer into two. These carries and borrows behave like the digits of a redundant binary counter.

### Layers

@decl PopTart.Cherry.Layers PopTart.Cherry.Layers.decode PopTart.Cherry.Layers.height

`Layers` is a list of layers, each with one, two or three crumbs. `decode bottom layers` is the weighted tree: the crumbs of all layers, in order, as the left children of the spine, with `bottom` at the end. `height` is the number of layers, not the height of the tree.

@decl PopTart.Cherry.Valid

`Valid level layers` says that the crumbs of the first layer are perfect of height `level`, those of the next layer of height `level + 1`, and so on. A Cherry pop-tart is a valid `Layers` at level $0$ with a single-slot bottom, `Perfect 0 bottom`. The general level is needed for the recursion: a carry from layer $i$ is a push at level $i+1$.

### Push and pop

@decl PopTart.Cherry.Layers.push PopTart.Cherry.Layers.pop

`push new` adds a crumb in front of the first layer. A full layer `three a b c` becomes `two new a`, and the crumb `node b c` is pushed recursively onto the next layer. `pop` takes the first crumb. A layer `one a` with a nonempty tail borrows: it pops a crumb `node b c` from the next layer and becomes `two b c`. The pop is totalized by `none` on shapes the invariant excludes, for example a borrowed crumb that is a single slot.

@decl PopTart.Cherry.Layers.pushCost PopTart.Cherry.Layers.popCost PopTart.Cherry.Layers.potential

`pushCost` charges $10$ instructions for each carry, and `popCost` charges $6$ for each borrow. These are the exact lengths of the traces built in the proofs: walk down the spine to the layer, rotate, and walk back. The potential is the paper's, scaled to the cost: $10$ for each layer with one or three crumbs, $0$ for a layer with two. A carry turns a three-crumb layer into a two-crumb layer, and a borrow turns a one-crumb layer into a two-crumb layer, so each releases exactly the $10$ units that pay for it.

### Operations and programs

@decl PopTart.Cherry.Operation PopTart.Cherry.Operation.cost PopTart.Cherry.Operation.input PopTart.Cherry.Operation.output

An `Operation level layers rest` is a push of a perfect crumb of the given level, or a pop that is known to succeed. Its `cost` is `pushCost` or `popCost` of the layers before it. `input bottom` and `output bottom` are the physical trees at the boundaries, with the same conventions as for Vanilla: a push starts with the new node above the decoded stack, and a pop ends with the popped node above the rest.

@decl PopTart.Cherry.Program PopTart.Cherry.Program.cost PopTart.Cherry.Program.Realizes

A `Program level layers rest n` is a sequence of $n$ operations from `layers` to `rest`, and its cost is the sum. `Realizes bottom program` says that each operation is realized by a pointer trace from its input to its output, root to root, of exactly its cost. The bottom slot stays fixed, and any transfer between operations is left to the caller.

### Lemma 2: amortized cost, worst case and height

**Theorem (one push, one pop).** Let `layers` be valid at some level. Pushing a perfect crumb of that level gives valid layers, puts the crumb's slots in front of the fringe, is realized by a trace of `pushCost` instructions, and has amortized cost at most $10$. If `layers` is nonempty, a pop succeeds and returns a perfect crumb of that level and valid layers, removes the crumb's slots from the front of the fringe, is realized by a trace of `popCost` instructions, and has amortized cost at most $10$.

@decl PopTart.Cherry.Results.push PopTart.Cherry.Results.pop

Amortized cost means actual cost plus the potential after, which is at most $10$ plus the potential before.

@decl PopTart.Cherry.Results.operation_trace

Each operation's trace can be run under any context, so a Cherry pop-tart may sit anywhere in a larger tree.

**Theorem (sequences).** A program of $n$ operations from valid layers ends in valid layers, is realized, and costs at most $10n$ plus the initial potential minus the final one. From the empty stack, the total cost is at most $10n$.

@decl PopTart.Cherry.Results.sequence PopTart.Cherry.Results.empty_sequence

`empty_sequence` writes the bound as $n + \text{cost} \le 11n$, that is, $\text{cost} \le 10n$. It holds at every level and for every bottom slot. This is the "good" half of Lemma 2.

The height bound counts slots. A layer at index $j$ holds at least one $j$-crumb, with $2^j$ slots, so there are at most $\log_2 L$ layers.

@decl PopTart.Cherry.Results.layer_population PopTart.Cherry.Results.height_log

`layer_population` is the counting statement at any level, $2^{\ell + h} + 1 \le L + 2^{\ell}$ for $h$ layers starting at level $\ell$. `height_log` specializes it to level $0$: $h \le \log_2 L$.

**Theorem (depth).** In a Cherry pop-tart with $L$ slots, every slot has depth at most $4\log_2 L$. In an ordinary Cherry pop-tart with $n$ nodes, every node has depth less than $4\log_2(n+1)$.

@decl PopTart.Cherry.Results.depth_log PopTart.Cherry.Results.key_depth

For the proof: a slot in layer $j$ lies below at most $3(j+1)$ spine nodes and $j$ crumb levels, and $j < h \le \log_2 L$. The key version uses [[PopTart.WeightedTree.Results.empty_count]]: an ordinary pop-tart with $n$ keys has $n+1$ slots.

**Theorem (worst case).** In a Cherry pop-tart with $L$ slots, the next push costs at most $10\log_2 L$ instructions and the next pop at most $6\log_2 L$.

@decl PopTart.Cherry.Results.worst_case

A carry or borrow can ripple through every layer, but there are at most $\log_2 L$ of them. The bound refers to the stack before the operation, and to its number of slots, not to weights or payload sizes.

### Lemma 3: increasing weights

For the weighted version, each push must weigh at least as much as everything already in the stack.

@decl PopTart.Cherry.Operation.Increasing PopTart.Cherry.Program.Increasing

A push is `Increasing` when its crumb is ordered and each of its slots weighs at least as much as each slot of the current stack, the bottom included. At level $0$ the crumb is a single slot, so the condition says that the new weight is at least the current maximum. Pops are unrestricted. The comparison is with the slots present at the time of the push, not with all slots ever pushed. The paper's condition, "new leaves are added with increasing weights", implies it, provided the bottom slot is no heavier than the first push.

@decl PopTart.Cherry.Results.push_ordered PopTart.Cherry.Results.push_leaf_ordered PopTart.Cherry.Results.pop_ordered PopTart.Cherry.Results.operation_ordered PopTart.Cherry.Results.sequence_ordered

These lemmas show that the ordered invariant survives. Pushing an ordered, dominating crumb onto an ordered stack gives an ordered stack, and `push_leaf_ordered` is the single-slot case. A pop leaves an ordered crumb and an ordered rest. `operation_ordered` and `sequence_ordered` lift this to increasing operations and programs. Carries and borrows never reorder slots: they only regroup the fringe, as [[PopTart.Cherry.Results.push]] and [[PopTart.Cherry.Results.pop]] state.

**Theorem (depth by rank).** In a Cherry pop-tart, the $k$-th slot of the fringe has depth at most $3 + 4\log_2 k$.

@decl PopTart.Cherry.Results.depth_rank

The first slots of the fringe are in the first layers. The $k$-th slot is in a layer of index at most $\log_2 k$, which gives the bound as in `depth_log`. This needs no weights at all.

**Theorem (Lemma 3, depth).** In a Cherry pop-tart whose fringe is ordered, a slot of weight $w > 0$ at depth $d$ satisfies $d \le 3 + 4\log_2(W/w)$. If its payload is nonempty, the pointer machine reaches it from the root in exactly $d$ instructions.

@decl PopTart.Cherry.Results.weighted_depth PopTart.Cherry.Results.weighted_access

This combines `depth_rank` with [[PopTart.WeightedTree.Results.ordered_prefix_mass]]: the $k$-th slot of an ordered fringe has $k \le W/w$.

**Theorem (Lemma 3).** Start from the empty Cherry pop-tart, with a single bottom slot of nonnegative weight. After any increasing program of $n$ single-slot operations, the stack is valid and ordered, every operation was realized, the total cost is at most $10n$, and every slot of weight $w > 0$ has depth at most $3 + 4\log_2(W/w)$.

@decl PopTart.Cherry.Results.weighted_sequence

The depth bound is stated for the final stack. It holds at every intermediate moment as well, since the intermediate stacks are again valid and ordered and `weighted_depth` applies to them. Lemma 3 does not claim a worst-case bound; `worst_case` above gives one anyway, in terms of the number of slots.

## Located slots

A slot's depth bounds the cost of reaching its payload. The heavy-path structures also need the *rank* of the payload's keys in the physical tree, to say how deep a given key is. A located slot records it.

@decl PopTart.WeightedTree.fringeSpan PopTart.WeightedTree.LocatedSlot

`fringeSpan slots` counts the physical keys spanned by a list of slots: each payload's keys plus the separator that follows it. `LocatedSlot t subtree weight offset depth` is a `SlotAt` witness that also records `offset`, the number of keys of `t.tree` before the payload in inorder. Going right past a separator adds the left subtree's keys and the separator itself, as in [[Pointer.offset]].

@decl PopTart.Located.Results.fringeSpan_append PopTart.Located.Results.fringeSpan_fringe

The span is additive, and the span of a whole fringe is one more than the number of keys, since the last slot has no separator after it.

@decl PopTart.Located.Results.forget PopTart.Located.Results.fits PopTart.Located.Results.split PopTart.Located.Results.locate_split PopTart.Located.Results.context

Every located slot is a slot (`forget`), and its payload fits inside the tree (`fits`). Its offset is the span of the fringe entries before it (`split`), and conversely every entry of the fringe is a located slot with that offset (`locate_split`). `context` is the zipper path to the slot, of length `depth` and with [[Pointer.offset]] equal to `offset`.

**Theorem (key depths in a located slot).** If a located slot holds `subtree` at depth $d$ and offset $o$, the key $o + x$ of the physical tree, for $x$ a key of `subtree`, has depth $d + \mathrm{depth}_{\mathit{subtree}}(x)$. The keys just after and just before the payload, when they exist, have depth less than $d$.

@decl PopTart.Located.Results.key_depth PopTart.Located.Results.successor_depth PopTart.Located.Results.predecessor_depth

The keys at $o + |\mathit{subtree}|$ and $o - 1$ are the separators adjacent to the slot, which are ancestors of it. In a heavy-path stack these separators are the path nodes themselves, and the payloads are the off-path subtrees. The bounds [[HeavyPath.Paired.Results.lower_key_bound]] and [[HeavyPath.Paired.Results.lower_separator_bound]] on the paired stacks of [Chapter 46](heavy-paths.html) are these lemmas combined with Chocolate's weighted depth bound. Chocolate's interruption lemmas ([Chapter 45](chocolate.html)) use located slots in the same way, to bound key depths in the middle of an operation.

## Mirrored pop-tarts

The paper notes that every pop-tart can be flipped to accept pushes in increasing key order. In a heavy path, the ancestors larger than the endpoint arrive in increasing order. The library does not define a second family of pop-tarts. It stores such a stack as an ordinary one, in reversed coordinates, and reflects it when it is decoded.

@decl PopTart.WeightedTree.mirror

`mirror` swaps the two children of every separator and reflects every payload with [[Tree.mirror]], keeping the weights. The physical tree of the mirror is the mirror image of the physical tree. To keep a payload in its original orientation in the reflected stack, the caller stores its reflection: [[HeavyPath.Paired.Stacks.push]] pushes `r.erase.mirror` onto the upper stack, and decoding the stack mirrors it back.

@decl PopTart.Mirror.Results.involution PopTart.Mirror.Results.tree PopTart.Mirror.Results.mass PopTart.Mirror.Results.nonnegative PopTart.Mirror.Results.fringe PopTart.Mirror.Results.slot

Mirroring is an involution and commutes with taking the physical tree. It preserves mass and nonnegativity. It reverses the fringe and reflects each payload. It maps a slot to a slot with the reflected payload, the same weight and the same depth. Every depth bound of a pop-tart therefore holds for its mirror image, with the same constants. This is how the paired stacks obtain their bounds for the upper stack, such as [[HeavyPath.Paired.Results.upper_depth]]. Pointer traces are transferred the same way: a mirrored trace is a trace of the same length ([[Pointer.Mirror.Results.trace]], [Chapter 12](replay.html)), and the paired stacks obtain their upper pops from their lower ones by it.
