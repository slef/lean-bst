# Chocolate pop-tarts

A *pop-tart* ([Chapter 44](pop-tarts.html)) is a binary search tree that implements a stack. A new node is pushed as the parent of the current root, with the old stack as its right child, and a pop removes the root's left fringe slot. Between operations the structure may rebalance itself with pointer moves and rotations, and the finger must end at the root again. The Vanilla pop-tart does nothing, and keeps a slot of weight $w$ near the root only if every new slot outweighs all older ones. The Cherry pop-tart is a 2–4 tree turned sideways, and handles unit weights or weights that increase along the stack.

The *Chocolate pop-tart* of Bose, Collette, Fagerberg and Langerman handles arbitrary weights. It is the building block of their deamortization: each heavy path of the simulated tree is stored as two Chocolate pop-tarts, whose slots are the subtrees hanging off the path, weighted by their sizes. Its Lemma 4 says that the structure is *crazy good*: $O(1)$ amortized and $O(\log n)$ worst-case time per push and pop, and every slot of weight $w$ at depth $O(\log(W/w))$, where $W$ is the total weight. This chapter formalizes that lemma with explicit constants, and two refinements that the later chapters need: operations that can be *interrupted* after any instruction with bounded intermediate depths, and in-place replacement of the *top* slot.

```headline chocolate-pop-tart
title: The Chocolate pop-tart is crazy good
source: Bose, Collette, Fagerberg and Langerman, *De-amortizing binary search trees* (2012)
theorems: PopTart.Chocolate.Results.push PopTart.Chocolate.Results.pop PopTart.Chocolate.Top.Results.hasTop_of_fringe PopTart.Chocolate.Results.weighted_sequence PopTart.Chocolate.Results.operation_worst_case

Start a Chocolate pop-tart from a single bottom slot of nonnegative weight. Run any sequence of $n$ operations, each either a push of one new fringe slot (an arbitrary payload subtree with an arbitrary nonnegative weight) or a pop, which is available whenever the stack holds at least two slots. Then:

- **Stack semantics.** Every state is valid. A push prepends the new slot to the inorder sequence of weighted slots, and a pop exposes the first slot under a separator at the root and leaves the rest.
- **Local pointer operations.** The rebalancing of each operation is a pointer-machine trace of exactly $\mathrm{cost}(op)$ moves and rotations, from the root of the stack back to its root, and it exists below any surrounding context: the stack may sit anywhere inside a larger tree.
- **Amortized cost.** $\mathrm{cost}(op) + \Phi' \le 20 + \Phi$ for a potential $\Phi \ge 0$, and from the initial single slot, $n + \sum \mathrm{cost} \le 21\,n$.
- **Worst-case cost.** Each operation on a stack with $N$ fringe slots has $1 + \mathrm{cost}(op) \le 7 + 14\log_2 N$.
- **Weighted depth.** After the sequence, every slot of weight $w > 0$ is at depth at most

$$7 + 7\log_2 \frac{W}{w},$$

where $W$ is the total weight of the slots.

This is Lemma 4 of the paper. The paper's depth bound is $6 + 7\log(W/w)$; the Lean constant is one larger. The cost of an operation counts only the rebalancing: placing the caller's new separator on a push, and removing the exposed one on a pop, belong to the caller, which is why the bounds add $1$ per operation. Weights live on the fringe slots only; separators weigh nothing. A slot of weight $0$ is allowed but gets no depth bound.
```

::: note Do you need this chapter?
Only if you want to follow the deamortization proof into its data structures. The headline results of [Chapter 37](deamortization.html) and [Chapter 38](combined-finger.html) state costs of online algorithms, and no pop-tart appears in their statements. The heavy-path representation of [Chapter 46](heavy-paths.html) to [Chapter 49](finger-histories.html) uses the operations and bounds of this chapter, mostly through [Section 45.6](#interrupted-operations) and [Section 45.7](#the-top-slot). The definitions are in `Structures/PopTart/Chocolate/Definitions/Abstract.lean` and `Top/Definitions/Abstract.lean`; the theorems are in `Chocolate/Abstract.lean`, `Interruption/Abstract.lean` and `Top/Abstract.lean`.
:::

## Overview

The pop-tarts of this book work on a [[PopTart.WeightedTree]] ([Chapter 44](pop-tarts.html)). Its `node`s are the separators that the pop-tart rearranges. Its `leaf`s are *fringe slots*, each carrying a payload subtree and a real weight. The pop-tart never looks inside a payload. In the paper a slot is an empty leaf. In the heavy-path application it is an entire subtree hanging off the path, moved as a block. The *mass* of a weighted tree is the total weight of its slots, and a *crumb of level $i$* is a [[WeightedTree.Perfect]] tree of height $i$, with $2^i$ slots.

Like the Cherry pop-tart, the Chocolate pop-tart cuts the right spine into *layers*, numbered $0, 1, 2, \dots$ from the root. Layer $i$ of the paper consists of

- one to three **regular nodes**, each with an $i$-crumb as its left child;
- then a **next node**, whose left child is layer $i+1$ and whose right child is the **icing** of layer $i$.

The last layer has no next node: zero to three regular nodes, followed directly by its icing, and zero regular nodes only if the icing is a single $i$-crumb.

```
layer i:   r ─ r ─ r ─ next ─ icing ─ … ─ (bottom crumb)
           │   │   │    │       │
           c   c   c  layer   frozen
                       i+1    blocks
```

Here every horizontal edge is a right child, every vertical edge a left child, and `c` is an $i$-crumb. The icing is a Vanilla pop-tart, a plain right spine, whose slots are *frozen* subtrees of the Chocolate pop-tart. Two invariants hold:

- **Structural invariant**: the layer shapes just described.
- **Thick-icing invariant**: the mass of layer $i+1$ is strictly smaller than the mass of the icing of layer $i$.

A **push** adds a regular node to layer $0$. If a layer now has four regular nodes, its last two crumbs are joined by a rotation into an $(i+1)$-crumb, which is carried into layer $i+1$, as in a binary counter. Before the carry, the algorithm compares masses. If layer $i+1$ with the carried crumb would weigh at least as much as the icing of layer $i$, that layer is **frozen** instead: it is pushed, together with the next node above it, as one block onto the icing of layer $i$, without further rebalancing, and layer $i$ becomes the last layer. Since the block weighs at least as much as the icing below it, the icing stays a well-behaved Vanilla pop-tart. A **pop** removes the first regular node of layer $0$. If a layer runs out of regular nodes, it borrows an $(i+1)$-crumb from the layer below and splits it into two; a last layer instead **thaws** the top block of its icing.

The depth bound comes from the thick-icing invariant. Layer $i+1$ weighs less than its icing, so less than half of layer $i$: weight halves at every active layer. A frozen block sits in a Vanilla stack, so it is at depth $O(\log(W/W_{\text{block}}))$, and the layer frozen inside it was, when frozen, light relative to the block. An induction on the layers gives the $7\log_2(W/w)$ term.

## Layers and icing

@decl PopTart.Chocolate.Regulars PopTart.Chocolate.Regulars.attach PopTart.Chocolate.Regulars.Valid

[[Chocolate.Regulars]] holds the zero to three regular crumbs of one layer, top first. `attach tail` hangs them on a right spine above `tail`, each crumb as a left child. `Valid level` asks that each crumb be perfect of the given level, with nonnegative weights.

@decl PopTart.Chocolate.Layer PopTart.Chocolate.Icing

The two types are mutually inductive. A [[Chocolate.Layer]] is either `last regulars icing`, the last layer, or `next regulars child icing`, an active layer whose next node points to `child`, the next layer. An [[Chocolate.Icing]] is a Vanilla stack read from the top:

- `base crumb` is the bottom of the icing. For the whole pop-tart, the base of the last icing of level $0$ is the bottom slot of the initial empty stack.
- `solid crumb tail` is a frozen $(i+1)$-crumb on top of `tail`. It arises when the carried crumb alone already outweighs the icing, so there is no layer to freeze, only the crumb.
- `frozen carry old tail` is a frozen layer. It remembers the carried $(i+1)$-crumb `carry` and the old next layer `old` separately, rather than as one layer with four regular nodes. This is exactly the state before the carry, and thawing restores it.

@decl PopTart.Chocolate.Layer.decode PopTart.Chocolate.Icing.decode

`decode` is the physical tree as a weighted tree, so `stack.decode.tree` is the BST the pointer machine holds. A next node is `.node child.decode icing.decode`. A frozen block is the separator `.node carry old.decode`, and it hangs on the icing spine under the old next node of the frozen layer, as in the paper.

@decl PopTart.Chocolate.Layer.Valid PopTart.Chocolate.Icing.Valid

`Valid level` is the invariant at layer number `level`:

- A last layer has valid regulars and icing, and it has no regulars only if its icing is a single `base` crumb.
- An active layer has one to three regulars (`rs ≠ .zero`), a valid next layer at level `level + 1`, a valid icing, and the thick-icing inequality `child.decode.mass < icing.decode.mass`.
- A `base` crumb is perfect of the layer's level; a `solid` crumb is perfect one level higher and dominates the rest of the icing, `tail.decode.mass ≤ crumb.mass`.
- A `frozen` block keeps two certificates: the strict thick-icing inequality that held when the frozen layer was still active, `old.decode.mass < tail.decode.mass`, and the domination `tail.decode.mass ≤ carry.mass + old.decode.mass` that made it freeze. The first is needed when the layer is thawed, and both bound depths inside the block.

All weights are nonnegative. The whole pop-tart is valid at level $0$, where crumbs are single slots.

@decl PopTart.Chocolate.Icing.outer

`outer` views the icing as the Vanilla pop-tart of the paper: each frozen block, or solid crumb, becomes one slot of a [[PopTart.WeightedTree]] whose payload is the block's whole physical subtree and whose weight is its total mass. The physical tree and the mass are unchanged ([Section 45.5](#depth)). The view exists only to apply the Vanilla depth bound to the icing.

@decl PopTart.Chocolate.Layer.activeDepth

`activeDepth` is the number of active layers below the top one: the length of the chain of next nodes. Layers frozen inside icing do not count, since a push or pop never recurses into them.

## Push and pop

@decl PopTart.Chocolate.Layer.push PopTart.Chocolate.Layer.pushCost

`push new` follows the paper. With fewer than three regulars the new crumb is simply added. With three, the layer now has four, `new a b c`, and `b` and `c` are joined into the carried crumb `.node b c`:

- In a last layer, if `(.node b c).mass < icing.decode.mass`, the layer becomes active with a new next layer `.last .zero (.base (.node b c))`, holding the carried crumb as its icing and nothing else. Otherwise the crumb is frozen as `solid` onto the icing.
- In an active layer, if the next layer with the crumb would still be lighter than the icing, `(.node b c).mass + child.decode.mass < icing.decode.mass`, the crumb is pushed recursively into `child`. Otherwise the layer freezes `frozen (.node b c) child icing`, and the layer becomes `last`.

After an overflow, in every case, two regulars `new a` remain, so the layer's potential drops to $0$ ([Section 45.3](#potential-and-operations)). The comparison uses only masses that are already available. It is decided by `classical`, which is why `push` is `noncomputable`; nothing else is chosen classically.

`pushCost` is the exact number of pointer instructions of the rebalancing: $6$ for an overflow of a last layer, $8$ for a freeze, and $14$ plus the cost of the recursive push otherwise, which includes going back up to the root between the local rotations and the recursive carry. A push that does not overflow costs $0$: placing the new separator above the old root is the caller's step, not part of the pop-tart's work.

@decl PopTart.Chocolate.Icing.thaw PopTart.Chocolate.Icing.thawCost PopTart.Chocolate.Icing.popCost

`thaw` refills a last layer that has lost its regulars. A `base` crumb becomes the layer with no regulars. A `solid` crumb `.node b c` is split into two regulars `b c`. A `frozen` block is reactivated: its carry is split into two regulars, and the saved `old` layer becomes the next layer again. The physical change is one right rotation for `solid` and two for `frozen`, and `thawCost` (2 and 4) is the cost of thawing at the icing's own root. `popCost` (4 and 6) is the cost of the same thaw seen from the exposed separator of a pop, two moves more. The paper's thaw turns the frosted subtree into one regular node and a next node; the Lean version splits the carried crumb back into two regulars instead. No theorem of the reading interface mentions `thawCost`; the pop theorems use `popCost`.

@decl PopTart.Chocolate.Layer.HasTop PopTart.Chocolate.Layer.baseCrumb PopTart.Chocolate.Layer.pop PopTart.Chocolate.Layer.popCost

`HasTop` says that the top layer has a regular crumb, so that there is something to pop. `pop` removes the first regular crumb and repairs an emptied layer:

- a last layer with one regular thaws its icing;
- an active layer with one regular borrows from its next layer. If that layer is only a single base crumb (`baseCrumb`), the crumb is split into two regulars and the layer becomes last. Otherwise the next layer is popped recursively and the returned $(i+1)$-crumb is split into two regulars.

Like the other pop-tart operations, `pop` is totalized by `none` on shapes that the invariant excludes, such as a borrowed crumb that is a single slot. The `pop` theorem below shows that it succeeds on every valid stack with a top. `popCost` is $0$ unless the layer had a single regular, and $10$ plus the recursive cost for a recursive borrow.

## Potential and operations

@decl PopTart.Chocolate.Regulars.potential PopTart.Chocolate.Layer.potential PopTart.Chocolate.Icing.potential

The paper charges $1$ to every layer whose regular count is not $2$. The library charges $20$, enough for one rebalancing round trip in pointer instructions, to layers with one or three regulars, and nothing to layers with zero or two. A last layer with zero regulars is a single base crumb, which no operation repairs. Credits of frozen layers stay in the potential, through `Icing.potential`. When a frozen layer is thawed, its credit is therefore still there.

@decl PopTart.Chocolate.Pushes PopTart.Chocolate.Pushes.cost PopTart.Chocolate.Pushes.Realizes

[[Chocolate.Pushes]] `level stack rest n` is a history of `n` pushes from `stack` to `rest`, each of a perfect, nonnegative crumb of the given level, with every intermediate state determined by `push`. Its cost is the sum of the push costs. `Realizes` asks that each push be witnessed by a [[Pointer.Trace]] ([Chapter 6](pointer.html)) from the tree with the new separator on top to the rebalanced tree, at exactly its `pushCost`, with the cursor at the root at both ends. The theorems prove `Realizes`, rather than assuming it.

@decl PopTart.Chocolate.Operation PopTart.Chocolate.Operation.cost PopTart.Chocolate.Operation.input PopTart.Chocolate.Operation.output

An [[Chocolate.Operation]] is one push, of a perfect nonnegative crumb, or one pop, with a proof that `pop` succeeded. `input` and `output` are the trees at the operation's boundaries. A push starts from `.node new.tree stack.decode.tree`, the caller's separator above the old stack, and ends at the new stack. A pop starts at the stack and ends at `.node crumb.tree rest.decode.tree`, the popped crumb exposed as the left child of a root separator that the caller then takes away.

@decl PopTart.Chocolate.Program PopTart.Chocolate.Program.cost PopTart.Chocolate.Program.Realizes

A [[Chocolate.Program]] is a sequence of operations, chained by their states; `Realizes` asks for a trace of each operation, from its input to its output at its cost.

## Amortized cost

The single-operation theorems state everything about one push or pop.

**Theorem (push).** Let `stack` be valid at some level, and push a perfect, nonnegative crumb of the same level. Then the result is valid, its fringe is the new crumb's fringe followed by the old one, and its mass is the sum. Below any context `cs`, a trace of exactly `pushCost` instructions turns the tree with the new separator on top into the result. Finally, `pushCost` $+\,\Phi' \le 20 + \Phi$.

@decl PopTart.Chocolate.Results.push

**Theorem (pop).** Let `stack` be valid with a top. Then `pop` succeeds, with a perfect, nonnegative crumb of the stack's level and a valid rest. The stack's fringe is the crumb's followed by the rest's, its mass is their sum, and below any context `cs` a trace of exactly `popCost` instructions exposes the crumb. Finally, `popCost` $+\,\Phi' \le 20 + \Phi$.

@decl PopTart.Chocolate.Results.pop

The context `cs` in both theorems is what makes the operations *local*: the trace starts and ends with the cursor at the stack's root, wherever that root is in a larger tree, and the ancestors above it are the same at both ends. The heavy-path structure runs pop-tart operations deep inside the simulated tree this way.

@decl PopTart.Chocolate.Results.push_trace PopTart.Chocolate.Results.pop_trace PopTart.Chocolate.Results.layer_nonnegative PopTart.Chocolate.Results.icing_nonnegative

The trace exists for every push, valid or not (`push_trace`), and for every successful pop (`pop_trace`): the rebalancing rotations are legal on any shape that `push` or `pop` accepts. Validity is needed only for the fringe, mass and potential parts. A valid layer or icing has nonnegative weights.

@decl PopTart.Chocolate.Results.operation_valid PopTart.Chocolate.Results.operation_trace PopTart.Chocolate.Results.operation_amortized

The same three facts for an [[Chocolate.Operation]]: it preserves validity, it has a trace below any context, and its amortized cost is at most $20$.

**Theorem (sequences).** A program of $n$ operations from a valid state ends in a valid state, is realized by traces, and costs at most $20n + \Phi_0 - \Phi_n$. From a single base crumb, where $\Phi_0 = 0$, the cost plus one unit per operation is at most $21n$.

@decl PopTart.Chocolate.Results.push_sequence PopTart.Chocolate.Results.empty_push_sequence PopTart.Chocolate.Results.sequence PopTart.Chocolate.Results.empty_sequence

The `push_` versions are the special case of push-only histories. The $n$ added on the left of `empty_sequence` is the caller's unit per operation; the pop-tart's own cost is at most $20n$.

@decl PopTart.Chocolate.Results.layer_potential_bound PopTart.Chocolate.Results.icing_potential_bound

The potential is at most $20(N - 1)$ for a stack with $N$ fringe slots. So the credit stored in a pop-tart is linear in its size, and a structure that builds or discards pop-tarts can account for their potential explicitly.

## Depth

### The icing is a Vanilla pop-tart

@decl PopTart.Chocolate.Results.outer_tree PopTart.Chocolate.Results.outer_mass PopTart.Chocolate.Results.icing_vanilla

The Vanilla view of an icing has the same physical tree and the same mass, and it satisfies [[PopTart.Vanilla.Valid]]: each block weighs at least the rest of the icing below it. This is where the two domination inequalities of `Icing.Valid` are used.

@decl PopTart.Chocolate.Results.icing_depth PopTart.Chocolate.Results.icing_access

Hence a block of weight $w > 0$ is at depth at most $1 + \log_2(W/w)$ in the icing, $W$ being the icing's mass, as in Lemma 1 of the paper. `icing_access` also produces the pointer path: a trace of exactly that many moves from the icing's root to the block, with the matching context frames. The depth `depth` of a [[WeightedTree.SlotAt]] counts edges from the root of the weighted tree to the slot.

### Every slot of a layer

**Theorem (layer depth).** In a stack valid at level $i$, every fringe slot of weight $w > 0$ is at depth at most $i + 7 + 7\log_2(W/w)$, where $W$ is the stack's mass. In an icing valid at level $i$, every slot of the full physical icing, including the slots inside frozen blocks, is at depth at most $i + 3 + 7\log_2(W/w)$.

@decl PopTart.Chocolate.Results.layer_depth PopTart.Chocolate.Results.icing_leaf_depth

The two are proved together, by induction on the mutual structure, following the paper's three cases: slots in regular crumbs, slots in the next layer, and slots in the icing, where a frozen layer's old certificate `old.decode.mass < tail.decode.mass` plays the role of the paper's "otherwise the layer would have been frosted earlier". The paper's hypothesis is $i + 6 + 7\log(W_i/w)$; the Lean induction carries $i + 7$.

**Theorem (weighted depth).** In a stack valid at level $0$, every slot of weight $w > 0$ is at depth at most $7 + 7\log_2(W/w)$, and a pointer trace of exactly that length reaches it from the root.

@decl PopTart.Chocolate.Results.weighted_depth PopTart.Chocolate.Results.weighted_access

@decl PopTart.Chocolate.Results.weighted_push_sequence PopTart.Chocolate.Results.weighted_sequence

`weighted_sequence` is the combination used in the headline: a program of $n$ operations at level $0$ from a single base slot ends in a valid state, is realized, costs at most $20n$, and leaves every slot of positive weight at depth $7 + 7\log_2(W/w)$. Every prefix of a program is a program, so the depth bound holds after every operation.

::: caveat Compared with Lemma 4
- **Weights on slots only.** The paper gives every internal node weight $1$. Here [[PopTart.WeightedTree]] weighs only fringe slots, and separators count nothing. The heavy-path representation adds the weight of each path node to the weight of the slot beside it.
- **Zero weights.** Weights must be nonnegative. A slot of weight $0$ is allowed, and the heavy-path stacks start from a bottom slot of weight $0$, but the depth bounds assume `0 < weight`: Mathlib's $\log_2$ of $W/0$ would be $0$.
- **Constants.** The depth bound is $7 + 7\log_2(W/w)$ rather than the paper's $6 + 7\log(W/w)$. Amortized cost is $20$ pointer instructions per operation. The constants are not optimized.
- **Cost model.** Costs are exact instruction counts of a single-cursor [[Pointer.Trace]] from root to root, not $O(\cdot)$ bounds. The caller's separator step is not included.
:::

## Worst-case cost

The crumbs of layer $i$ have $2^i$ slots each, so the number of active layers is logarithmic in the number of slots, whatever the weights.

@decl PopTart.Chocolate.Results.icing_population PopTart.Chocolate.Results.active_population PopTart.Chocolate.Results.push_cost_active_depth

A valid icing of level $i$ has at least $2^i$ slots, since its base is an $i$-crumb. A valid stack at level $i$ with `activeDepth` $d$ has at least $2^{i+d}$ slots. And a push costs at most $14d + 6$, since it recurses at most once per active layer.

**Theorem (worst case).** On a stack valid at level $0$ with $N$ fringe slots, a push costs $1 + \mathrm{cost} \le 7 + 14\log_2 N$ and a pop $1 + \mathrm{cost} \le 7 + 10\log_2 N$.

@decl PopTart.Chocolate.Results.push_worst_case PopTart.Chocolate.Results.pop_worst_case PopTart.Chocolate.Results.operation_worst_case

$N$ is [[WeightedTree.leafCount]] of the stack before the operation, which counts slots, not nodes: at level $0$ it is one more than the number of separators. The bound for a pop is stated without assuming the pop succeeds, since `popCost` is defined anyway. `operation_worst_case` takes the larger constant for both kinds.

@decl PopTart.Chocolate.Results.uniform_height PopTart.Chocolate.Results.uniform_key_depth

With unit weights the depth bound becomes a height bound, $7 + 7\log_2 N$. If moreover every slot is an empty leaf, the pop-tart is an ordinary BST on its separators, and every key has depth less than $7 + 7\log_2(\text{size} + 1)$. This is the unweighted case of the paper, the Cherry guarantee of [Chapter 44](pop-tarts.html) recovered by the weighted structure.

## Interrupted operations

The deamortized algorithm of [Chapter 37](deamortization.html) cannot afford to run a whole push or pop at once whenever the simulation needs it. Its scheduler performs a bounded number of instructions per access, so a pop-tart operation is often stopped half-way, the tree is searched in that intermediate state, and the operation resumes later. Searches in the intermediate tree must still be fast. The theorems of this section make this precise. Each turns the trace of an operation into a concrete list of [[Multifinger.Opcode]]s, replayed with [[Multifinger.replay]] on one cursor ([Chapter 12](replay.html)), and bounds the depth of every key at *every* cut point.

Each theorem has the same shape. There is a list `ops` of exactly `cost` opcodes whose replay performs the operation, and for every `cut` the prefix `ops.take cut` replays to some intermediate configuration `middle`, from which the suffix `ops.drop cut` replays to the final one. The theorems differ in the depth bound for `middle.tree`, the whole tree in the intermediate state. Here [[Tree.depth]] is the depth of a key, given by its inorder rank, in the whole tree.

**Theorem (additive interruption).** On a stack valid at level $0$ with $N$ slots, below any context, the depth of every key at any cut point exceeds its depth before the operation by at most $6 + 14\log_2 N$ for a push and $6 + 10\log_2 N$ for a pop.

@decl PopTart.Chocolate.Interruption.Results.push_prefix PopTart.Chocolate.Interruption.Results.pop_prefix

`push_prefix` makes no assumption on `new`: the rebalancing of `push` does not depend on the pushed crumb's shape. The quantifier `∀ x` ranges over all naturals; for ranks outside the tree, [[Tree.depth]] is totalized to the length of the right spine, and the bound holds for those too.

**Theorem (multiplicative interruption).** Without any validity assumption, at every cut point every key has depth at most $4d + 8$, where $d$ is its depth before the operation.

@decl PopTart.Chocolate.Interruption.Results.push_depth_prefix PopTart.Chocolate.Interruption.Results.pop_depth_prefix

@decl PopTart.Chocolate.Interruption.Results.push_within PopTart.Chocolate.Interruption.Results.pop_within

The `within` forms state the same invariant, together with preservation of the size, as a [[Pointer.TraceWithin]]: a trace whose every intermediate tree satisfies a predicate. They are stated at the stack's root (empty context), in the form that [[Chocolate.Top.Results.replaceTop_within]] lifts below a top slot ([Section 45.7](#the-top-slot)). The heavy-path interruption proofs use these.

**Theorem (payload depth).** At level $0$, let a payload subtree occupy a slot of weight $w > 0$ at inorder offset `offset` of the stack, and let $x$ be a key of the payload at depth $d$ inside it. At every cut point of a pop, the key is at depth at most $d + 13 + 7\log_2(W/w) + 10\log_2 N$. For a push the key's rank is shifted by the new crumb and its separator, and the bound is $d + 14 + 7\log_2(W/w) + 14\log_2 N$.

@decl PopTart.Chocolate.Interruption.Results.pop_payload_prefix PopTart.Chocolate.Interruption.Results.push_payload_prefix

The slot is described by a [[WeightedTree.LocatedSlot]] ([Chapter 44](pop-tarts.html)), which records both its outer depth and the inorder rank of its first key. The traces here start at the stack's root, with no outer context.

**Theorem (weighted interruption).** With the same data, at every cut point the key is at depth at most $4d + 36 + 28\log_2(W/w)$ for a pop, and $4d + 40 + 28\log_2(W/w)$ for a push.

@decl PopTart.Chocolate.Interruption.Results.pop_weighted_prefix PopTart.Chocolate.Interruption.Results.push_weighted_prefix

These are the purely weighted bounds that a heavy path needs, with no $\log N$ term: a key inside a heavy subtree stays close to the root even in the middle of a rebalancing, independently of how many light slots the stack holds. The price is the multiplicative factor $4$ on the depth inside the payload.

**Theorem (uniform interruption).** With unit weights and empty slots, the ordinary unweighted pop-tart, every key at every cut point has depth less than $13 + 17\log_2 N$ during a pop and less than $14 + 21\log_2 N$ during the push of a new empty slot of weight $1$.

@decl PopTart.Chocolate.Interruption.Results.uniform_pop_prefix PopTart.Chocolate.Interruption.Results.uniform_push_prefix

## The top slot

In the heavy-path representation, the slot at the top of a pop-tart is the subtree next to the finger. The simulated algorithm changes that subtree, and its weight, without pushing or popping. The `Top` module supports this.

@decl PopTart.Chocolate.Layer.top PopTart.Chocolate.Layer.topTail PopTart.Chocolate.Layer.replaceTop

`top` is the first outer crumb: the first regular crumb, or, when the top layer has no regulars, the whole stack, which is then a single base crumb on a valid stack. `topTail` is the rest of the stack beyond the first separator, or `none` if there is no separator. `replaceTop new` replaces the top crumb and keeps every other piece of the representation. It is a change of representation only. The physical change of the subtree must be paid for by a trace, as `replaceTop_lift` below does.

@decl PopTart.Chocolate.Top.Results.decode_top PopTart.Chocolate.Top.Results.replaceTop_decode PopTart.Chocolate.Top.Results.replaceTop_top PopTart.Chocolate.Top.Results.replaceTop_tail PopTart.Chocolate.Top.Results.replaceTop_replaceTop

The physical stack is `top` alone or `.node top tail`. After `replaceTop new` it is the same with `new` in place of `top`. The tail is unchanged, and a second replacement overrides the first.

@decl PopTart.Chocolate.Top.Results.top_valid PopTart.Chocolate.Top.Results.replaceTop_valid PopTart.Chocolate.Top.Results.replaceTop_potential PopTart.Chocolate.Top.Results.replaceTop_mass PopTart.Chocolate.Top.Results.replaceTop_size

The top crumb of a valid stack is perfect and nonnegative. Conversely, replacing it by any perfect, nonnegative crumb of the same level keeps the stack valid and does not change the potential. At level $0$, any single slot qualifies, whatever its payload and weight. This works because the top crumb sits under a regular node, and no inequality of `Valid` involves the masses of regular crumbs. So the top slot's weight can rise or fall arbitrarily with no rebalancing, and the depth bounds then hold for the new masses. The mass and the size change by the difference between the two crumbs.

**Theorem (lifting a top change).** Let the old and new top trees be nonempty, and let a trace of cost $c$ turn the old top tree into the new one. Then a trace of cost at most $c + 2$ turns the whole stack into the stack after `replaceTop`. If every intermediate tree of the given trace satisfies the size-and-depth invariant $\mathrm{depth} \le f \cdot d + k$ (with $f \ge 1$) relative to the old top, then the lifted trace satisfies the same invariant relative to the whole stack.

@decl PopTart.Chocolate.Top.Results.replaceTop_lift PopTart.Chocolate.Top.Results.replaceTop_within

The $2$ is one move down to the top crumb and one move back up, needed only when there is a tail. The trees must be nonempty because the cursor must stand on a node.

@decl PopTart.Chocolate.Top.Results.hasTop_of_fringe PopTart.Chocolate.Top.Results.pop_front

At level $0$, a valid stack with at least two fringe slots has a top, so a pop is available whenever the stack holds more than its bottom slot. `pop_front` reads the pop off the fringe: if the fringe is `(subtree, weight) :: suffix` with `suffix` nonempty, then `pop` returns exactly that slot and a valid rest whose fringe is `suffix`, with amortized cost at most $20$. This is the form in which the heavy-path histories pop the slot next to the finger.
