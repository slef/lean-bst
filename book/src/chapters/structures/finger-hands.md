# Finger hands

The multi-finger model of [Chapter 10](fingers.html) keeps several persistent fingers in one BST. Each instruction moves one finger to a neighbouring node or rotates at it, and every other finger stays on its key. The pointer machine of [Chapter 6](pointer.html) has a single cursor, which starts at the root for every request. A *finger hand* lets the single cursor simulate the fingers. It shapes the BST so that every finger is a constant number of steps from the root, for a fixed number of fingers, and it maintains that shape as the fingers move and rotate.

The library uses the hand with a single finger. Theorem 6 of the lazy finger paper [@bose2016] compares dynamic BSTs with static trees searched by a lazy finger. Its formal counterpart, [[LazyFinger.Dynamic.Results.optimal]] in [Chapter 15](lazy-finger-hierarchy.html), says that from any initial tree on $n$ keys, some pointer-machine execution serves the whole request sequence at cost at most $16n + 464\,\mathrm{OPT}$, where $\mathrm{OPT}$ is the cost of the best static tree searched with a lazy finger. The execution is an offline witness: it is chosen knowing the sequence. The proof runs the lazy finger as a one-finger execution of the multi-finger model, and simulates that execution with a hand. The central proof-file theorem is `Hand.one_finger_execution` (in `Structures/FingerHand/Packed/Simulation/Execution.lean`):

> Let $t$ be a nonempty tree, and suppose a multi-finger execution with $k$ fingers, all starting at the root of $t$, serves a request sequence at cost $C$. Then the pointer machine serves the same sequence from the same tree $t$, at cost at most $(344 + 60(k+1))\,C$.

Here $C$ is the multi-finger cost: one unit per request plus one per instruction. With $k = 1$ the factor is $464$, the constant of [[LazyFinger.Dynamic.Results.same_tree]]. The overhead grows linearly with the number of fingers. That is enough for the lazy finger, but it is weaker than an overhead independent of $k$.

::: note Do you need this section?
No theorem statement of the reading interface mentions a hand, and no headline result has these definitions on its reading path. They are shown so that the proof of [[LazyFinger.Dynamic.Results.optimal]] can be followed in the source. A reader who only wants to check Theorem 6 can stop at its statement in [Chapter 15](lazy-finger-hierarchy.html). The building blocks, BST deques and tendons, are in [Chapter 34](bst-deques.html). Everything here lives in `Structures/FingerHand`. The theorems quoted by name in plain code are internal to the library.
:::

## Overview

Three trees are involved:

- The *reference tree* is the tree of the multi-finger execution, [[Multifinger.State]]`.tree`. Its fingers are inorder ranks.
- The *skeleton* is a small labelled tree of reference keys: the fingers, the reference root, and the branching vertices between them, with every other vertex contracted away. It has at most $2(k+1)$ vertices.
- The *physical tree* is the tree that the pointer machine actually holds. It has the same keys in the same inorder as the reference tree, but a different shape.

The physical tree is built from the skeleton. Each skeleton vertex, a *pseudofinger*, is a real node. A skeleton edge stands for a reference path, possibly very long, and that path is stored as a tendon, which puts the lower endpoint at physical depth at most four. The subtrees that contain no skeleton vertex, the *knuckles*, are kept exactly as they are in the reference tree. A pseudofinger is therefore at physical depth less than $5$ times the number of skeleton vertices, and the cursor reaches any finger and returns to the root in fewer than $20(k+1)$ instructions.

A multi-finger instruction changes the skeleton by a bounded amount. A move adds the destination to the skeleton and may make the source obsolete. A rotation acts on two skeleton vertices. The simulation of one instruction has three phases:

1. **Exposure.** Make the destination a pseudofinger, at most one new vertex. If it was inside a tendon, take it out with a tendon operation. If it was the root of a knuckle, split the knuckle.
2. **The change itself.** A move needs nothing more. A rotation also exposes the parent and rotates the two pseudofingers, a constant number of physical instructions, since both are exposed.
3. **Suppression.** Remove the vertex that is no longer a finger and no longer branches, by pushing it into a neighbouring tendon or merging it into a knuckle.

The tendon potentials pay for the amortized deque operations. Each phase costs a constant plus the travel through the hand, which is $O(k)$.

## The compressed skeleton

The skeleton is computed from a set of *marks*, the reference ranks to keep:

@decl RotationBST.FingerHand.compress

`compress marks t lo` reads `t` with inorder ranks starting at `lo`. A vertex is kept if it is marked, or if both of its compressed subtrees are nonempty. An unmarked vertex with marks on only one side is replaced by that side's compressed subtree, and a subtree without marks disappears. The result is the subtree of `t` spanned by the marks, with its unmarked unary vertices contracted. It keeps the inorder order and the ancestor relation of the surviving keys (`compress_sublist`, `marked_mem`), and its labels are global ranks. The vertex above the topmost branching point is not kept unless it is marked, which is why the root is added as a mark below.

@decl RotationBST.FingerHand.markedCount

`markedCount marks t lo` counts the marks that are actually ranks of `t`. Marks outside the interval do not count. The library proves that a nonempty compressed skeleton has fewer than $2\cdot$`markedCount` vertices, the usual bound for a tree whose leaves and unary vertices are all marked (`compress_size_invariant`).

@decl RotationBST.FingerHand.rootRank RotationBST.FingerHand.stateMarks RotationBST.FingerHand.ofState

`rootRank t` is the rank of the root, `l.size`. On the empty tree it is $0$, a totalized value. The marks of a multi-finger state are the finger positions together with the root, so fingers on the same key contribute a single mark. `ofState s` is the skeleton of the state. It has at most $2(k+1)$ vertices, whatever the size of the tree (`ofState_size`), and it contains every finger of a valid state (`ofState_finger`). Including the root as a permanent *anchor* means that the cursor, which starts at the root, enters the skeleton at its top.

@decl RotationBST.FingerHand.lowerPath RotationBST.FingerHand.upperPath

`lowerPath t lo x` lists the keys smaller than `x` on the search path to `x` ([[Tree.searchPath]]), from the root down, and `upperPath` the larger ones. These are the two monotone sequences that a tendon stores, described by keys. The proofs work with the zipper versions [[Tendon.lowerFringe]] and [[Tendon.upperFringe]] instead, and no theorem currently uses `lowerPath` or `upperPath`.

## Packed hands

The physical structure mirrors the skeleton:

@decl RotationBST.FingerHand.Hand

A hand is a `knuckle`, an untouched reference subtree stored as is, or a `node`, one pseudofinger. A node records `path`, the reference path from the pseudofinger up to its skeleton parent, as zipper frames, innermost first. That path consists of the contracted vertices, each with its hanging subtree. The node also records `tendon`, the deque representation of that path, and its two child hands. The path may be empty, when the skeleton parent is the reference parent.

@decl RotationBST.FingerHand.Hand.count RotationBST.FingerHand.Hand.reference RotationBST.FingerHand.Hand.tree RotationBST.FingerHand.Hand.labels

These four readings of a hand are what the proofs relate:

- `count` is the number of pseudofingers.
- `reference` is the reference subtree the hand stands for. It plugs the node's own subtree back into its path, so it uses only `path`, never `tendon`.
- `tree` is the physical tree. It uses only `tendon`: the node's own subtree becomes the bottom of the tendon's tree ([[Tendon.State.tree]]). The path is bookkeeping for the proofs; the physical tree does not depend on it.
- `labels lo` is the skeleton as a labelled tree, with global reference ranks. A pseudofinger's rank is `lo`, plus the offset of its path, plus the size of its left reference subtree. Knuckles contribute nothing.

@decl RotationBST.FingerHand.Hand.Valid RotationBST.FingerHand.Hand.potential

`Valid` asks that every tendon represent its path, in the sense of [[Tendon.State.Represents]]. On a valid hand the physical and reference trees have the same size and the same inorder ranks (`tree_size`). The potential of a hand is the sum of the potentials of its tendons.

### Building a hand

@decl RotationBST.FingerHand.Hand.extend RotationBST.FingerHand.Hand.build RotationBST.FingerHand.Hand.forState

`build marks t lo` follows `compress` case by case. A marked vertex becomes a pseudofinger with an empty path. An unmarked vertex whose subtrees are both knuckles stays inside one larger knuckle. If exactly one side contains marks, the vertex is pushed onto the incoming path of that side with `extend`. If both sides contain marks, the vertex branches and becomes a pseudofinger. `extend` rebuilds the tendon as a balanced [[Tendon.State.ofPath]] each time, which is fine for a specification but is not how the simulation maintains it. `forState s` packs a multi-finger state.

Two facts make the canonical hand a good starting point. Its skeleton is exactly `compress` (`build_labels`). And when every finger is at the root, as in [[Multifinger.initial]], the only mark is the root, the hand is one pseudofinger with two knuckles, its physical tree is the reference tree itself, and its potential is $0$ (`initial_tree`). So no startup reshaping is needed.

### The invariant

@decl RotationBST.FingerHand.Hand.Represents

`h.Represents s` is the invariant of the simulation:

1. every tendon represents its reference path (`Valid`),
2. the reference tree is exactly the multi-finger tree `s.tree`, and
3. the skeleton is exactly the compressed skeleton `ofState s`, labels included.

The deque states inside the tendons are not fixed: any valid state is allowed, and the potential accounts for their imbalance. Conditions 2 and 3 tie the hand to the simulated state precisely. All fingers are pseudofingers, and there are no extra pseudofingers, so the hand has at most $2(k+1)$ of them (`Represents.count`). Each pseudofinger costs at most five physical frames, one edge from its skeleton parent and at most four inside its tendon (`location`). The cursor therefore reaches finger $i$ and comes back in fewer than $10(k+1)$ instructions each way, by navigation alone (`Represents.visit`). This holds for every maintained hand, not only the canonical one.

## Editing inside a hand

The updates are local. A zipper over the hand locates the region being edited:

@decl RotationBST.FingerHand.Hand.ContextFrame

A context frame is an enclosing pseudofinger, with its path, its tendon and the sibling hand that is not being edited. As for [[Pointer.Frame]], the constructor names the side on which the edited region lies.

@decl RotationBST.FingerHand.Hand.Context.plug RotationBST.FingerHand.Hand.Context.Valid RotationBST.FingerHand.Hand.Context.pointer RotationBST.FingerHand.Hand.Context.referencePath RotationBST.FingerHand.Hand.Context.potential RotationBST.FingerHand.Hand.Context.count

`plug` rebuilds the whole hand, and `Valid` checks the tendons and siblings along the way. The two paths relate the edited region to the two trees. `pointer` is the physical zipper: for each enclosing pseudofinger, one frame for the edge into the region, then the at most four frames of its tendon's context. `referencePath` is the same position in the reference tree, through the full reference path of each enclosing vertex. `potential` and `count` add up what the enclosing frames hold. The proof lemma `Context.lift_trace` turns a local bound into a global one. A local trace with amortized cost $C$ lifts to the whole hand at cost $C + 10 \cdot$(number of frames), because the cursor travels down and back. In a maintained hand this is at most $C + 20(k+1)$ (`lift_in_state`).

@decl RotationBST.FingerHand.Hand.graft RotationBST.FingerHand.Hand.fork

`graft cs d f child` puts a new pseudofinger above `child`, with incoming path `cs`, tendon `d`, and the off-path sibling of frame `f` kept as a knuckle. `fork l r` is a pseudofinger with an empty incoming path and the canonical empty tendon. It is an *exposed* vertex, physically the parent of its children's trees.

@decl RotationBST.FingerHand.Hand.LocalRotation

A local rotation rotates two adjacent exposed pseudofingers, both with empty incoming paths, inside the region of an enclosing node with path `cs` and tendon `d`. The tendon and the three subhands `a`, `b`, `c` are unchanged. Physically this is a single rotation just below the bottom of tendon `d`, at depth at most four. It takes two instructions plus at most eight to go there and back (`LocalRotation.trace`). The labelled skeleton undergoes the same rotation (`LocalRotation.labels`), so all pseudofingers keep their ranks.

@decl RotationBST.FingerHand.Hand.Expansion

An expansion is a representation change that adds exactly one pseudofinger. Both hands are valid, the reference tree is the same, the count goes up by one, and, for every offset `lo`, the old skeleton's inorder list is a sublist of the new one. It is not an insertion into the BST: no key is added to the tree, only to the skeleton. Its five fields, `before_valid`, `after_valid`, `reference`, `count` and `keys`, are exactly these conditions. The proof files show that the new vertex is exactly one key (`Expansion.key_set`). Marking that key makes the expanded skeleton canonical for the enlarged mark set (`Expansion.mark_added`).

## Exposing a key

@decl RotationBST.FingerHand.Hand.Exposure

`Exposure before after key` is the contract of phase 1. The new hand is valid and stands for the same reference tree. It keeps every old pseudofinger, has at most one more, and has `key` among its pseudofingers. Unlike an expansion, an exposure may add nothing, when `key` already is a pseudofinger. The field names `valid`, `reference`, `keys`, `count` and `retained` are the five conditions.

The library proves exposure lemmas for each neighbour of a pseudofinger (in `Packed/Neighbors`):

- `expose_parent`: if the incoming path is nonempty, the parent is the innermost path node, and the tendon's `removeBottom` operation takes it out, at amortized cost at most $180$ plus navigation. If the path is empty, the parent already is the enclosing pseudofinger, at no cost.
- `expose_left`, `expose_right`: a child is the root of a knuckle, or the top of the child hand's path, or already a pseudofinger. The first case splits the knuckle into a pseudofinger and two smaller knuckles, which changes no pointer. The second uses `removeTop` on the child's tendon (`expose_root`).
- `expose_instruction`: for any legal multi-finger instruction, the destination of the moving finger can be exposed.

## Pruning the skeleton

When a finger leaves a key, the hand must lose the vertices that are no longer needed. These definitions describe, on labelled trees, which vertices go:

@decl RotationBST.FingerHand.join RotationBST.FingerHand.prune

`join` is the step of `compress` for one vertex. It keeps a marked vertex or a branching one, and contracts an unmarked vertex with an empty side. `prune marks t` applies it bottom up to a labelled tree, keeping its labels. It recomputes a skeleton for fewer marks from an existing skeleton, with no access to the reference tree. Two results justify this. If $a \subseteq b$ then `prune a (prune b t) = prune a t` (`prune_prune`). And if a hand's skeleton contains every mark of its reference interval, then pruning it gives exactly the compressed skeleton of the reference tree (`prune_labels`).

@decl RotationBST.FingerHand.Contracts

`Contracts s t` says that `t` arises from `s` by discarding subtrees and contracting paths. Surviving vertices keep their labels and their ancestor relations. Every hand's skeleton is a contraction of its labelled reference tree (`labels_contracts`). When the labels are distinct, any contraction that retains all the marks determines the exact compressed skeleton (`Contracts.project`). Distinctness matters here: without it, another occurrence of the same label could falsely witness that a mark was retained.

@decl RotationBST.FingerHand.lostMarks RotationBST.FingerHand.skeletonMass

These two quantities bound how much a skeleton shrinks. `lostMarks before after t` counts the vertices of `t` labelled by a mark of `before` that is not in `after`. `skeletonMass t` is the number of vertices plus one if `t` is nonempty; the extra unit pays for a component that disappears entirely. For $a \subseteq b$, removing the marks of $b \setminus a$ loses at most two units of mass per lost mark (`prune_mass_loss`). On distinctly labelled trees, removing one mark removes at most two skeleton vertices, however deep the reference tree is (`erase_size`).

@decl RotationBST.FingerHand.stationaryMarks

`stationaryMarks s i` is the root anchor together with every finger except finger $i$. When finger $i$ moves without changing the tree, the new marks are these stationary marks plus its new position (`step_stationary_marks`). A coincident finger, or the root anchor, at the old position keeps that key marked. The proof lemma `update_common_skeleton` then shows that the skeletons before and after the move are both prunings of one *joint* skeleton, marked with the old marks plus the new position. That joint skeleton has at most two more vertices than either of them.

@decl RotationBST.FingerHand.MarkedRotation

`MarkedRotation marks s t` is a rotation of the labelled reference tree, anywhere inside it, whose two participating keys are both marked. The enclosing vertices need not be marked. Compression commutes with such a rotation: the skeleton of the rotated tree is the rotated skeleton (`MarkedRotation.project`). This is why a finger rotation first marks its parent temporarily: once both endpoints are pseudofingers, the reference rotation is a [[Hand.LocalRotation]] of the hand.

## Suppression

Pruning says which vertices go. Suppression removes them one at a time, by steps the pointer machine can perform:

@decl RotationBST.FingerHand.Reduced

`Reduced marks t` is the normal form of a skeleton: every vertex is marked or has two nonempty children. Compressed skeletons are in this form.

@decl RotationBST.FingerHand.Suppress

`Suppress marks x s t` removes the single obsolete vertex `x` from `s`, without making any other vertex obsolete:

- `unaryLeft`, `unaryRight`: `x` has one nonempty child. Contract it. Physically, `x` joins a tendon, at the bottom of its own incoming tendon (`suppress_bottom_under`, using `Tendon.State.addBottom`) or at the top of its child's tendon (`suppress_top_under`, using `addTop`).
- `leafLeft`, `leafRight`: `x` is a leaf whose parent `y` is marked. Delete it. Physically, its two knuckles and the node itself merge into one knuckle, which changes no pointer and no potential (`demote_left`). The parent must be marked: an unmarked parent would become unary, and therefore obsolete as well.
- `inLeft`, `inRight`: the removal happens inside a subtree, and the enclosing vertices are kept.

`Suppress` is exactly the pruning it is meant to implement. If `s` is reduced for the marks plus `x`, `x` is not a mark, and the labels are distinct, then `prune marks s = t` (`Suppress.prune_eq`), and `t` is again reduced (`Suppress.reduced`).

## Simulating one instruction

The pieces combine as follows (in `Packed/Simulation`). Here $k$ is the number of fingers, and every bound is amortized: instructions plus the new potential, at most a constant plus the old potential.

- **A move** of finger $i$ from $x$ to a neighbour $y$ (`simulate_move`). `prepare_move` exposes $y$, giving a hand whose skeleton is canonical for the old marks plus $y$. If $x$ is still needed (it is another finger, the root anchor, or a branching vertex), the hand already represents the new state (`move_retained`). Otherwise `cleanup_obsolete` suppresses $x$. The physical step required for this is located from the instruction that moved the finger: going to a parent uses `suppress_up`, and going to a child uses `suppress_down_left` and its mirror image. The amortized cost is at most $324 + 40(k+1)$.
- **A rotation** at finger $i$ (`simulate_rotate_right`, `simulate_rotate_left`). The parent $p$ is exposed as a temporary mark. The two pseudofingers are rotated as a local rotation (`rotate_right_prepared`), which keeps the skeleton canonical because both keys are marked. Then `finish_rotation` drops the temporary mark on $p$, suppressing $p$ if it has become obsolete. At the root the anchor moves with the rotation, since the rotating finger becomes the new root (`rotation_marks_right`). The amortized cost is at most $344 + 60(k+1)$.

`simulate_step` takes the larger bound for all six instructions, and `simulate_trace` adds it up along a trace, with the potentials telescoping. For a request, `simulate_serves` simulates the instructions before the visit, navigates to the visiting finger and back in fewer than $10(k+1)$ instructions each way, and simulates the instructions after it. The request unit pays for that navigation. Over a whole execution, `simulate_execution` gives a [[Pointer.Execution]] whose cost plus the final potential is at most $(344 + 60(k+1))\,C$ plus the initial potential. The initial potential is $0$ when all fingers start at the root, which is `one_finger_execution`.

::: check
- The simulated execution starts from the same physical tree as the multi-finger one, and its final tree is the physical tree of the final hand. That tree has the same keys as the final multi-finger tree, but usually not the same shape.
- The hand is not rebalanced. The skeleton is laid out as it is, and its depth can be as large as its size, so navigating it costs $O(k)$. This is where the term $60(k+1)$ comes from.
- Planning is free, as everywhere in the pointer model. The bounds count pointer instructions and request units, and the simulation reads the multi-finger execution to decide what to do. The hand's reference paths and labels are bookkeeping and cost nothing.
:::
