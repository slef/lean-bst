# BST deques and tendons

A finger in a binary search tree may sit far below the root. The pointer machine of [Chapter 6](pointer.html) has a single cursor that starts at the root for every request, so to simulate a persistent finger it must reach the finger in a constant number of steps. The deep path from the root down to the finger must therefore be stored compactly. The *finger hand* of [Chapter 35](finger-hands.html) does this, and this section provides its building blocks.

A *tendon* is a long path of a reference tree, from a top node down to a bottom node, together with the subtrees hanging off it. In inorder, the path nodes that are smaller than the bottom increase as the path descends, and the nodes that are larger decrease. A tendon therefore stores the path as two sorted sequences, each kept in a *BST deque*. A BST deque is a binary search tree in which both the minimum and the maximum sit at depth one. Nodes can be pushed or popped at either end by a constant number of pointer instructions, amortized. In the tendon the bottom of the path sits at physical depth at most four, however long the path is, and the path can grow or shrink by one node at either end in amortized constant work.

The vocabulary of hands, tendons and knuckles comes from Demaine, Iacono, Langerman and Özkan, *Combining binary search trees* (2013), who simulate several fingers inside one BST. The library builds its own version of the construction, with explicit constants.

::: note Do you need this section?
No theorem statement of the reading interface mentions a deque or a tendon. These definitions are used in the proof of [[LazyFinger.Dynamic.Results.optimal]] ([Chapter 15](lazy-finger-hierarchy.html)), the part of Lazy Finger Theorem 6 stating that a dynamic BST does as well as the best static tree with a lazy finger, up to a constant factor and a startup term. They are never on the reading path of a headline result. Read this section to follow that proof, or as an example of how the library argues about pointer-machine traces. All definitions are in `Structures/BSTDeque` and `Structures/Tendon`. The cost lemmas quoted below are in the proof files of the same directories.
:::

## Overview

All the structures of this section are [[Pointer.Lazy.Skeleton]]s ([Chapter 6](pointer.html#reshaping-a-connected-region)). A skeleton is a connected region of *active* nodes whose leaves are *holes*, each holding an entire subtree that the structure never enters. The holes of a deque are called its *fringe*, and their inorder list is all a deque guarantees about its contents. The deque has no keys of its own. Its elements are tree nodes, and their order is the inorder of the tree they sit in.

Costs are counted as pointer instructions ([[Pointer.Trace]]) from the root configuration of the structure's tree to the root configuration of the result. Amortization uses an explicit potential, $32$ times the imbalance between the two halves of a deque. The bounds proved in the library are:

| operation | bound | lemma |
|---|---|---|
| deque push at either end | at most $2$ instructions; potential grows by at most $32$ | `pushFront_trace`, `pushFront_potential` |
| deque pop at either end | instructions plus new potential at most $80$ plus old potential | `popFront_trace`, `popBack_trace` |
| tendon: new node at the top | at most $54$ instructions; amortized at most $86$ | `Tendon.State.addTop_trace`, `addTop_amortized` |
| tendon: new node at the bottom | amortized at most $134$ | `Tendon.State.addBottom_amortized` |
| tendon: remove the top node | amortized at most $132$ | `Tendon.State.removeTop` |
| tendon: remove the bottom's parent | amortized at most $180$ | `Tendon.State.removeBottom` |

None of these constants depends on the size of the hanging subtrees or on the length of the path.

## Deques of nodes

A deque is two stacks on either side of a pivot. The stack of small nodes is a right spine whose left children are fringe subtrees, and the stack of large nodes is the mirror image:

@decl RotationBST.BSTDeque.frontSpine RotationBST.BSTDeque.backSpine

`frontSpine [g₁, g₂, …] gap` is a node with left hole `g₁` whose right child is `frontSpine [g₂, …] gap`. The list ends in the hole `gap` at the bottom on the right. `backSpine` stores its list from the maximum inward, so its first node is the largest, with the right hole `g₁`.

@decl RotationBST.BSTDeque.Deque

A nonempty deque `node front a b back` is a pivot node whose left subtree is `frontSpine front a` and whose right subtree is `backSpine back b`. The holes `a` and `b` are the two fringe subtrees adjacent to the pivot. An empty deque `empty gap` has no active node and only one hole.

@decl RotationBST.BSTDeque.Deque.skeleton RotationBST.BSTDeque.Deque.tree RotationBST.BSTDeque.Deque.size RotationBST.BSTDeque.Deque.fringe

For example, take `front = [g₁, g₂]` and `back = [h₁, h₂]`, and name the front nodes $n_1, n_2$, the pivot $p$ and the back nodes $m_1, m_2$. The inorder sequence of the tree is

$$
g_1\ n_1\ g_2\ n_2\ a\ \ p\ \ b\ m_2\ h_2\ m_1\ h_1 .
$$

The pivot is the root, the minimum $n_1$ is its left child and the maximum $m_1$ is its right child. In general the $i$-th smallest front node is at depth $i$, so a deque is fast only at its two ends. `size` counts the active nodes, `front.length + 1 + back.length`, and `fringe` lists the holes in inorder, `front ++ [a, b] ++ back.reverse`, one more than the size. The library proves `skeleton.size = size` and `skeleton.fringe = fringe` (in `Shape.lean`).

@decl RotationBST.BSTDeque.Deque.potential RotationBST.BSTDeque.Deque.balance

The potential is $32\,|\,|\mathit{front}| - |\mathit{back}|\,|$. `balance xs` rebuilds a deque from a fringe list: the first $k = \lfloor(|xs| - 2)/2\rfloor$ holes go to the front, the next two become `a` and `b`, and the rest go to the back, reversed. Both stacks then have nearly equal length, and `balance_potential` proves that the result has potential at most $32$. On a one-element list `balance` returns an empty deque. The empty list is totalized to `empty .nil`, a case the operations never reach.

## Pushing and popping

@decl RotationBST.BSTDeque.Deque.pushFront RotationBST.BSTDeque.Deque.pushBack RotationBST.BSTDeque.Deque.popFront RotationBST.BSTDeque.Deque.popBack

The node being pushed comes from the enclosing structure. Before `pushFront g`, the new node is the *parent* of the deque, with left subtree `g` and the deque as its right subtree. In the tree `.node g q.tree` it is the root, and it is smaller than every node of the deque. Two instructions, `downRight` and `rotateRightChild`, rotate the pivot above it, and the new node becomes the first node of the front spine (`pushFront_trace`). Pushing onto an empty deque costs nothing: the tree `.node g a` already has the shape of `.node [] g a []`.

A pop exposes the minimum as the parent of the remaining deque and returns its left hole. When the front stack is nonempty, its first node is the pivot's left child, and `downLeft`, `rotateLeftChild` bring it to the root. When the front stack is empty, the pivot itself is the minimum. `popFront` then rebuilds the rest with `balance`, and the proof realizes the change of shape by the reshaping theorem [[Pointer.Lazy.Results.reshape]], at most $16$ instructions per node. That linear cost is paid by the old potential: the back stack has as many nodes as the imbalance it creates. The result is `popFront_trace`:

> If `q.popFront = some (g, r)`, a pointer trace of $k$ instructions turns `q.tree` into `.node g r.tree`, root to root, with $k + \Phi(r) \le 80 + \Phi(q)$.

No node is deleted. A pop does not remove anything from the tree; it only changes which node the deque regards as its own. The popped node stays as the root, and the enclosing structure takes it over.

### Operations and programs

The library also packages these operations as a typed vocabulary:

@decl RotationBST.BSTDeque.Operation RotationBST.BSTDeque.Operation.input RotationBST.BSTDeque.Operation.output RotationBST.BSTDeque.Operation.Realizes

An `Operation q r` is a legal operation taking deque `q` to deque `r`. Pops carry a proof that they succeed, so popping an empty deque is not an operation. `input` and `output` are the trees at the boundary: a push receives its node as the root above the deque, and a pop leaves its node as the root above the result. `Realizes op cost` says that a pointer trace of exactly `cost` instructions goes from the input to the output, root to root.

@decl RotationBST.BSTDeque.Program RotationBST.BSTDeque.Program.Realizes

A `Program q s n` is a sequence of `n` operations, mixing both ends arbitrarily, from `q` to `s`. `Program.Realizes` adds up the realizations of its operations. Moving a node between the deque and its caller, between two operations, is the caller's business and is not part of this cost.

::: caveat Vocabulary without a theorem
At present no theorem of the library mentions `Operation.Realizes` or `Program.Realizes`. The per-operation bounds are proved directly on the trees, in `pushFront_trace`, `pushBack_trace`, `popFront_trace` and `popBack_trace` (in `Structures/BSTDeque/Operations.lean`), and the tendons below use those. Summing these bounds would show that every program of $n$ operations from a deque of potential $\Phi$ is realizable with at most $80n + \Phi$ instructions, but the library does not state this.
:::

## The two boundary slots

A tendon grafts its bottom subtree into the extreme holes of its deques. These are the leftmost and rightmost fringe slots:

@decl RotationBST.BSTDeque.Deque.minGap RotationBST.BSTDeque.Deque.maxGap RotationBST.BSTDeque.Deque.withMin RotationBST.BSTDeque.Deque.withMax

`minGap` is the first hole in inorder, the left hole of the minimum, or the hole `a` when the front stack is empty. `withMin q g` replaces that one hole by `g`, without moving any active node. `maxGap` and `withMax` are the mirror images. The proof files show that `withMin` and `withMax` change neither the size nor the potential, and only the extreme entry of the fringe.

@decl RotationBST.BSTDeque.Deque.minContext RotationBST.BSTDeque.Deque.maxContext

`minContext q` is the zipper path ([[Pointer.Frame]], innermost first) from the minimum slot up to the root of the deque, and `maxContext` the path from the maximum slot. Each has at most two frames, because the extreme nodes are at depth one. The library proves that plugging the slot's contents back in gives the deque's tree, `Pointer.plug q.minContext q.minGap = q.tree`, and that the offset of the minimum slot is $0$. A subtree grafted into a boundary slot is therefore reachable from the deque's root in at most two moves.

## Tendons

A tendon represents a path of the reference tree, given as a zipper path `cs`, innermost first: `cs.head` is the frame of the bottom node's parent. A frame `.right l` is an ancestor *smaller* than the bottom subtree, whose left subtree `l` hangs off the path; a frame `.left r` is a *larger* ancestor with hanging right subtree `r`. The subtrees hanging on each side, in inorder, are:

@decl RotationBST.Tendon.lowerFringe RotationBST.Tendon.upperFringe

`lowerFringe cs` lists the hanging subtrees that precede the bottom in inorder, from the top of the path down to the bottom, and `upperFringe cs` those that follow it, from the bottom up. Both orders are inorder. The path itself is not stored in this form: only the two sides are, and their interleaving along the path is lost.

@decl RotationBST.Tendon.State

A tendon state is a pair of deques. `lower` holds the path nodes smaller than the bottom and `upper` those larger than it. The bottom subtree is grafted into the maximum slot of `lower` and the minimum slot of `upper`, so the values stored in these two slots are placeholders.

@decl RotationBST.Tendon.State.context RotationBST.Tendon.State.tree RotationBST.Tendon.State.skeleton

`d.tree bottom` is the physical tree. The bottom subtree goes into the minimum slot of the upper deque, and that whole deque goes into the maximum slot of the lower deque. The root is the lower deque's pivot. `context` is the zipper path of the bottom: at most two frames in the upper deque, then at most two in the lower deque. So the bottom is at depth at most four, whatever the length of the path (`context_length`). `skeleton` is the same tree as a skeleton whose active nodes are exactly the path nodes, with `bottom` left as a hole.

@decl RotationBST.Tendon.State.potential RotationBST.Tendon.State.Represents

`Represents d cs` is the representation invariant. The lower deque's fringe, without its last slot, is `lowerFringe cs`, and the upper deque's fringe, without its first slot, is `upperFringe cs`. So the deques have exactly as many nodes as the path has smaller and larger ancestors. The physical tree has the same nodes, in the same inorder, as the path itself, and the bottom subtree keeps its global rank (`represents_offset`). The shape inside each deque is arbitrary, which is what lets the operations work lazily. The reference path `cs` is not recoverable from `d`, since the deques do not record how the two sides interleave. Whoever needs `cs`, such as the finger hand, keeps it as separate bookkeeping.

@decl RotationBST.Tendon.State.ofPath

`ofPath cs` is a balanced representation of a path, built with `balance` from the two fringe lists, with `.nil` as the placeholder slot values. It represents `cs` and has potential at most $64$.

### Growing and shrinking a tendon

@decl RotationBST.Tendon.State.addTop RotationBST.Tendon.State.addBottom

`addTop d f` extends the path upward by the node whose frame is `f`. Before, that node is the parent of the tendon's tree; after, it is part of the tendon. A smaller node (`.right g`) becomes the new minimum of the lower deque, and a larger node (`.left g`) the new maximum of the upper deque. The upper deque sits inside the lower one, so reaching its maximum first takes a short exchange: the lemma `lower_exchange` reshapes the at most three nodes around the lower deque's maximum slot, at most $48$ instructions. `addTop_represents` proves that the result represents `cs ++ [f]`, and `addTop_trace` that the whole update takes at most $54$ instructions.

`addBottom d f` extends the path at the other end. Here the old bottom node joins the tendon, and one of its children becomes the new bottom. Its hanging subtree `g` fills the slot that the bottom used to occupy (`withMax g` or `withMin g`), and the node is pushed as the new innermost element with a fresh placeholder slot. The result represents `f :: cs`, at amortized cost at most $134$.

The reverse operations are proved as lemmas. They have no definitions of their own, because the resulting state is produced by the proof:

- `removeTop`: if `d` represents `cs ++ [f]`, some `e` represents `cs`, and the top node is expelled to become the root above the tendon, `Pointer.plug [f] (e.tree bottom)`, at amortized cost at most $132$.
- `removeBottom`: if `d` represents `f :: cs`, some `e` represents `cs`, and the bottom's parent leaves the tendon to become the new bottom endpoint, `e.tree (Pointer.plug [f] bottom)`, at amortized cost at most $180$.

All four operations touch only the extreme slots of the deques and the at most four frames above the bottom. The rest of the path and every hanging subtree stay in place.

## Where tendons are used

In a finger hand ([Chapter 35](finger-hands.html)), every edge of the compressed skeleton of the fingers is a tendon. When a finger moves, a skeleton vertex may need to appear in the middle of a tendon or disappear into one. The operations above perform these changes at the ends of the tendon, and the potentials of all tendons together pay for the occasional rebalancing.
