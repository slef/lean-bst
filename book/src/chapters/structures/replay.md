# Replays, mirrors and detours

The pointer machine of [Chapter 6](pointer.html) and the command streams of [Chapter 10](fingers.html) are enough to *state* the results on combining search trees and on deamortization. Their *proofs* treat pointer computations as data. A computation is recorded as a list of instructions, replayed later on another cursor, or undone. A cursor leaves its work for a moment, visits a requested key, and comes back to exactly the configuration it left. A construction proved on the left side of a tree is transferred to the right side by mirroring. The depth of every key is tracked at every instruction boundary of a long computation, not only at its ends. And cursors move over trees whose nodes carry data: labels that travel with their nodes under rotations, payload words, and the interval of keys below each node, which lets a cursor find any key by looking only at the node it stands on.

This chapter collects these tools. It has no theorem of its own and no headline result. It is a toolbox, and most of its statements are lemmas used inside proofs. The table says which chapters use each part.

| Section | Lean modules | Used by |
|---|---|---|
| [Recorded instruction streams](#recorded-instruction-streams) | `Models/Multifinger/Program/Replay` | the emitted programs of deamortization ([Chapter 37](deamortization.html)) and of the combined finger bound ([Chapter 38](combined-finger.html)); the replay logs of ComboBST workers ([Chapter 34](combo-workers.html)); saving and restoring tree states ([Chapter 50](tree-buffers.html), [Chapter 51](snapshots.html)); interruptible pop-tarts and heavy paths ([Chapter 45](chocolate.html), [Chapter 47](recursive-heavy-paths.html), [Chapter 49](finger-histories.html)) |
| [Walks and detours](#walks-and-detours) | `Models/Pointer/Walk`, `Models/Pointer/Detour` | serving a request in the middle of pending work ([Chapter 37](deamortization.html)); requests during the heavy-path simulation ([Chapter 49](finger-histories.html)) |
| [Mirror images](#mirror-images) | `Models/Pointer/Mirror` | right-hand pop-tarts ([Chapter 44](pop-tarts.html)) and paired heavy paths ([Chapter 46](heavy-paths.html)) |
| [Depths along a computation](#depths-along-a-computation) | `Bounds/StaticTree/Trace`, `Models/Pointer/Invariant` | the bounded-depth simulation behind deamortization: Chocolate pop-tarts ([Chapter 45](chocolate.html)), heavy paths ([Chapter 46](heavy-paths.html) to [Chapter 49](finger-histories.html)) and the request window of [Chapter 37](deamortization.html) |
| [Labelled cursors](#labelled-cursors) | `Models/Labelled/Cursor`, `Models/Labelled/Cursor/Map` | the source configurations of the deamortization ([Chapter 37](deamortization.html)) and of heavy paths ([Chapter 46](heavy-paths.html)); tree-buffer nodes ([Chapter 50](tree-buffers.html)); ComboBST request replay ([Chapter 34](combo-workers.html)) |
| [Data in the nodes](#data-in-the-nodes) | `Models/Labelled/Metadata` | tree-buffer cells ([Chapter 50](tree-buffers.html)) |
| [Interval fields and local routing](#interval-fields-and-local-routing) | `Models/Pointer/Routing`, `Models/Labelled/Intervals` | tree buffers and scans ([Chapter 50](tree-buffers.html)), snapshot startup ([Chapter 51](snapshots.html)), and through them every ComboBST policy ([Chapter 36](combo-online.html), [Chapter 38](combined-finger.html)) |

::: note Do you need this chapter?
A reader who only wants to check the headline theorems of [Chapter 33](combining.html) to [Chapter 38](combined-finger.html) needs two definitions from here. The programs emitted by the deamortized and combined algorithms are stated as legal by [[Multifinger.replay]], from the first section. The ComboBST theorems are quantified over arbitrary old contents of the interval words, `fields : Nat → IntervalMetadata.Bounds`, from the last section; that parameter is only the initial content of memory, so the reader may treat it as "whatever was there". Everything else is proof machinery. Read the section on depths if you want to see why the deamortized algorithms have a worst-case bound per request, and the section on interval fields if you want to see how a ComboBST cursor finds keys without a search from the root.
:::

The models extend three earlier ones. [Chapter 6](pointer.html) gives the single cursor, its configurations [[Pointer.Config]], its instructions [[Pointer.Step]] and traces [[Pointer.Trace]], and the navigation-only [[Pointer.Walk]]. [Chapter 10](fingers.html) gives the six opcodes [[Multifinger.Opcode]] and their executable reading [[Multifinger.perform]]. [Chapter 11](linked-search.html) gives search in a [[LabelledTree]] whose nodes carry keys; here, nodes carry arbitrary data and the cursor may start anywhere.

## Recorded instruction streams

A [[Multifinger.Program]] of [Chapter 10](fingers.html) is a relation: a legal command stream between two multi-finger states. Algorithms that emit instructions one at a time, and proofs that store, concatenate or invert such streams, need a plain function that runs a list of opcodes on one cursor.

@decl RotationBST.Multifinger.replay

`replay ops c` runs the opcodes in order from the configuration `c`, using [[Multifinger.perform]] for each one. It returns `none` as soon as one instruction is illegal, for instance a move onto an empty child or a rotation at the root. Nothing else is supplied: the stream names neither the tree it should produce nor the keys it should reach. Whether a stream is legal, and where it ends, is computed from the configuration alone. There is no finger index, since a single cursor is meant; the multi-finger reading is [[Multifinger.Command.Step]].

@decl RotationBST.Multifinger.Opcode.inverse RotationBST.Multifinger.undo

`Opcode.inverse` undoes one instruction and restores the whole configuration, tree and cursor. A move is undone by the opposite move. A rotation needs three instructions. After `rotateLeftChild`, the cursor is still on the promoted node, and its old parent is now its right child. The cursor steps down to it (`downRight`), rotates it back up (`rotateRightChild`), and steps down to the original node (`downLeft`). `undo ops` undoes the stream in reverse chronological order, expanding each instruction into its inverse.

The five results say that streams and traces are the same thing, and that undoing works.

- **Streams are traces.** A successful replay is a [[Pointer.Trace]] with exactly one instruction per opcode (`physical`). Conversely, every trace of $k$ instructions is the replay of some stream of length $k$ (`record`).
- **Undoing restores.** If `ops` takes `a` to `b`, then `undo ops` takes `b` back to `a` (`restore`), so `ops ++ undo ops` returns from `a` to `a` (`roundtrip`). The undo stream is at most three times as long as the original (`inverse_size`).

@decl RotationBST.Multifinger.Replay.Results.physical RotationBST.Multifinger.Replay.Results.record RotationBST.Multifinger.Replay.Results.restore RotationBST.Multifinger.Replay.Results.inverse_size RotationBST.Multifinger.Replay.Results.roundtrip

The restoration is of the *configuration*: the cursor comes back to the same node, with the same path to the root, not only the same tree. This is the step behind the tree-state buffer of the ComboBST paper (Demaine, Iacono, Langerman and Özkan, Section 3). There, a tree state is saved by recording the operations of a linear-time algorithm that turns the tree into a path, and it is loaded by turning the current tree into a path and then undoing the recorded operations. The snapshots of [Chapter 51](snapshots.html) formalize this. The factor $3$ of `inverse_size` is the same factor as in the reversal of pointer traces inside the reshaping theorem [[Pointer.Lazy.Results.reshape]] of [Chapter 6](pointer.html).

## Walks and detours

A walk only moves the cursor, so it never changes the tree. The three facts that make this precise are short.

@decl RotationBST.Pointer.Walk.Results.primitive RotationBST.Pointer.Walk.Results.physical RotationBST.Pointer.Walk.Results.fixed_tree

A [[Pointer.Move]] is a [[Pointer.Step]], a [[Pointer.Walk]] of $k$ moves is a [[Pointer.Trace]] of $k$ instructions, and the two ends of a walk represent the same tree.

The proof of Theorem 6 of Bose, Collette, Fagerberg and Langerman (*De-amortizing binary search trees*) serves a request in the middle of other work. The simulated algorithm has a pending sequence of operations. Whenever too many of them have been performed without reaching the next requested key, the deamortized algorithm "accesses this element by moving the finger to it and back". This is a *detour*: a walk from the current configuration to the requested key, and the reverse walk, after which the pending work resumes exactly where it stopped. The library states it in five steps.

@decl RotationBST.Pointer.Detour.Results.trace_nonempty

A cursor that stands on a node keeps standing on a node: every trace from a configuration with a nonempty focus ends at a nonempty focus. This holds because no instruction moves the cursor onto an empty subtree ([Chapter 6](pointer.html#instructions)). It lets a detour start at any intermediate configuration of a computation that started on a node.

@decl RotationBST.Pointer.Detour.Results.walk

**Theorem (walk there and back).** Let the cursor of `start` be on rank `current`, and let `target` be a rank of the same tree. Some configuration `visited` has the cursor on `target`, in the same tree, and there are walks from `start` to `visited` and from `visited` back to `start` with the same number of moves. That number is at most $\mathrm{depth}(\mathit{current}) + \mathrm{depth}(\mathit{target})$, and it is $0$ if the cursor is already on the target.

The walk goes up to the lowest common ancestor and down again. The depths are [[Tree.depth]], in edges, of the tree that `start` represents.

@decl RotationBST.Pointer.Detour.Results.record

A walk is recorded as a stream of the same length, and every prefix of that stream replays to a configuration of the *same* tree. The prefix clause matters because the deamortized algorithm may be interrupted again inside a detour; whatever the cut, the tree is the one the detour started from.

@decl RotationBST.Pointer.Detour.Results.bounded

**Theorem (bounded detour).** Suppose the cursor of `start` is on a node, `target` is a rank of the tree, and every rank of the tree has depth at most `height`. Then there are streams `before`, from `start` to a configuration on `target`, and `after`, from there back to `start`, with

$$1 + |\mathit{before}| + |\mathit{after}| \le 1 + 4\cdot\mathit{height}.$$

Both streams are empty if the cursor is already on the target, and every prefix of either stream stays in the same tree.

The leading $1$ is the request unit of [[Pointer.Serves]], so the left side is the cost of one detour as a request. The bound is $4\,\mathit{height}$ and not $2\,\mathit{height}$ because both the way there and the way back may climb from one key to the common ancestor and descend to the other. `height` is a real number, so that it can be a logarithm.

@decl RotationBST.Pointer.Detour.Results.resume

Finally, a detour can be spliced into a stream. If `earlier` reaches `middle`, the detour leaves `middle` and returns to it, and `later` continues from `middle` to `finish`, then the concatenation `earlier ++ before ++ after ++ later` runs from `start` to `finish`. Together with `bounded`, this is how [[Deamortization.Window.Results.serve]] of [Chapter 37](deamortization.html) serves a request with a bounded number of extra instructions while keeping the pending work intact. That theorem needs the depth of every rank to be bounded at the moment of interruption, which is the subject of the section after next.

## Mirror images

Reflecting a tree exchanges left and right everywhere.

@decl RotationBST.Tree.mirror RotationBST.Pointer.Frame.mirror RotationBST.Pointer.Config.mirror

`Tree.mirror` swaps the two children of every node. A frame `left r`, where the cursor is in the left subtree of an ancestor whose right subtree is `r`, becomes `right r.mirror`, and conversely. A configuration is mirrored focus and frames alike. The inorder order is reversed: rank $x$ of `t` becomes rank $|t| - 1 - x$ of `t.mirror`.

Mirroring is an involution on trees, frames and configurations; it keeps the size; it commutes with [[Pointer.plug]], so the mirror of a configuration represents the mirror of its tree; and it turns every instruction into an instruction and every trace into a trace of the same length.

@decl RotationBST.Pointer.Mirror.Results.tree_involution RotationBST.Pointer.Mirror.Results.tree_size RotationBST.Pointer.Mirror.Results.frame_involution RotationBST.Pointer.Mirror.Results.config_involution RotationBST.Pointer.Mirror.Results.plug RotationBST.Pointer.Mirror.Results.config_tree RotationBST.Pointer.Mirror.Results.step RotationBST.Pointer.Mirror.Results.trace

Under the mirror, `downLeft` becomes `downRight`, `upLeft` becomes `upRight` and `rotateLeftChild` becomes `rotateRightChild`, and conversely. The use is economy of proof. The heavy-path representation of the deamortization paper keeps, for the path from the root to the finger, the nodes that leave the path to the left and those that leave it to the right in two weighted stacks, $L(r,f)$ and $R(r,f)$. The library builds and analyses only the left-hand pop-tart, and obtains the right-hand one as its mirror image ([Chapter 44](pop-tarts.html), [Chapter 46](heavy-paths.html)). The results above, and the depth versions below, carry costs and depth bounds across the reflection.

## Depths along a computation

### Why depths are tracked

The deamortization of [Chapter 37](deamortization.html) runs a simulation of the source algorithm and may stop it after any instruction to serve a request by a detour. A detour costs at most $4$ times the largest depth in the current tree, by `bounded` above. The current tree is an *intermediate* tree of the simulation: one that the algorithm passes through, between two of its own requests, and that no amortized analysis speaks about. A bound on the cost of each request therefore needs a depth bound that holds at *every instruction boundary* of the simulation.

That is what the heavy-path simulation provides. In [[Deamortization.Weighted.Results.simulation]], every cut of the emitted stream reaches a tree in which every rank has depth at most $336 + 240 \log_2(W/w)$, where $w$ is the rank's weight and $W$ the total weight. The deamortization uses unit weights, so the bound is $336 + 240\log_2 n$. With it, each response of the deamortized algorithm costs less than $251 + 195\log_2 n$. The deamortized Splay theorems of [Chapter 37](deamortization.html), from scanning to static optimality and static finger, are all stated for one implementation and one run, so they hold together with this worst-case bound; the bound itself rests on the lemmas of this section. Static optimality is *not* derived from these depth bounds: it comes from the total-cost comparison with Splay.

The depth bounds of the simulation are assembled from bounds for each piece: one pop-tart operation, one heavy-path update, one change inside a subtree, the mirror image of a left-hand operation, and operations in sequence. The lemmas below are the glue. All depths are [[Tree.depth]], in edges, indexed by inorder rank, the same function as in the static-tree bounds of [Chapter 13](bounds.html).

### One instruction changes a depth by at most one

**Theorem (rotations).** One rotation increases the depth of any rank by at most $1$. A sequence of $c$ rotations increases it by at most $c$.

@decl RotationBST.StaticTree.Trace.Results.rotate_depth RotationBST.StaticTree.Trace.Results.rotations_depth

**Theorem (traces).** Along a pointer trace of $c$ instructions from `s` to `t`, the depth of every rank changes by at most $c$, in both directions: $\mathrm{depth}_t(x) \le \mathrm{depth}_s(x) + c$ and $\mathrm{depth}_s(x) \le \mathrm{depth}_t(x) + c$.

@decl RotationBST.StaticTree.Trace.Results.trace_depth RotationBST.StaticTree.Trace.Results.trace_depth_reverse

Moves do not change the tree, and a rotation changes each depth by at most one in either direction, since it can be undone by one rotation. The quantifier ranges over all natural numbers $x$. For $x \ge |t|$ in a nonempty tree, [[Tree.depth]] follows the right spine and returns one more than the depth of the maximum, so these cases add nothing.

**Theorem (cut a stream anywhere).** If a stream `ops` runs from `s` to `t`, then for every cut point the prefix `ops.take cut` reaches some `middle`, the suffix `ops.drop cut` continues from `middle` to `t`, and every rank satisfies

$$\mathrm{depth}_{\mathit{middle}}(x) \le \min\bigl(\mathrm{depth}_s(x) + |\text{prefix}|,\ \mathrm{depth}_t(x) + |\text{suffix}|\bigr).$$

If the whole stream has at most `budget` instructions, then $\mathrm{depth}_{\mathit{middle}}(x) \le \mathrm{depth}_s(x) + \mathit{budget}$.

@decl RotationBST.StaticTree.Trace.Results.replay_prefix_depth RotationBST.StaticTree.Trace.Results.replay_prefix_bound

These are the bounds for streams that are short compared with the depths, such as the bounded number of instructions that the deamortized algorithm executes per request. For long computations an additive bound is useless, and the depth must be controlled by an invariant.

### The trace invariant

@decl RotationBST.Pointer.TraceWithin

`TraceWithin holds a c cost` is a pointer trace of `cost` instructions from `a` to `c`, together with the fact that the tree satisfies `holds` at every instruction boundary, both endpoints included. It is [[Pointer.Trace]] with one more hypothesis in each constructor. The invariants used in the library all have the same shape: relative to the starting tree `s`, every intermediate tree `u` has the same size and

$$\mathrm{depth}_u(x) \le f\cdot\mathrm{depth}_s(x) + k \quad\text{for every rank } x,$$

with a factor $f \ge 1$ and a constant $k$. The size clause is what makes depths of different trees comparable: rotations keep the size and the inorder order, so rank $x$ names the same key in all of them.

**Theorem (every trace satisfies the additive invariant).** A trace of $c$ instructions from `a` satisfies the invariant with $f = 1$ and $k = c$.

@decl RotationBST.StaticTree.Trace.Results.within_size_depth

This is the previous section, at every boundary. The pieces of the heavy-path simulation are short, so this lemma starts most of their invariants.

**Theorem (composition).** If a trace from `a` to `b` satisfies the invariant with $(f, u)$ relative to `a`, and a trace from `b` to `c` satisfies it with $(g, v)$ relative to `b`, where $g \ge 1$, then the concatenated trace satisfies it with factor $g f$ and constant $g u + v$ relative to `a`.

@decl RotationBST.StaticTree.Trace.Results.within_append

The constants compose like affine maps: $\mathrm{depth}_c \le g\,\mathrm{depth}_b + v \le g(f\,\mathrm{depth}_a + u) + v$. Factors multiply, so this composition is meant for a bounded number of pieces: a long sequence of pieces, each with a factor larger than $1$, would let the bound grow geometrically.

**Theorem (embedding in a context).** If $t$'s depths are bounded by $f\cdot{}$`s`'s depths plus $k$, with $f \ge 1$ and equal sizes, then the same bound holds after both trees are plugged into the same context `cs`. Consequently, a root-to-root trace from `s` to `t` satisfying the invariant becomes a root-to-root trace from `plug cs s` to `plug cs t` of cost $|cs| + c + |cs|$ that satisfies the invariant relative to `plug cs s`, provided that `s` and `t` are nonempty.

@decl RotationBST.StaticTree.Trace.Results.plug_bound RotationBST.StaticTree.Trace.Results.within_embed

The embedded trace walks down the context to the subtree, runs the computation there, and walks back up; the two walks cost $|cs|$ each. A key outside the subtree keeps its depth, and a key inside has its depth in the subtree plus $|cs|$; the condition $f \ge 1$ makes the bound survive the extra $|cs|$. This is how an operation on one pop-tart, deep inside the heavy-path representation, contributes to the depth invariant of the whole tree. The nonemptiness hypotheses let the cursor stand on the root of the subtree at both ends.

**Theorem (mirror images).** Mirroring moves rank $x$ to rank $|t| - 1 - x$ and keeps its depth. Depth bounds of the invariant's form, and the invariant along a trace, transfer to the mirror images.

@decl RotationBST.StaticTree.Trace.Results.mirror_rank_depth RotationBST.StaticTree.Trace.Results.mirror_bound RotationBST.StaticTree.Trace.Results.within_mirror_depth

`mirror_bound` compares the mirrors at the same rank, which is legitimate because both trees have the same size, so the reflection of ranks is the same on both sides. With `within_mirror_depth` and [[Pointer.Mirror.Results.trace]], every depth guarantee proved for a left-hand pop-tart holds for the right-hand one.

## Labelled cursors

The configurations of [Chapter 6](pointer.html) are shapes: a node has no content, and its key is its inorder rank, computed from subtree sizes. Most structures of the deamortization and combination chapters store something in their nodes: a weight, a key and a stored interval, a payload word. They need a cursor on a [[LabelledTree]] whose instructions carry each label along with its node.

@decl RotationBST.LabelledCursor.Frame RotationBST.LabelledCursor.plug RotationBST.LabelledCursor.Frame.erase

A labelled frame records one ancestor of the cursor, now with its label: `left entry r` says that the cursor is in the left subtree of an ancestor labelled `entry` whose right subtree is `r`, and `right l entry` is the mirror case. As in [[Pointer.Frame]], the constructor names the side on which the cursor is. `plug` rebuilds the labelled tree from the focus and the frames, nearest ancestor first, and `Frame.erase` forgets the labels.

@decl RotationBST.LabelledCursor.Config RotationBST.LabelledCursor.Config.tree RotationBST.LabelledCursor.Config.erase

A labelled configuration is a focused labelled subtree with its labelled context. `tree` is the labelled tree it represents, and `erase` is the underlying shape configuration of [Chapter 6](pointer.html).

@decl RotationBST.LabelledCursor.Config.read RotationBST.LabelledCursor.Config.write

`read` returns the label of the node under the cursor, and `write entry` replaces it, keeping both children and the whole context. Both fail on an empty focus. They are the only ways to inspect or change a label, and they act only at the cursor: a structure that wants to read the label of another node must first walk there. The cursor model charges nothing for them; the models that use them (the word costs below, and the cell costs of [Chapter 50](tree-buffers.html)) charge for reads and writes explicitly.

@decl RotationBST.LabelledCursor.perform

`perform op c` executes one of the six opcodes of [[Multifinger.Opcode]] on a labelled configuration. The patterns are those of [[Multifinger.perform]], with labels added. A rotation moves the labels with their nodes: after `rotateLeftChild` at the node labelled `x`, whose parent is labelled `y`, the node labelled `x` is on top and the node labelled `y` is its right child. As the docstring says, no rank or subtree size is computed by these primitives.

The results say that the labelled cursor is the shape cursor with labels attached, and nothing more.

@decl RotationBST.LabelledCursor.Results.erase_tree RotationBST.LabelledCursor.Results.perform_erase RotationBST.LabelledCursor.Results.perform_physical RotationBST.LabelledCursor.Results.write_erase

Erasing commutes with building the tree (`erase_tree`) and with every instruction (`perform_erase`): a labelled instruction succeeds exactly when the shape instruction succeeds, and it then does the same thing to the shape. In particular each successful labelled instruction is one [[Pointer.Step]] (`perform_physical`), so labelled computations are charged by the pointer machine of [Chapter 6](pointer.html). A write leaves the shape configuration unchanged (`write_erase`).

@decl RotationBST.LabelledCursor.Results.lift

Conversely, every shape cursor can be labelled: if a labelled tree `whole` has the shape of the tree of a shape configuration `cursor`, then some labelled configuration of `whole` erases to `cursor`. So a shape computation, a [[Pointer.Trace]] for example, can always be followed on a labelled tree of the same shape.

### Projecting fields

A node often stores a tuple of fields, of which a sub-structure uses only some. The library projects a labelled tree or cursor by a function on labels.

@decl RotationBST.LabelledTree.map RotationBST.LabelledCursor.Frame.map RotationBST.LabelledCursor.Config.map

These apply `f` to every label of a tree, a frame, or a configuration. The docstring is explicit: `Config.map` is a proof projection, not a traversal run by the machine. It is used to say that the routing view of a tree-buffer node ([Chapter 50](tree-buffers.html)), its key and interval, evolves exactly as the interval model of the last section, whatever the other fields of the node hold.

@decl RotationBST.LabelledCursor.Results.map_erase RotationBST.LabelledCursor.Results.perform_map RotationBST.LabelledCursor.Results.lift_map

A projection keeps the shape configuration (`map_erase`) and commutes with every instruction (`perform_map`). And a cursor on the projected tree lifts to a cursor on the full tree with the same projection (`lift_map`), so a computation on the projected fields can be followed on the full nodes.

## Data in the nodes

The ComboBST paper allows each node to store $O(\log n)$ bits of augmented data, and builds its buffers from them (Section 3). The library describes the data attached to a tree of shape `t` by a payload function on ranks.

@decl RotationBST.Metadata.label

`Metadata.label data t lo` labels the node of rank $x$ with the pair $(x, \mathit{data}(x))$, where ranks start at `lo`. It is [[Tree.labelFrom]] of [Chapter 1](shapes.html#canonical-labels), with a payload next to each key. `data` is a total function on all natural numbers, but only its values on the keys of the tree appear in the result: as the docstring says, the function is a semantic representation, and only the tree's finite key interval is stored.

@decl RotationBST.Metadata.At RotationBST.Metadata.Write

`At t x v` says that some node of `t` has key `x` and payload `v`. `Write t x v t'` says that `t'` is `t` with the payload of the node with key `x` replaced by `v`, everything else unchanged. Both are structural relations, which locate a node by its position. They do not grant access: as the docstrings warn, a structure that reads or writes a payload must have its cursor on that node, through [[LabelledCursor.Config.read]] and [[LabelledCursor.Config.write]]. The library proves (internally, in `Models/Labelled/Metadata`) that a write at the cursor is a `Write` and that a read at the cursor gives an `At`.

## Interval fields and local routing

A ComboBST cursor does not restart at the root. It finds the next key from wherever it stands, as a lazy finger does ([Chapter 15](lazy-finger.html)). On the pointer machine, the key of a node is its inorder rank, and computing it requires the sizes of subtrees off the cursor's path. A real implementation must decide the direction from what is stored in the node. The library stores, in each node, its key and the half-open interval $[\mathit{low}, \mathit{high})$ of the keys in its subtree. Three words suffice to choose the next edge toward any target.

### The routing rule

@decl RotationBST.Pointer.Routing.View RotationBST.Pointer.Routing.View.Valid

A view is the three words read at the current node: `low`, `key` and `high`. It is *valid* for a cursor when `low` is the number of keys before the focused subtree ([[Pointer.offset]]), `key` is the rank under the cursor, and `high` is `low` plus the size of the focused subtree. So the subtree holds exactly the ranks in $[\mathit{low}, \mathit{high})$. Validity is a specification: computing offsets and sizes there is not part of the model, and the rule below reads only the three fields.

@decl RotationBST.Pointer.Routing.Direction RotationBST.Pointer.Routing.choose

`choose v target` compares the target with the three words. It returns `none` if the target is the current key: the cursor has arrived. If the target is inside the interval, it goes left or right according to the key. Otherwise it goes to the parent.

@decl RotationBST.Pointer.Routing.perform RotationBST.Pointer.Routing.next

`perform` follows the chosen pointer, with the patterns of [[Pointer.Move]], and fails if the child is empty or there is no parent. `next` chooses and then follows. The library proves (internally, in `Models/Pointer/Routing`) that with a valid view and a target in the tree, `next` makes one [[Pointer.Move]] that decreases the lazy-finger distance [[LazyFinger.distance]] to the target by exactly one, and that every move with this property is the one `next` chooses. The routing rule is therefore a shortest-path walk, decided locally. The tree-buffer scans of [Chapter 50](tree-buffers.html) state the consequence in their reading interface, for example [[TreeBuffer.Scan.Results.labelled_route]].

### Stored intervals

@decl RotationBST.IntervalMetadata.Bounds RotationBST.IntervalMetadata.label

`Bounds` is a pair of words. `IntervalMetadata.label t lo` is the *canonical annotation* of a shape: the node of rank $x$ gets the label $(x, [\mathit{lo}', \mathit{lo}' + \mathit{size}))$, the interval of its own subtree. The docstring says that this recursive annotation is the representation invariant, not the routing code: the routing code reads fields, and this function says what the fields should contain.

A rotation changes the intervals of exactly two subtrees, those of the two rotated nodes.

@decl RotationBST.IntervalMetadata.Update

`Update s t` relates two annotated trees when `t` is a rotation of `s` in which only the two rotated nodes get new intervals, computed from their own keys and old intervals. In the case `right`, the left child $x$ is promoted over $y$. Its subtree is now the whole old subtree of $y$, with interval $[\mathit{low}_x, \mathit{high}_y)$, and $y$'s subtree now starts just after $x$, with interval $[x + 1, \mathit{high}_y)$. The case `left` is symmetric, and `inLeft`, `inRight` place the update anywhere in the tree. The ancestors keep their intervals, because a rotation does not change the set of keys below any other node. The library proves internally that a rotation of the shape turns the canonical annotation into the canonical annotation by such an update.

@decl RotationBST.IntervalMetadata.Access.route RotationBST.IntervalMetadata.Access.Canonical

`route target c` is the routing step on an annotated labelled cursor. It reads the key and the interval at the cursor, chooses a direction with [[Pointer.Routing.choose]], and performs the corresponding labelled move. It charges $4$ units: three word reads and one pointer move. It fails if the cursor has arrived (and then nothing needs to be done) or the move is impossible. `Canonical c` says that every field of the whole tree is correct, that is, the tree is the canonical annotation of its shape. The library proves internally that from a canonical cursor and a target in the tree, `route` succeeds with cost $4$, makes a move that brings the cursor one step closer to the target, changes no field, and leaves the cursor canonical.

### Initializing the fields

The ComboBST theorems quantify over the old contents of the memory, `fields : Nat → IntervalMetadata.Bounds`: the library does not assume that the intervals are already in place. A startup traversal writes them, with one cursor and a constant number of registers.

@decl RotationBST.IntervalMetadata.Initialization.Mode RotationBST.IntervalMetadata.Initialization.State

The state is a shape cursor, the field memory `fields`, indexed by key, one pending interval in two registers, and a mode. As the docstring says, the traversal is stackless: it keeps no stack of ancestors. What it needs when it returns to an ancestor is in the parent links of the zipper and in the fields that it has already written.

@decl RotationBST.IntervalMetadata.Initialization.tick

One `tick` is one step of a depth-first traversal.

- `write`: store the pending interval in the field of the current key, at cost $2$ (two word writes), and turn to the left child.
- `left`: if there is no left child, pay $1$ for the null check and turn right. Otherwise descend, at cost $4$: the new pending interval runs from the current node's stored `low` to the current key.
- `right`: symmetric. The new pending interval runs from the current key plus one to the stored `high`.
- `up`: climb to the parent at cost $1$. Coming from a left child, turn to the parent's right child; coming from a right child, keep climbing.

At the root in mode `up`, and at an empty tree, no case applies and the traversal halts. The current key is written `Pointer.offset … + l.size`. As the docstring explains, this denotes the key stored at the cursor, as in the shape model; its recursive evaluation is not part of the word-cost model.

@decl RotationBST.IntervalMetadata.Initialization.Run RotationBST.IntervalMetadata.Initialization.initial

`Run s t cost` is a sequence of ticks with their summed charges. `initial tree n fields` starts at the root, in mode `write`, with the pending interval $[0, n)$ and arbitrary old fields.

@decl RotationBST.IntervalMetadata.Initialization.populate RotationBST.IntervalMetadata.Initialization.work

`populate` is the mathematical effect of the traversal, the field memory with every key of the tree set to its canonical interval. The docstring stresses that it is used only to state the output; the running traversal computes each child's interval from the parent's key and stored field. `work t` is the total charge: $2$ per node, $1$ per missing child, and $5$ per existing child (descent and return). The library proves internally that `work t + 4 = 8 |t|` for a nonempty tree, and that the traversal started by `initial` halts at the root after cost at most $8n$, with every field of the tree equal to its canonical interval and every field of a key $\ge n$ unchanged.

@decl RotationBST.IntervalMetadata.Initialization.State.Bounded

`Bounded limit s` is a word-size invariant: the tree size, the two registers, and every stored field are at most `limit`. The limit may exceed $n$, so that old memory may hold any bounded garbage. The library proves internally that every prefix of the traversal keeps this invariant if the start satisfies it.

@decl RotationBST.IntervalMetadata.Initialization.runLoop RotationBST.IntervalMetadata.Initialization.runFuel

`runFuel fuel s` runs the traversal as a loop with a budget of `fuel` ticks and an accumulated charge, again in scalar registers only. It returns the halted state and the charge, or `none` if the traversal has not halted within the budget. The snapshot startup of [Chapter 51](snapshots.html) runs a variant of this loop, for nodes that carry a data word as well, with budget $8n$.

### Maintaining the fields under rotations

A source algorithm simulated in a ComboBST tree rotates. After each rotation the two changed intervals must be rewritten, at the cursor, with a constant number of operations.

@decl RotationBST.IntervalMetadata.Maintenance.Side RotationBST.IntervalMetadata.Maintenance.Side.opcode

`Side` names which child is promoted: `left` stands for `rotateLeftChild`, which promotes a left child over its parent, and `right` for `rotateRightChild`.

@decl RotationBST.IntervalMetadata.Maintenance.State RotationBST.IntervalMetadata.Maintenance.Op RotationBST.IntervalMetadata.Maintenance.Op.moves RotationBST.IntervalMetadata.Maintenance.Op.cost

The state is an annotated labelled cursor and two saved node entries, `child` and `parent`, each a key and an interval: six scalar registers. An operation is a pointer instruction, a read of the current entry into `child` or `parent`, or a write of a new interval at the cursor. `Op.moves` counts pointer instructions, rotations included. `Op.cost` charges $1$ per pointer instruction, $3$ per read (key and two bounds) and $2$ per write (two bounds).

@decl RotationBST.IntervalMetadata.Maintenance.childBounds RotationBST.IntervalMetadata.Maintenance.parentBounds RotationBST.IntervalMetadata.Maintenance.writeBounds

`childBounds` and `parentBounds` compute the new intervals of the promoted node and of the demoted one from the saved registers alone, exactly as in [[IntervalMetadata.Update]]. For `left`, the promoted child gets $[\mathit{low}_{\mathit{child}}, \mathit{high}_{\mathit{parent}})$ and the demoted parent $[\mathit{key}_{\mathit{child}} + 1, \mathit{high}_{\mathit{parent}})$; `right` is symmetric. `writeBounds` stores an interval at the cursor and keeps the stored key.

@decl RotationBST.IntervalMetadata.Maintenance.tick RotationBST.IntervalMetadata.Maintenance.run

`tick` executes one operation. Every operation is guarded by a node under the cursor, and writes change only the two interval words. `run` executes a list of operations and fails if one fails.

@decl RotationBST.IntervalMetadata.Maintenance.program RotationBST.IntervalMetadata.Maintenance.maintain

`program left` is the fixed sequence: read the child's entry, go up to the parent and read its entry, come back down, rotate, write the promoted node's interval, step down to the demoted node, write its interval, and come back up. It starts and ends on the promoted node. `maintain side` runs it.

@decl RotationBST.IntervalMetadata.Maintenance.charge RotationBST.IntervalMetadata.Maintenance.pointerCount

`charge` adds the costs and `pointerCount` counts the pointer instructions of an operation list. For either program, the charge is $15$: two reads ($6$), two writes ($4$), four moves and one rotation ($5$). The library proves internally that whenever the shape rotation is legal and the fields are canonical, `maintain` succeeds, performs that rotation on the shape, leaves all fields canonical, and is a pointer trace of $5$ instructions. The tree-buffer nodes of [Chapter 50](tree-buffers.html) run this program for their rotations.

::: check
- **What is charged.** The interval programs charge word reads and writes, null-link checks and pointer instructions. Only pointer instructions are pointer-machine work; the others are the word costs of the paper's augmented nodes. The ComboBST theorems of [Chapter 36](combo-online.html) state their costs in pointer instructions and requests.
- **What is not charged.** Lean's evaluation of offsets and subtree sizes, which appear in the specification (`View.Valid`, `Canonical`, `populate`) and, in the initialization, in the name of the current key. The docstrings say so, and the routing rules themselves read only stored fields.
- **No theorem in this chapter for the interval programs.** Their correctness theorems (`Initialization.complete`, `Access.progress`, `Maintenance.implement` and the routing lemmas) are internal. They reach the reading interface through the tree-buffer and scan theorems of [Chapter 50](tree-buffers.html).
:::
