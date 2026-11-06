# Snapshots

The combined search tree of [Chapter 33](combining.html) runs two online BST algorithms in alternating rounds. Each round starts from the same initial tree $T$: when a round runs out of budget, the structure transforms whatever tree it has back into $T$, and the other algorithm takes over. A BST cannot keep a second copy of $T$ on the side. Demaine, Iacono, Langerman and Özkan therefore store $T$ *inside the tree itself*, in the $O(\log n)$ bits of augmented data that every node may carry. Their *tree state buffer* (TSB, Section 3 of the paper) supports two operations. `SaveState()` records the current tree in the buffer, and `LoadState()` transforms the current tree, whatever it is, into the recorded one. The encoding is simple. Run a linear-time algorithm that rotates the tree into a path, and record its operations. To load, rotate the current tree into the same path, then undo the recorded operations. Lemma 10 of the paper says that both operations take $O(n)$ steps.

This section formalizes the tree state buffer on the cells and scans of [Chapter 50](tree-buffers.html), with explicit constants and with a payload of twelve bits per node.

```headline snapshots-save-load
title: A tree can be saved into its own nodes and restored, in linear time
source: Demaine, Iacono, Langerman and Özkan, *Combining binary search trees* (2013)
theorems: RotationBST.TreeBuffer.Snapshot.Recording.Results.save RotationBST.TreeBuffer.Snapshot.Streaming.Results.load

Consider a tree with $n$ nodes and one data cell per node, indexed by inorder rank, as in the buffers of [Chapter 50](tree-buffers.html). Two fingers share the tree: a *tree finger* that moves and rotates, and a *buffer finger* that walks from cell to cell and reads or writes the cell under it.

**Save.** Starting from a tree $t$, with both fingers at the root and arbitrary initial cell contents, there is a save execution that ends with the same tree $t$ and the tree finger at its root, and that leaves in the cells the snapshot of $t$: a fixed value below $2^{12}$ in every cell, determined by $t$ ([[TreeBuffer.Snapshot.CellIO.Stored]]). It costs at most $72n$. The cost counts every tree-finger instruction and every buffer-finger move, read and write.

**Load.** Suppose the cells hold the snapshot of a tree $s$, and the current tree has the same number $n$ of nodes, with both fingers at its root. Then there is a load execution that ends with the tree $s$ and the tree finger at its root, at cost at most $56n$, counted in the same way. The load never writes a cell, and its steps depend only on the current tree and on the cell contents; $s$ appears only in the conclusion.
```

The two theorems are the abstract counterpart of Lemma 10. The save executes the formal [[TreeBuffer.Snapshot.Recording.Save]], and the load executes [[TreeBuffer.Snapshot.Streaming.Load]]; both are defined in [Section 51.8](#save-and-load). Rotations performed by the tree finger are charged once, as tree-finger instructions; the buffer finger is not charged for them, but the detours they force on it are charged as buffer moves.

::: note Do you need this section?
Read it if you want to see how the combined tree returns to its initial state between rounds. The restart of a worker in [Chapter 36](combo-online.html) ([[Combo.Refinement.Results.restart]]) and the one-time preparation before the first request ([[Combo.Online.Prepared]]) both call the machinery of this section, through the shared-node versions of [Section 51.9](#on-shared-nodes). A reader who only wants to check the combining theorem can skip it: what that theorem needs is stated in its own hypotheses and conclusions in [Chapter 33](combining.html). The Lean sources are in `Structures/TreeBuffer/Snapshot`.
:::

## Overview

The development has three layers.

**Instruction streams.** The first layer works with lists of the six primitive opcodes of the multi-finger model ([[Multifinger.Opcode]]): move to the left or right child, move up from a left or right child, rotate the focused left or right child over its parent. [[Multifinger.replay]] runs such a list on a pointer cursor, and [[Multifinger.undo]] inverts it. [Section 51.1](#normalizing-to-a-vine) defines the normalizer that rotates any tree into the right path on its keys, the *vine*, and its log [[TreeBuffer.Snapshot.record]]. Save is "normalize, then undo the log". Load is "normalize the current tree, then undo the saved log". The log identifies the tree, has at most $4n$ opcodes, and fits four opcodes into each of the $n$ cells, as base-seven digits of a twelve-bit number ([Section 51.3](#packing-the-log-into-the-nodes)).

**Machines.** The second layer turns these streams into machines that keep only bounded working storage. A local *controller* computes the normalization log one opcode at a time from the focused subtree, a mode and a depth counter ([Section 51.5](#a-local-normalizer)). *Recording* runs the controller and, after every four opcodes, lets the buffer finger write the packet into the next cell ([Section 51.6](#recording)). *Streaming restoration* reads the cells in descending order and undoes each packet locally, so it never needs the reversed log as a whole ([Section 51.4](#snapshot-cells-and-inversion) and [Section 51.7](#streaming-restoration)). The buffer finger's walk is charged with the scan potential of [Chapter 50](tree-buffers.html), which absorbs the rotations made by the other finger, as in Lemma 9 of the paper.

**Shared nodes.** The third layer places both fingers on one labelled tree of [Chapter 50](tree-buffers.html), with routing words and payload fields in every node ([Section 51.9](#on-shared-nodes)). Its theorems are internal; the combining construction uses them.

The headline theorems belong to the second layer. Their cost is the sum of three counts: tree-finger instructions, buffer-finger moves and buffer-finger cell visits.

## Normalizing to a vine

The target shape is the *vine*, the tree whose nodes all lie on the right spine:

@decl RotationBST.TreeBuffer.Snapshot.vine

`vine n` has $n$ nodes, all with empty left subtrees. Its root has key $0$. The paper flattens the tree into a *left* path; the right path is the mirror image and changes nothing.

The normalizer walks down the right spine. At a node with an empty left subtree, it moves to the right child, normalizes there, and moves back up. At a node with a nonempty left subtree, it moves to the left child and rotates it over its parent, which moves one node from the left subtree to the spine; the cursor is then back at the same depth, on the rotated node, and the normalizer continues there.

@decl RotationBST.TreeBuffer.Snapshot.work RotationBST.TreeBuffer.Snapshot.recordFuel RotationBST.TreeBuffer.Snapshot.record

`recordFuel fuel t` returns the opcodes this procedure emits on `t`:

- on an empty tree or a leaf, nothing;
- on `node nil (node a b)`, `downRight`, then the opcodes for the right subtree, then `upRight`;
- on `node (node a b) c`, `downLeft`, `rotateLeftChild`, then the opcodes for the rotated tree `node a (node b c)`.

The recursion on the rotated tree is not structural, so it is driven by a fuel argument. `work t` is a measure that decreases by one at every recursive call: $2|l| + 1$ for the root with left subtree $l$, plus the work of the right subtree. A descent drops the root's term; a rotation of `node (node a b) c` into `node a (node b c)` replaces $2(|a|+|b|+1)+1$ by $(2|a|+1) + (2|b|+1)$. `record t` uses exactly `work t` as fuel, which is enough, so the fuel only totalizes the helper. The log contains opcodes only. It does not contain the tree, or any key.

**Theorem (normalization).** From any cursor focused on the root of a subtree $t$, under any ancestor context, replaying `record t` turns the subtree into the vine on $|t|$ nodes, with the cursor back on its root in the same context. The log has at most $4|t|$ opcodes.

**Theorem (the log identifies the tree).** Two trees with the same number of nodes and the same log are equal.

@decl RotationBST.TreeBuffer.Snapshot.Results.normalization RotationBST.TreeBuffer.Snapshot.Results.identifies

The ancestor context `cs` in `normalization` is the zipper context of [Chapter 6](pointer.html) ([[Pointer.Frame]]): normalization is a local computation that never leaves the subtree. The length bound has a simple reason: every opcode pair is either a rotation (`downLeft`, `rotateLeftChild`) or a spine descent (`downRight` with its later `upRight`), there are fewer than $n$ rotations, since each puts a new node on the spine, and fewer than $n$ descents. `identifies` is the reason why the log is a faithful snapshot. Intuitively, undoing the log from the vine returns the tree, the vine is fixed by $n$, and the undo is fixed by the log.

::: details A three-node example
Let $t$ be the balanced tree on keys $0,1,2$, with root $1$. The root has a nonempty left subtree, so the normalizer emits `downLeft` and `rotateLeftChild`: node $0$ becomes the root, and the tree is already the vine $0 \to 1 \to 2$. It then descends the spine twice and climbs back:

```
record t = [downLeft, rotateLeftChild, downRight, downRight, upRight, upRight]
```

Six opcodes, within the bound $4 \cdot 3 = 12$. Undoing reverses the list and inverts each opcode, where the inverse of a rotation takes three instructions (see [Section 51.2](#save-and-load-as-instruction-streams)):

```
undo (record t) = [downRight, downRight, upRight, upRight,
                   downRight, rotateRightChild, downLeft, upLeft]
```

From the vine, the first four opcodes walk down to key $2$ and back. Then `downRight` moves to key $1$, `rotateRightChild` rotates it over key $0$, which restores the balanced tree with the cursor on its root $1$, and `downLeft`, `upLeft` visit key $0$ and come back.
:::

## Save and load as instruction streams

The inverse of a single opcode is the move in the opposite direction, or, for a rotation, three instructions: the rotated node is now the parent of its old parent, so the cursor steps down to the old parent, rotates it back up, and steps down again ([[Multifinger.Opcode.inverse]]). `undo` reverses a list and inverts each opcode.

@decl RotationBST.TreeBuffer.Snapshot.saveProgram RotationBST.TreeBuffer.Snapshot.loadProgram

`saveProgram t` normalizes and immediately undoes. Its first half, `record t`, is the part that the snapshot retains. `loadProgram current saved` normalizes the current tree with its own log and then undoes a saved log. The saved tree is not an argument: only its log is.

**Theorem (save as a stream).** The stream `saveProgram t` is a legal pointer-machine trace from $t$, with the cursor at the root, back to $t$, with the cursor at the root. It has at most $16|t|$ instructions.

**Theorem (load as a stream).** If the current tree and the saved tree $s$ have the same number $n$ of nodes, the stream `loadProgram current (record s)` is a legal pointer-machine trace from the current tree to $s$, root to root, with at most $16n$ instructions.

@decl RotationBST.TreeBuffer.Snapshot.Results.save RotationBST.TreeBuffer.Snapshot.Results.load

The traces are [[Pointer.Trace]]s of [Chapter 6](pointer.html), whose count is the number of instructions. The bound $16n$ is $4n$ for the log plus $12n$ for its undo, since each opcode expands into at most three. These two theorems say nothing about storing the log: in this layer the stream is simply a list. Storing it in the nodes is the subject of the next two sections, and its cost is counted in [Section 51.6](#recording).

## Packing the log into the nodes

The log has at most $4n$ opcodes and the tree has $n$ nodes, so four opcodes per node suffice.

@decl RotationBST.TreeBuffer.Snapshot.pack RotationBST.TreeBuffer.Snapshot.cells

`pack n ops` cuts `ops` into $n$ packets of at most four opcodes, in order. Packets past the end of the list are empty, and opcodes beyond capacity $4n$ would be dropped; for a log this never happens. `cells t` is the packing of `record t` into exactly $|t|$ packets, one per node. Packet $j$ belongs to the node of inorder rank $j$. Since rotations preserve the inorder, that node keeps its packet whatever the shape becomes.

Each packet is encoded as a number:

@decl RotationBST.TreeBuffer.Snapshot.opcodeDigit RotationBST.TreeBuffer.Snapshot.digitOpcode RotationBST.TreeBuffer.Snapshot.encodeCell RotationBST.TreeBuffer.Snapshot.decodeFuel RotationBST.TreeBuffer.Snapshot.decodeCell

The six opcodes are the digits $1$ to $6$ in base seven, and the digit $0$ marks the end of a packet. `encodeCell` writes the first opcode as the least significant digit. `decodeCell` reads at most four digits and stops at the first $0$ (or at an invalid digit, which `digitOpcode` maps to `none`). A packet of at most four opcodes is a number below $7^4 = 2401 < 2^{12}$, and decoding it returns the packet.

@decl RotationBST.TreeBuffer.Snapshot.encodedCells RotationBST.TreeBuffer.Snapshot.decodeCells RotationBST.TreeBuffer.Snapshot.loadEncoded

`encodedCells t` is the list of the $|t|$ cell values, in inorder. `decodeCells` decodes a list of values and concatenates the packets. `loadEncoded current codes` is the load stream computed from encoded cells: normalize `current`, then undo the decoded log.

**Theorem (twelve bits per node).** The snapshot of $t$ has exactly $|t|$ values, each below $2^{12}$, and decoding them returns the log `record t`.

**Theorem (restoring from the encoded cells).** If the current tree and $s$ have the same number $n$ of nodes, the load stream computed from the current tree and the encoded snapshot of $s$ turns the current tree into $s$, under any unchanged ancestor context, with at most $16n$ instructions.

@decl RotationBST.TreeBuffer.Snapshot.Results.storage RotationBST.TreeBuffer.Snapshot.Results.encoded_restore

In `encoded_restore`, the target `saved` occurs only in the specification: the stream is computed from `current` and the list of numbers. Because of the context `cs`, the restoration also works on a subtree, as long as nothing above it changes.

## Snapshot cells and inversion

The machines below do not handle lists of cells. They have a cell field in each node, modelled as a function from keys to values, as in [[TreeBuffer.Cells.State]].

@decl RotationBST.TreeBuffer.Snapshot.CellIO.payload RotationBST.TreeBuffer.Snapshot.CellIO.Stored

`payload saved key` is the value that the snapshot of `saved` puts in the cell of rank `key`, and $0$ beyond the end of the list. `Stored saved data` says that a cell function holds the snapshot of `saved`: it agrees with `payload saved` on every rank below $|{\it saved}|$. Values at larger ranks are unconstrained, since no node has them. `Stored` speaks only about the cells. It says nothing about the current shape, which may be anything: this is the situation of the combined tree in the middle of a round, after a worker has rotated the tree for a while without touching the snapshot cells.

Restoring requires the log undone, that is reversed and inverted. A machine with bounded storage cannot reverse a list of $4n$ opcodes. It does not need to: undoing a concatenation of packets is the concatenation of the undone packets in reverse order, so reading the cells *backwards* and undoing each packet on its own produces exactly the undo of the whole log.

@decl RotationBST.TreeBuffer.Snapshot.CellIO.inverseCells

`inverseCells codes` decodes each value, undoes the packet, and concatenates. Applied to the cell values in descending rank order, it is `undo (record saved)`. For the three-node example, the cells are $[\,820, 32, 0\,]$ (packets `[downLeft, rotateLeftChild, downRight, downRight]`, `[upRight, upRight]` and the empty packet). Reading them as $0, 32, 820$ and undoing each gives `[]`, then `[downRight, downRight]`, then `[upRight, upRight, downRight, rotateRightChild, downLeft, upLeft]`, which concatenate to the undo stream shown above. An undone packet has at most $12$ opcodes, which is the bound on retained storage in [Section 51.7](#streaming-restoration).

## A local normalizer

The normalizer of [Section 51.1](#normalizing-to-a-vine) is a recursive function on the whole tree. The controller computes the same opcodes as a finite-state machine that looks only at the subtree under its cursor.

@decl RotationBST.TreeBuffer.Snapshot.Controller.Mode RotationBST.TreeBuffer.Snapshot.Controller.State

The state is a pointer cursor ([[Pointer.Config]]), a counter `depth` and a mode. The cursor's tree is the machine's tree, not a saved copy. `depth` counts the right-spine descents not yet climbed back. The three modes are `scan` (decide what to do at the current spine node), `promote` (the cursor has just moved to a left child, which must now be rotated up) and `ascend` (normalization is finished, climb back to the root).

@decl RotationBST.TreeBuffer.Snapshot.Controller.choose RotationBST.TreeBuffer.Snapshot.Controller.tick

`choose` is the transition table, and it reads only the mode, the shape of the focused subtree near its root, and whether `depth` is zero:

| mode | focus | action | next mode | depth |
|---|---|---|---|---|
| `scan` | empty or a leaf | none | `ascend` | unchanged |
| `scan` | empty left, nonempty right | `downRight` | `scan` | $+1$ |
| `scan` | nonempty left | `downLeft` | `promote` | unchanged |
| `promote` | any | `rotateLeftChild` | `scan` | unchanged |
| `ascend` | any, depth $d+1$ | `upRight` | `ascend` | $d$ |
| `ascend` | any, depth $0$ | halt | | |

The pending `upRight`s of the recursive normalizer all come at the end of its output, so a counter can replace the recursion. `tick` performs the chosen instruction with [[Multifinger.perform]]. A transition without an opcode only changes the mode. A failing instruction makes `tick` return `none`, so failure cannot pass for a step.

@decl RotationBST.TreeBuffer.Snapshot.Controller.Run

`Run s ops u` is a sequence of ticks from `s` to `u` whose emitted opcodes are `ops`. Silent transitions emit nothing. A run may stop anywhere; this is what lets the recording interleave it with cell writes.

**Theorem (the controller normalizes).** From the root of any tree $t$, in mode `scan` with counter $0$, the controller emits exactly `record t` and reaches the root of the vine, in mode `ascend` with counter $0$, where it halts. Every run replays its emitted opcodes on the cursor. Along every run from the root of $t$, the counter is at most $|t|$; more precisely, the counter plus the size of the focused subtree is at most $|t|$.

@decl RotationBST.TreeBuffer.Snapshot.Controller.Results.normalizes RotationBST.TreeBuffer.Snapshot.Controller.Results.halts RotationBST.TreeBuffer.Snapshot.Controller.Results.replay RotationBST.TreeBuffer.Snapshot.Controller.Results.counter RotationBST.TreeBuffer.Snapshot.Controller.Results.counter_focus

So the controller needs a cursor, two bits of mode and a counter of $O(\log n)$ bits; these are the constant number of registers that the paper allows. The log it emits is not kept: the recording stores it in the cells as it is produced.

## Recording

Recording runs the controller and the buffer finger on the same tree. The controller emits four opcodes; the buffer finger walks to the next cell and writes their encoding there; and so on.

@decl RotationBST.TreeBuffer.Snapshot.Recording.State RotationBST.TreeBuffer.Snapshot.Recording.State.Valid

A recording state has the controller state, the buffer finger's scan state ([[TreeBuffer.Scan.State]]: the tree, the finger's key, the next cell and a direction bit) and the cell contents. It is valid when the two components see the same tree and the scan state is valid. No packet is stored in the state: a packet lives only inside one step of the run below.

@decl RotationBST.TreeBuffer.Snapshot.Recording.Run RotationBST.TreeBuffer.Snapshot.Recording.initial

`Run s u ops work rotations` is a recording execution from `s` to `u`. `ops` is the controller's output, `work` the buffer finger's charged steps and `rotations` the rotations it witnessed. It is built from packets:

- `packet`: the controller runs until it has emitted a chunk of exactly four opcodes, or fewer if it has halted. The scan state follows the tree through the chunk's rotations, at most one per opcode, without moving ([[TreeBuffer.Scan.Trace]] with work $0$). Then the buffer finger performs a cell trace ([[TreeBuffer.Cells.Trace]]) whose only event is one write of `encodeCell chunk`, at a cost `work` that pays for its moves and the write.
- `done`: the controller has halted (after silent transitions only) and no cell remains to be written.

After the controller halts, further packets are empty, so the remaining cells receive the value $0$. `initial tree data` puts the controller at the root in mode `scan`, and the buffer finger at the root's key, as a forward scan from cell $0$, over arbitrary initial contents `data`.

**Theorem (recording).** The following hold for a recording run $s \to u$ that emits $\mathit{ops}$ with buffer work $w$, from a valid state $s$.

- *Production.* If the controller can run from $s$ and halt, emitting at most four opcodes per remaining cell, then there is a recording run that emits these opcodes and ends in that controller state.
- *Projections.* The controller part of the run is a controller run emitting $\mathit{ops}$; the buffer part is a scan trace with the same work and rotations; and at the end the controller is halted and every cell has been visited.
- *Cost.* $w + |\mathit{ops}| \le 4|s| + 4|\mathit{ops}|$, where $|s|$ is the number of nodes.
- *Contents.* The writes are exactly the packed and encoded opcodes, one per remaining cell, in scan order.
- *Snapshot.* From `initial tree data` on a nonempty tree, a run that emits `record tree` leaves the snapshot of `tree` in the cells. Such a run exists, ends with the controller halted at the root of the vine, and costs $w + |\mathit{ops}| \le 20|{\it tree}|$.

@decl RotationBST.TreeBuffer.Snapshot.Recording.Results.produce RotationBST.TreeBuffer.Snapshot.Recording.Results.controller RotationBST.TreeBuffer.Snapshot.Recording.Results.buffer RotationBST.TreeBuffer.Snapshot.Recording.Results.finished

`produce` builds recording runs from controller runs. Its hypothesis `capacity` asks that the remaining cells can hold the opcodes; for a full recording from cell $0$ it is the bound `record t` $\le 4n$. `controller`, `buffer` and `finished` read the run back: whatever happened in between, the opcodes are the controller's, and the buffer finger's steps form a legal scan trace in the sense of [Chapter 50](tree-buffers.html).

@decl RotationBST.TreeBuffer.Snapshot.Recording.Results.cost RotationBST.TreeBuffer.Snapshot.Recording.Results.cells RotationBST.TreeBuffer.Snapshot.Recording.Results.stored RotationBST.TreeBuffer.Snapshot.Recording.Results.snapshot

`cost` is the scan bound [[TreeBuffer.Scan.Results.total]] of [Chapter 50](tree-buffers.html), the formal Lemma 9: a scan over $n$ cells costs at most $4n$ plus $3$ per rotation performed by the other finger, and the rotations are among the emitted opcodes. With $|\mathit{ops}| \le 4n$, this gives the $20n$ of `snapshot`. `cells` describes the writes as [[TreeBuffer.Cells.Event]]s: the keys are the scan's remaining requests, in order, and the values are `pack` of the opcodes, encoded. `stored` excludes the empty tree, where there are no cells and the initial buffer position is only a totalized value; `snapshot` has no such hypothesis, because `Stored` is vacuous on the empty tree.

## Streaming restoration

Restoration starts from the vine, which recording leaves behind and which normalization produces from any tree. It runs the undo stream of the saved log, read from the cells as it goes.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.State RotationBST.TreeBuffer.Snapshot.Streaming.State.Valid RotationBST.TreeBuffer.Snapshot.Streaming.remaining

A streaming state has two cursors on the same tree, the *replay cursor* (a [[Pointer.Config]]) and the buffer finger (a scan state), and the current *packet*, the opcodes of one undone cell not yet executed. Validity asks for the common tree, a valid scan, and a packet of at most $12$ opcodes. `remaining data s` is the stream still to be executed: the packet, followed by the undone packets of the cells the scan has not read yet, in its order. It is a specification of what the machine will do. The machine does not store it.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Step RotationBST.TreeBuffer.Snapshot.Streaming.Trace

A step is one of three kinds, and each applies only in its own situation.

- `navigate`: the packet is empty, and the buffer finger takes one step toward its next cell, by the cell rule of [Chapter 50](tree-buffers.html). One unit of buffer work.
- `read`: the packet is empty, and the buffer finger is on its next cell. It reads the value and the packet becomes the undone decoded packet. One unit of buffer work.
- `execute`: the packet is nonempty. The replay cursor performs its first opcode, the scan state follows the tree through the zero or one rotation this causes, and the buffer finger stays on its key. One unit of replay work.

`Trace data s t w p r` composes steps, adding the buffer work `w`, the replay instructions `p` and the rotations `r` seen by the scan. The cells are the same `data` throughout: restoration never writes.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.potential RotationBST.TreeBuffer.Snapshot.Streaming.State.Done RotationBST.TreeBuffer.Snapshot.Streaming.initial RotationBST.TreeBuffer.Snapshot.Streaming.rootPosition

The potential is four units per remaining opcode plus the scan potential [[TreeBuffer.Scan.potential]], the cost of the rest of the scan if no further rotation occurred. Executing an opcode uses one unit and can raise the scan potential by at most three, since a rotation lengthens the scan's remaining route by at most a constant; navigating and reading lower the scan potential. `Done` means the packet is empty and every cell has been read. `initial tree position` puts the replay cursor at the root, the buffer finger on key `position`, the scan descending from the last cell, and the packet empty. `rootPosition tree` is the key of the root, $0$ for the empty tree, where no cell is ever accessed.

**Theorem (streaming).** Let $s$ be a valid streaming state whose remaining stream replays legally from its cursor to some target.

- *Progress and termination.* If $s$ is not done, some step applies. Some trace from $s$ reaches a done state with $w + p$ at most the potential of $s$.
- *Amortization.* Along every trace $s \to t$ from a valid state, $w + p + \Phi(t) \le \Phi(s)$.
- *Projections.* The replay cursor of every trace performs a [[Pointer.Trace]] of exactly $p$ instructions, and the buffer finger a scan trace with work $w$ and the $r$ rotations.
- *Completion.* A trace that ends in a done state has executed exactly the remaining stream of $s$, and $p$ is its length.
- *Space.* Along every trace from a valid state, the packet has at most $12$ opcodes, and the scan's counter and position stay below the number of nodes.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Results.progress RotationBST.TreeBuffer.Snapshot.Streaming.Results.finish RotationBST.TreeBuffer.Snapshot.Streaming.Results.cost

`progress` and `finish` assume that the remaining stream is executable (`executable`), which is the case for a stream of undone cells started on the right tree; without it, an `execute` step could fail.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Results.physical RotationBST.TreeBuffer.Snapshot.Streaming.Results.buffer RotationBST.TreeBuffer.Snapshot.Streaming.Results.completed RotationBST.TreeBuffer.Snapshot.Streaming.Results.space

`completed` is what makes the existential statements below meaningful: *every* completed trace from a given state ends with the cursor where the remaining stream leads, so all completed restorations agree. `space` is the bounded working storage: one packet of at most twelve opcodes, the buffer finger's key and its counter.

**Theorem (restoration from the vine).** If the cells hold the snapshot of $s$, the streaming machine started on the vine with $|s|$ nodes, with the buffer finger at its root, completes and ends with the tree $s$ and the cursor at its root. It executes exactly the undo of the log of $s$, and its total work $w + p$ is at most $52|s|$.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Results.restore

The constant is the initial potential: $4 \cdot 12n$ for the undo stream and at most $4n$ for the scan.

## Save and load

The two operations of the tree state buffer combine the machines above.

@decl RotationBST.TreeBuffer.Snapshot.Recording.Save

`Save data tree finalData cost` says: a recording run from `initial tree data` ends with the controller at the root, a streaming restoration from the resulting cells and the resulting tree (the vine) is done, its cursor is at the root of `tree` again, and `finalData` is what the recording wrote. The cost is the controller's opcodes, the recording's buffer work, the restoration's buffer work and its replay instructions. At the change of phase, the buffer finger stays on its key, and only its scan direction and counter are reset.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Load

`Load data current final cost` says: the controller normalizes `current` into the vine, while the buffer finger stays on the root's original key and only follows the rotations; then the streaming machine runs from the vine with the buffer finger at that key, until it is done with its cursor at the root of `final`. The cost is the normalizer's opcodes plus the restoration's buffer work and instructions. The saved tree does not appear among the inputs of the machines. It is `final`, an output.

**Theorem (shape-preserving save).** For every tree $t$ with $n$ nodes and all initial cell contents, there is a save of $t$ whose final cells hold the snapshot of $t$, at cost at most $72n$.

@decl RotationBST.TreeBuffer.Snapshot.Recording.Results.save

The constant is $20n$ for the recording plus $52n$ for the restoration.

**Theorem (streaming load).** Let the cells hold the snapshot of a tree $s$, and let the current tree have as many nodes as $s$, say $n$. Then a load from the current tree ends in $s$, at cost at most $56n$.

@decl RotationBST.TreeBuffer.Snapshot.Streaming.Results.load

The constant is $4n$ for the normalization plus $52n$ for the restoration. The normalization costs the buffer finger nothing, since it does not move. These are the two theorems of the headline.

## On shared nodes

In the machines above, the cells are a function from keys to values, and each finger is described by its own view of the tree. The combined tree runs on a single labelled tree whose nodes carry both routing words and payload fields, with two fingers on it: [[TreeBuffer.Shared.State]] of [Chapter 50](tree-buffers.html), with values in `Nat` and two fingers. Finger $0$ is the tree finger (the normalizer, or the replay cursor), and finger $1$ is the buffer finger.

@decl RotationBST.TreeBuffer.Snapshot.Recording.Refinement.Represents RotationBST.TreeBuffer.Snapshot.Streaming.Refinement.Represents RotationBST.TreeBuffer.Snapshot.Streaming.Refinement.Reads

The two `Represents` relations couple a shared state to a recording state or to a streaming state: the shared state is valid for the cells, its tree without labels is the model's tree, finger $0$ is on the key of the model's tree cursor, and finger $1$ on the buffer finger's key. `Reads data events` says that every cell event of an execution is a read returning the value in `data`. Restorations, and the worker instructions of the combined tree, satisfy it, so they never overwrite the snapshot.

@decl RotationBST.TreeBuffer.Snapshot.Startup.Execution

`Startup.Execution tree n fields data final events total` is the composition used once, before the first request: the node initialization of [Chapter 50](tree-buffers.html) (`Nodes.Initialization`, with fuel $8n$) computes the routing words of every node from arbitrary initial ones `fields`, returns to the root, and halts; then an arbitrary shared trace runs from the initialized tree, with both fingers at the original root, to `final`, with cell events `events` and cost `work`. The total cost is the sum. The definition does not say what the second phase does. The theorems that use it do.

Those theorems are internal to the library, in the proof files of `Structures/TreeBuffer/Snapshot`. On a valid shared state with both fingers at the root of a nonempty tree, a shared-node save (`Recording.Refinement.save`) costs at most $1080n$ and a shared-node load (`Streaming.Refinement.load`) at most $840n$, including routing and the maintenance of routing words through rotations. With initialization, `Startup.save` and `Startup.load` cost at most $1088n$ and $848n$. Through them, [[Combo.Refinement.Results.restart]] restores a worker's initial tree at cost at most $841n$, and [[Combo.Online.Prepared]] records the bound $1088n$ for the one-time save before the first request ([Chapter 36](combo-online.html)).

::: caveat Compared with the paper
- **Two fingers.** Lemma 10 gives TSB(M) $O(k)$ fingers for a structure M with $k$ fingers. Here the snapshot operations use two fingers on the shared tree. In the combined tree, the worker's instructions also run on finger $0$, and a finger hand ([Chapter 43](finger-hands.html)) simulates the two-finger machine with the single cursor of the pointer machine ([Chapter 36](combo-online.html)).
- **Twelve bits.** The paper allows $O(\log n)$ bits per node and suggests packing or multiple buffers when $n$ cells are not enough. The normalization log has at most $4n$ opcodes, so a constant twelve bits per node suffice, and a single buffer.
- **Cost model.** The headline costs count the tree finger's instructions and the buffer finger's moves and cell visits, in the buffer model of [Chapter 50](tree-buffers.html). The constants $72$ and $56$ are not optimized. The shared-node constants are larger, since each routing step and rotation update has its own cost there.
- **Existence of executions.** The theorems state that an execution exists. The machines are local: the controller is a function of its state, and a streaming step applies only in its own situation. The theorem `completed` shows that every completed restoration ends in the same tree.
- **Storage beyond the snapshot.** The storage clauses of the combining theorem (that the whole structure fits in $O(\log n)$ bits per node and $O(1)$ registers) are not formalized ([Chapter 33](combining.html)). This section only bounds the snapshot payload, the packet and the counters.
:::
