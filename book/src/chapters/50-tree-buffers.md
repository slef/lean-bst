# Tree buffers

ComboBST ([Chapter 33](combining.html)) runs two online BST algorithms on one physical tree, in alternating rounds. Every round starts from the same initial tree $T$, so at the end of a round the structure must turn whatever tree the interrupted worker left behind back into $T$. It has no memory outside the tree beyond a constant number of registers. Where does it keep the description of $T$? Demaine, Iacono, Langerman and Özkan (*Combining binary search trees*, Section 3) answer: in the nodes themselves. Each node may carry $O(\log n)$ bits of augmented data, so the $n$ nodes together form a *buffer* of $n$ cells. Their Definition 8 stores the $j$-th cell in the $j$-th node in inorder, and a buffer finger walks from cell to cell by inorder traversal.

The difficulty is that the tree changes shape while the buffer is in use. When the tree state is loaded, a second finger rotates the tree while the buffer finger reads the saved instructions, and every rotation can lengthen the buffer finger's route. Their Lemma 9 says this costs little: an inorder traversal interleaved with $r$ rotations by other fingers takes $O(n + r)$ time. Lemma 10 then makes saving and loading the tree state cost $O(n)$, because a linear-time normalization performs only $O(n)$ rotations.

This chapter formalizes the buffer: the scan and its cost, the cells and their reads and writes, the node records that hold keys, routing bounds and cells, and a shared tree in which several persistent fingers act on the same nodes. The snapshot, the saved instruction log packed into the cells, is the subject of [Chapter 51](snapshots.html).

```headline tree-buffers-scan
title: An inorder scan interleaved with $r$ rotations costs at most $4n + 3r$
source: Demaine, Iacono, Langerman and Özkan, *Combining binary search trees* (2013)
theorems: TreeBuffer.Scan.Results.cost TreeBuffer.Scan.Results.total TreeBuffer.Scan.Results.completion

Let $T$ be a tree with $n$ nodes, whose keys are the inorder ranks $0,\dots,n-1$. A scan finger sits on any node, and the cells still to visit are either a suffix $b, b+1, \dots, n-1$ in increasing order or a prefix $b-1, \dots, 1, 0$ in decreasing order. A scan step either moves the finger one edge along a shortest path, in the current tree, toward the next pending cell, or *visits* that cell once the finger is on it. Both cost one unit. Arbitrary rotations of the tree, performed by someone else, may be interleaved between any two scan steps. If a trace contains $r$ such rotations, the scan's work is

$$\text{moves} + \text{visits} \;\le\; 4n + 3r,$$

and the total including the rotations is at most $4n + 4r$. Any such partial trace can be completed, with no further rotations, so that every pending cell is visited and the whole scan still costs at most $4n + 3r$.

This is the paper's Lemma 9, with explicit constants. The bound holds for any start position of the finger and any boundary $b$, in either direction.
```

## Overview

### Do you need this chapter?

The statements of the ComboBST results, [Chapter 33](combining.html) to [Chapter 36](combo-online.html), and of the combined finger theorem in [Chapter 38](combined-finger.html) are about pointer-machine executions of the hand tree ([Chapter 43](finger-hands.html)). They do not mention cells or scans. The prepared policy ([[Combo.Online.Prepared]]) does carry a proof that its startup is a legal shared-node execution ([[Snapshot.Startup.Execution]]), and its state ([[Combo.Online.State]]) carries a shared tree. So the definitions of the node and shared layers, the last two sections of this chapter, are on the reading paths of those headline results, together with the event type [[TreeBuffer.Cells.Event]]. A reader who only wants to confirm those results needs just one fact from here: a shared-node trace is made of legal pointer moves, cell reads and writes, and rotations maintained by a fixed local program, each with a fixed charge. The scan and cell layers are proof machinery. Read them to see why restoring the initial tree costs $O(n)$.

### Four layers

The library builds the buffer in four layers, from the most abstract to the most concrete. All live in `Structures/TreeBuffer`.

| Layer | State | What a step costs | Main theorem |
|---|---|---|---|
| Scan (`Scan`) | tree, finger key, boundary, direction | move or visit: 1; rotation: counted apart | [[TreeBuffer.Scan.Results.cost\|cost]]: $4n+3r$ |
| Cells (`Cells`) | scan state and one payload per key | navigate, read or write: 1 | [[TreeBuffer.Cells.Results.write_completed\|write_completed]], [[TreeBuffer.Cells.Results.read_completed\|read_completed]] |
| Nodes (`Nodes`) | one labelled node: key, interval bounds, cell | route: 4; cell read or write: 1; maintained rotation: 15 | used by the shared layer |
| Shared (`Shared`) | one labelled tree and $k$ persistent fingers | as for nodes, plus a bare move: 1 | used by [[Combo.Refinement.Results.worker_step]] and the snapshot |

The scan is a model of Lemma 9 and nothing else: it only knows which key the finger is on and which cells remain. The cell layer adds the data. The node layer says how that data, together with the routing information the finger needs to find its way, is laid out in actual node records. The shared layer puts several fingers on the same records: ComboBST uses two fingers, finger 0 for the worker or the replay and finger 1 for the buffer scan ([[Combo.Refinement.Represents]], [[Snapshot.Streaming.Refinement.Represents]]).

Cells are attached to *keys*, which are inorder ranks. A rotation preserves the inorder, so it moves every cell along with its node and never changes which cell is the $j$-th. This is the paper's design, and it is what makes rotations by other fingers harmless to the data. They only lengthen the routes.

### Where it is used

- [Chapter 51](snapshots.html) saves a tree by normalizing it to a right path, writing the opcode log into the cells with a forward scan, and undoing the normalization ([[Snapshot.Recording.Results.save]], at most $72n$). It loads a saved tree by normalizing the current tree and replaying the inverse log while a reverse scan reads the cells. The replay's rotations interrupt the scan, and the scan bound pays for them ([[Snapshot.Streaming.Step]], [[Snapshot.Streaming.Results.load]], at most $56n$).
- [Chapter 36](combo-online.html) runs the ComboBST controller on a shared tree with two fingers. Each worker step costs at most $15$ shared units ([[Combo.Refinement.Results.worker_step]]) and a restart costs at most $841n$ ([[Combo.Refinement.Results.restart]]).

## The scan

### State

@decl TreeBuffer.Scan.State TreeBuffer.Scan.State.Valid

A scan state is the current `tree`, the key `position` of the buffer finger, a boundary `next`, and a direction bit `descending`. The finger is a key, that is an inorder rank, as for the fingers of [Chapter 10](fingers.html). The tree is part of the state because other fingers may rotate it. In a real structure it is the shared tree, not a copy. A state is valid when the finger is on an existing node and the boundary is at most $n$.

@decl TreeBuffer.Scan.State.requests TreeBuffer.Scan.State.target TreeBuffer.Scan.State.afterVisit

The boundary determines the pending cells:

- forward ($\texttt{descending} = \texttt{false}$): `next` is the first unvisited cell, and the pending list is $\texttt{next}, \texttt{next}+1, \dots, n-1$;
- reverse ($\texttt{descending} = \texttt{true}$): `next` is one past the first unvisited cell, and the pending list is $\texttt{next}-1, \dots, 1, 0$.

`target` is the head of that list, and `afterVisit` advances the boundary by one in the scan's direction. `requests` is a specification quantity: the machine only stores the key, the counter and the bit. Note that `target` is totalized. A reverse scan with $\texttt{next} = 0$ has no pending cell, and its target is $0 - 1 = 0$ in natural numbers, but no step uses it, because both scan steps require a nonempty pending list.

### Steps

@decl TreeBuffer.Scan.Step TreeBuffer.Scan.Trace

A step carries two counters, the scan's own work and the number of external rotations.

- `move` follows one pointer, a parent or child edge of the current tree ([[Pointer.Move]]), from the finger's node to a node $y$. It is allowed only if it brings the finger strictly closer to the target: the edge distance ([[LazyFinger.distance]]) from $y$ to the target is one less than from the current key. So the finger always moves along a shortest path in the *current* tree. It costs one unit of work.
- `visit` is allowed when the finger is on the target. It consumes the target and costs one unit of work. This is where the cell layer will read or write.
- `rotate` is any rotation of the tree ([[RotationBST.Rotate]]). It leaves the finger on the same key and costs no scan work, only one in the rotation counter. Nothing restricts where the rotation happens. The paper's rotations "by other fingers" are a special case, and a rotation at the scan finger's own node is allowed too.

A trace concatenates steps and adds both counters. The paper describes the traversal as moving to the inorder successor. The shortest-path rule is the same thing when the tree is fixed, and it stays meaningful when the tree changes in between: after a rotation, the finger simply continues along a shortest path in the new tree.

### The potential

@decl TreeBuffer.Scan.potential

The potential of a scan state is the lazy-finger cost ([[LazyFinger.costFrom]], [Chapter 15](lazy-finger.html)) of its pending cells, starting from the current finger: one unit per pending cell, plus the distance from each cell to the next. If no more rotations happen, it is the work that remains: each move or visit lowers it by one.

The proof of the bound works with the interval decomposition of the lazy-finger cost. Each node $v$ of the tree has a key interval, the keys of its subtree, and the edge above $v$ is crossed exactly when consecutive positions of the route lie on different sides of that interval's boundary. So the potential is the number of pending cells plus, for each node, the number of times the sequence (position, pending cells) enters or leaves its interval ([[LazyFinger.crossings]], [[LazyFinger.intervalCost]]). A monotone sequence of cells, started from an arbitrary position, crosses the boundary of any interval at most three times. For example, it may leave the interval, enter it again, and leave it for good. This gives the two facts the proof needs:

- the potential is at most $n + 3n = 4n$;
- a rotation of $x$ over its parent $y$ gives $x$ the old interval of $y$ and gives $y$ a new one, so the set of subtree intervals loses one interval and gains one. The potential therefore increases by at most $3$.

Each move or visit decreases the potential by one. Summing over a trace gives work $\le 4n + 3r$.

The paper's proof of Lemma 9 counts at most $2n$ for an inorder traversal and at most one extra step per rotation. The library's constants are larger for three reasons: visits are charged too, the finger may start anywhere rather than at the first cell, and the rotation bound is proved for the whole potential at once rather than for a single path.

### Results

@decl TreeBuffer.Scan.Results.initial

The pending scan of any valid state, forward or reverse, has potential at most $4n$.

@decl TreeBuffer.Scan.Results.cost TreeBuffer.Scan.Results.total

These are the headline bounds. For every trace from a valid state with $r$ rotations, the scan's work is at most $4n + 3r$, and the work plus the rotations is at most $4n + 4r$. Here $n$ is the size of the starting tree; rotations do not change it. Both theorems hold for every prefix of a scan, finished or not.

@decl TreeBuffer.Scan.Results.progress TreeBuffer.Scan.Results.finish TreeBuffer.Scan.Results.completion

The bounds would be empty if the scan could get stuck. `progress` says it never does: from a valid state with a pending cell, some step of work one exists, a move or a visit. `finish` runs a whole scan without rotations, within the potential. `completion` extends any interleaved partial trace to a finished one, with no further rotations, and the extended trace still satisfies the $4n + 3r$ bound.

@decl TreeBuffer.Scan.Results.visits

Conversely, work cannot be avoided: a trace that consumes $j$ pending cells has done at least $j$ units of work. Rotations and moves never consume a cell, so a scan cannot skip cells for free.

### Choosing a move locally

The `move` rule is stated with the global distance function, which a real finger cannot compute. The next three theorems show that the move can be chosen by looking only at fields stored at the finger's node: its key and the bounds $[\mathit{low}, \mathit{high})$ of its subtree's key interval. [[Pointer.Routing.choose]] goes to the parent if the target is outside the interval, and otherwise left or right according to the key.

@decl TreeBuffer.Scan.Results.route TreeBuffer.Scan.Results.fields_route TreeBuffer.Scan.Results.labelled_route

When the finger is not yet on the target:

- `route`: for any correct view of the interval at the cursor ([[Pointer.Routing.View.Valid]]), the pointer chosen by [[Pointer.Routing.next]] is a legal scan move.
- `fields_route`: the same, with the view read from a field array that is correctly initialized ([[IntervalMetadata.label]]).
- `labelled_route`: the same, for a labelled cursor that stores keys and bounds in its nodes. The routing step [[IntervalMetadata.Access.route]] charges $4$ (three word reads and one pointer move), and the cursor stays canonical afterwards.

These theorems hold for any tree shape, so they apply after any number of rotations, as long as the bounds were maintained. The maintenance is the node layer's job.

## Cells

The cell layer adds the payloads. It is still a specification: the payloads are a function of the key, and the tree is the scan's tree.

@decl TreeBuffer.Cells.State

`data x` is the cell of the node with key $x$. Rendered on the tree by [[Metadata.label]], it is the paper's layout: the $j$-th cell in the $j$-th node in inorder. Values at keys outside $\{0,\dots,n-1\}$ exist because `data` is a total function, but no operation can read them.

@decl TreeBuffer.Cells.Event TreeBuffer.Cells.Event.key TreeBuffer.Cells.Event.value

An event records an observable cell access, a read or a write, with its key and value. The event list of a trace is a specification of what was read and written, not storage of the machine.

@decl TreeBuffer.Cells.Step TreeBuffer.Cells.Trace

The steps are the scan's steps, with the visit split in two:

- `navigate` is a scan move. It costs one and emits no event.
- `read` visits the target and emits the target's current value. It costs one.
- `write value` visits the target, replaces its cell by `value`, and emits the write. It costs one.
- `rotate` is an external rotation. The payloads are unchanged, since they are indexed by keys.

So the cell layer can only read or write the cell under the finger, and only in scan order. A trace adds up the work and the rotations, as before, and collects the events.

@decl TreeBuffer.Cells.writeMany TreeBuffer.Cells.effect

Two specification functions describe the data after a stream of accesses. `writeMany target keys data` sets each key in `keys` to its `target` value, in order. `effect data events` applies a list of events: reads change nothing, and writes update one key. No theorem of the reading interface mentions them; the `writes` theorem below states their content directly.

### Local access

@decl TreeBuffer.Cells.Results.read_local TreeBuffer.Cells.Results.write_local

A read returns the cell of the finger's node, $x = $ `position` and value `data x`. The read is also located in the labelled tree ([[Metadata.At]]). A write changes only the finger's cell: the labelled tree changes by one payload update ([[Metadata.Write]]) and every other key keeps its value.

### Order and cost

@decl TreeBuffer.Cells.Results.order TreeBuffer.Cells.Results.cost

The keys of the events of a trace are exactly the pending cells consumed, in scan order: the pending list before the trace is the event keys followed by the pending list after it. And a cell trace obeys the scan bound: work at most $4n + 3r$, reads and writes included.

### Complete passes

@decl TreeBuffer.Cells.Results.read_completed TreeBuffer.Cells.Results.write_completed TreeBuffer.Cells.Results.writes

These lift a finished scan trace, rotations included, to a cell trace with the same work and the same rotations.

- `read_completed`: reading at every visit produces one read event per pending cell, in order, with the stored values, and leaves the data unchanged.
- `write_completed`: writing a target function at every visit produces one write per pending cell, in order. The final data agree with the target on the pending cells and with the old data elsewhere.
- `writes`: for any trace whose events are writes of `target` at a list of keys, the final cell of $x$ is `target x` if $x$ is in the list and the old value otherwise.

The snapshot load of [Chapter 51](snapshots.html) uses the read direction with rotations interleaved. The save uses the write direction.

@decl TreeBuffer.Cells.Results.read_all TreeBuffer.Cells.Results.write_all TreeBuffer.Cells.Results.read_reverse

Whole-buffer passes without interleaved rotations. From a finger anywhere in the tree, a forward read of all $n$ cells, a forward write of all $n$ cells, or a reverse read of all $n$ cells costs at most $4n$ work. The write sets the cells of the keys below $n$ to the target values and leaves the rest unchanged.

@decl TreeBuffer.Cells.Results.write_next

One cell at a time: from a valid state with a pending cell, the scan can navigate to the next pending cell and write it, with exactly that one write event and no rotation. The theorem does not bound the work of this single step: the finger may have to travel far. Its work is bounded by `cost` when it is part of a longer trace from a valid state.

## Physical nodes

The two layers above speak of keys and of a function `data`. The node layer says what a node actually stores, and how a finger moves, reads, writes and rotates using only the fields of the nodes it touches. A node is a record in a labelled tree ([[LabelledTree]]), addressed by a zipper cursor ([[LabelledCursor.Config]]), as in [Chapter 12](replay.html).

@decl TreeBuffer.Nodes.Entry TreeBuffer.Nodes.Entry.routing TreeBuffer.Nodes.Entry.payload

A node entry stores three things: its key, the bounds $[\mathit{low}, \mathit{high})$ of its subtree's key interval ([[IntervalMetadata.Bounds]]), and its buffer cell. The projection `routing` forgets the cell and gives the routing annotation of [Chapter 12](replay.html). The projection `payload` forgets the bounds and gives the key and cell, the layout of [[Metadata.label]]. In ComboBST the cell type is `Nat`: a cell holds a packet of opcodes ([Chapter 51](snapshots.html)). The Lean model does not bound the size of the words; the storage clauses of the paper are not formalized.

@decl TreeBuffer.Nodes.label TreeBuffer.Nodes.Routing TreeBuffer.Nodes.Stored

`label data t lo` is the canonical layout of a tree whose keys start at `lo`: every node stores its rank, the exact interval of its subtree, and its cell. `Routing c` says that the routing projection of a cursor's tree is canonical, and `Stored data c` says that its payload projection is the layout of `data`. These are representation invariants used in the proofs, not operations.

### Maintained rotations

A rotation changes the subtree intervals of the two nodes involved. If the bounds are not updated, routing breaks. The update is local: the new bounds of both nodes can be computed from their old keys and bounds.

@decl TreeBuffer.Nodes.State TreeBuffer.Nodes.State.routing TreeBuffer.Nodes.writeBounds TreeBuffer.Nodes.tick TreeBuffer.Nodes.run TreeBuffer.Nodes.maintain

A node-machine state is a cursor and two scratch registers, `child` and `parent`, each holding a key and its bounds. `State.routing` forgets the cells and gives the state of the routing-only maintenance machine ([[IntervalMetadata.Maintenance.State]]). `tick` executes one instruction of that machine ([[IntervalMetadata.Maintenance.Op]]): a pointer opcode, a read of the current node's key and bounds into a register, or a write of new bounds into the current node with `writeBounds`. The cell is carried along by every pointer operation and never touched by a bounds write. `run` executes a list of instructions, and `maintain side` runs the fixed program [[IntervalMetadata.Maintenance.program]] for a left or right rotation. Starting at the child, it reads the child, goes up, reads the parent, comes back down, rotates, rewrites the bounds of the promoted and the demoted node, and returns to the promoted node.

The program performs six word reads, four word writes, four moves and one rotation. Its charge is $15$, the cost of a maintained rotation in the shared layer below. The proof files show that `maintain` agrees with the routing-only program on the routing projection, performs exactly a rotation on the payload projection, keeps both invariants, and starts from any scratch values (`maintain_routing`, `maintain_payload`, `maintain_preserves`, `maintain_scratch` in `Nodes/Maintenance.lean`).

### Routing and cell access

@decl TreeBuffer.Nodes.route TreeBuffer.Nodes.readCell TreeBuffer.Nodes.writeCell

`route target c` reads the current node's key and bounds, chooses a direction with [[Pointer.Routing.choose]], and follows one pointer: down to a child, or up through the zipper's top frame. It charges $4$, like the routing-only [[IntervalMetadata.Access.route]], and fails at the target itself or at the root when the target is outside. `readCell` returns the current node's cell for one unit and reads no routing field. `writeCell` replaces the current cell for one unit and keeps the key and bounds. The proof files show that these three operations realize the `navigate`, `read` and `write` steps of the cell layer on a correctly labelled tree (`navigate_step`, `read_step`, `write_step` in `Nodes/Bridge.lean`), and that `maintain` realizes its `rotate` step, with the scan finger's key unchanged (`rotation_step`).

### Initializing the bounds

When ComboBST starts, the nodes of the initial tree hold their keys and some cells, but their bound words may contain anything. A traversal writes the correct bounds before the first save.

@decl TreeBuffer.Nodes.Initialization.raw

`raw fields data t lo` is the starting layout: each node stores its correct key and its cell, and arbitrary bounds `fields key`.

@decl TreeBuffer.Nodes.Initialization.State TreeBuffer.Nodes.Initialization.tick TreeBuffer.Nodes.Initialization.Run

The initializer is the stackless traversal of the routing-only initializer ([[IntervalMetadata.Initialization.tick]]), run on the actual combined nodes. Its state is a cursor, one pending pair of bounds, and a mode ([[IntervalMetadata.Initialization.Mode]]):

- `write` stores the pending bounds into the current node (charge $2$) and switches to `left`;
- `left` descends into a nonempty left child (charge $4$), with pending bounds $[\mathit{low}, \mathit{key})$ computed from the parent's stored fields, or switches to `right` if there is none (charge $1$);
- `right` does the same on the right, with $[\mathit{key}+1, \mathit{high})$, or switches to `up`;
- `up` returns to the parent (charge $1$) and resumes in `right` mode if it came from the left.

It keeps no stack: the ancestors' information is in the parent links and in the bounds already written. Each step keeps every key and cell. `Run` is a finite run, with its total charge.

@decl TreeBuffer.Nodes.Initialization.initial TreeBuffer.Nodes.Initialization.runLoop TreeBuffer.Nodes.Initialization.runFuel

`initial tree n` starts at the root in `write` mode with pending bounds $[0, n)$. The universe size $n$ is a scalar input, not computed from the tree. `runFuel fuel` is the executable loop: it runs until no step applies, and fails if more than `fuel` steps would be needed. Every step charges at least one, so a fuel equal to a bound on the charge is enough. The proof file `Nodes/Initialization/Execution.lean` shows that, when $n$ is the size of the tree, the loop with fuel $8n$ ends at the root with the canonical layout `label data tree 0` and total charge at most $8n$ (`complete`). The startup of ComboBST, [[Snapshot.Startup.Execution]], requires exactly this run and then a shared-node trace from its result.

## Shared nodes

The last layer puts several fingers on one labelled tree. This is the physical counterpart of the multi-finger model of [Chapter 10](fingers.html), with node records instead of bare nodes.

@decl TreeBuffer.Shared.State TreeBuffer.Shared.State.Valid TreeBuffer.Shared.View

A shared state is one labelled tree of node entries and a key for each of its `fingers` persistent fingers. As in the multi-finger model, a finger is the key of an existing node, so a rotation, which preserves keys, keeps every finger on its node. `Valid s data` says that the routing projection is the canonical interval annotation, that the payload projection is the layout of `data`, and that every finger is on a node. The data are a parameter of validity, not stored separately: the cells *are* the payload projection. `View s i c entry` says that the cursor `c` is finger `i`'s position in the shared tree, reading `entry`. The cursor is a proof witness of where the finger is, not a separate copy of the tree.

@decl TreeBuffer.Shared.Step TreeBuffer.Shared.Trace

A step acts at one finger `i`, emits at most one event, and has a charge:

| Step | Effect | Charge |
|---|---|---|
| `move op` | follow one parent or child pointer ([[Pointer.Move]] on the erased cursors), without reading fields | 1 |
| `navigate target` | one `Nodes.route` step toward `target` | 4 |
| `read` | read finger `i`'s cell; nothing changes | 1 |
| `write value` | write finger `i`'s cell in place | 1 |
| `rotate side` | run `Nodes.maintain side` at finger `i` | 15 |

Moves and navigation update only finger `i`. Writes and rotations change the shared tree, and every finger keeps its key. A trace collects the events and adds the charges. Its event list is a specification. The runtime state is the tree, the fixed number of fingers, and the scratch words of the current local operation.

The two kinds of movement serve the two kinds of fingers. A worker finger follows the opcodes of its algorithm with `move`, and the buffer finger routes itself with `navigate`.

@decl TreeBuffer.Shared.State.erase

Erasing forgets the routing and cell fields and keeps the tree shape and every finger, giving a [[Multifinger.State]]. The proof files show that a shared trace erases to a multi-finger trace ([[Multifinger.Trace]]) with no more instructions than its charge (`Trace.erase` in `Shared/Erasure/Traces.lean`). This is how ComboBST's physical execution, which is described on shared nodes, becomes a multi-finger execution and then, through the hand of [Chapter 43](finger-hands.html), a pointer-machine execution.

@decl TreeBuffer.Shared.CellRefinement.Represents

`Represents actual model i` relates a shared state to a cell-layer state: the shared state is valid for the model's data, its shape is the scan's tree, and finger `i` is the scan finger. The proof files lift every rotation-free cell trace to a shared trace with the same events, at most four times the work, and with all other fingers unmoved (`CellRefinement.trace` in `Shared/CellRefinement/Traces.lean`). The factor four is the cost of `navigate`. No theorem of the reading interface mentions this relation; the snapshot chapter uses the lifting in its proofs.

@decl TreeBuffer.Shared.Requests.Visit TreeBuffer.Shared.Requests.Execution

Requests on shared nodes. A `Visit s t x events cost` is a shared trace from `s` to `t` that passes through a state in which some finger is on key $x$. The work after that moment is part of the visit and is charged. An `Execution` serves a list of requests by consecutive visits, and charges one unit per request plus all pointer, cell, routing and maintenance work. This is the convention of [[Multifinger.Execution]] and of the rest of the library. The proof files show that an execution erases to a multi-finger execution of the same requests, with no larger cost (`Requests.Execution.erase`). ComboBST's per-request transition ([[Combo.Online.Transition]]) records such a visit, whose events are all correct reads of the saved cells.
