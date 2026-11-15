# Real-world implementations

The models of this part count BST operations: moves, rotations and requests. Nothing else is charged. An online algorithm of [Chapter 5](online.html) receives the whole request history at every step, and may compute anything from it for free. That is the right model for competitive analysis, but it says nothing about the memory and the time that an implementation spends to choose its operations.

@bose2012 observe that almost all BST implementations in the literature have three more properties: they work in the pointer machine model, they use no more space than the tree itself plus $O(1)$ words of balance information per node and $O(1)$ working variables, and they generate their BST operations in time proportional to the BST cost. @demaine2013 define a *real-world BST*, crediting @bose2012 for the term, by the space conditions alone: one that can be implemented with a constant number of registers of $O(\log n)$ bits and $O(\log n)$ bits of data at each node. Both papers prove transformations that preserve these properties: the deamortization (Theorem 7 of @bose2012, [Chapter 37](deamortization.html)) preserves all three, and ComboBST and the one-finger simulation of several fingers (Theorems 3 and 5 of @demaine2013, [Chapter 23](combination.html)) preserve the space conditions.

This chapter makes the notion precise. A *real-world machine* is a finite program with a fixed number of word registers, run on a tree whose nodes hold a fixed number of words, with one persistent finger. Every instruction costs one step of running time, and only moves and rotations count as BST operations. The second half of the chapter compiles every such program into a single program for the pointer machine of @tarjan1979, with a constant factor in running time.

```headline real-world-trace
title: A real-world machine runs online, its BST operations form a pointer trace, and they cost at most its running time
theorems: RealWorld.Results.physical RealWorld.Results.bst_cost RealWorld.Results.causal

Fix a real-world machine $p$. If $p$ runs from state $s$ to state $t$ in $T$ steps, with $k$ of them moves or rotations, then those $k$ instructions form a trace of the single-cursor machine of [Chapter 7](pointer.html) from the tree and cursor of $s$ to those of $t$, with the node data forgotten, and $k \le T$. The machine receives one request at a time, and two executions of the same requests from the same state end in the same state with the same costs.

In Lean, machines are [[RotationBST.RealWorld.Machine]], their states [[RotationBST.RealWorld.State]], runs [[RotationBST.RealWorld.Run]], and traces [[RotationBST.Pointer.Trace]].
```

```headline real-world-compiler
title: Every real-world machine compiles to one program of Tarjan's pointer machine, with at most 19 instructions per step and 3 per request
theorems: RealWorld.Linked.Results.primitive RealWorld.Compiler.Results.response RealWorld.Compiler.Results.execution RealWorld.Compiler.Results.storage RealWorld.Compiler.Results.code_size

Store the tree in records with three links (left, right, parent), the key and the node's data words. Every move and rotation of the finger is then a fixed program of at most 19 pointer-machine instructions, which keeps the whole representation and allocates nothing. A real-world machine with $l$ instructions compiles to one pointer-machine program of $24l + 4$ instructions. Start the compiled program from a state that stores the source state, a relation that requires a nonempty tree, and let the word width be at least one bit. If the machine serves $m$ requests in $T$ steps in total, the compiled program responds to the same requests in at most $19T + 3m$ instructions, ends in a state that stores the source's final state, and keeps the number of records.

In Lean, the pointer machine is `Cslib.PointerMachine` from CSLib Frontier, the representation is [[RotationBST.RealWorld.Linked.Realizes]], the relation between the two machines is [[RotationBST.RealWorld.Compiler.Image]], and the compiler is [[RotationBST.RealWorld.Compiler.compile]].
```

## The machine

@decl RotationBST.RealWorld.Node RotationBST.RealWorld.Instruction RotationBST.RealWorld.Machine

A node holds an immutable key and `fields` mutable words. Words are `BitVec width`: addition and subtraction wrap around modulo $2^{\mathit{width}}$, and comparisons are unsigned. A machine is a table of `labels` instructions and an entry label. Each instruction names its successor labels, so the control is finite: the numbers of fields, registers and labels are fixed, independently of the tree, the requests and the word width. Constants in instructions are fixed natural numbers. No instruction contains a Lean function, so a machine cannot hide a computation in an instruction.

The instructions are of three kinds.

- **Register instructions:** a constant, a copy, addition, subtraction, a branch on `a < b`, and reading the current request into a register.
- **Instructions at the finger:** read the finger's key, and read or write one of its data words. No instruction reads another node.
- **BST instructions:** one of the six moves and rotations of [[Multifinger.Opcode]] ([Chapter 10](fingers.html#command-streams)), applied at the finger.

Two more instructions close a request. `mark` succeeds only if the finger's key equals the request, and records that the request was visited. `finish` succeeds only after a `mark`, and ends the request.

@decl RotationBST.RealWorld.State RotationBST.RealWorld.eval RotationBST.RealWorld.tick

A state holds the tree with its finger, as a labelled cursor ([[LabelledCursor.Config]], from [Chapter 33](replay.html#labelled-cursors)), the registers, the current request, the visited flag, and the label of the next instruction. When there is no next label, the machine is between two requests, at a *response boundary*. The cursor is a zipper, the path from the finger to the root. This is how the mathematics describes a linked tree with a pointer into it; it is not a stack that the machine stores, and the second half of the chapter stores the tree with parent links instead.

`eval` executes one instruction and returns the new state, together with the BST instruction it performed, if any. It fails on an illegal move or rotation ([[LabelledCursor.perform]]), on an access to an empty finger, on a `mark` at the wrong key, and on a `finish` before a `mark`. A failed step has no successor, so a machine that fails or loops never completes its request. `tick` runs the instruction at the current label.

## Requests and runs

@decl RotationBST.RealWorld.accept RotationBST.RealWorld.Event RotationBST.RealWorld.lts

`accept` gives the machine its next request, and only at a response boundary. It stores the key, clears the visited flag and jumps to the entry label. The state has no field for past requests. A machine that wants to remember something about them must keep it in its registers or in the data words of the nodes. The machine is also a labelled transition system in the sense of CSLib, whose events are inputs and computation steps.

@decl RotationBST.RealWorld.Run RotationBST.RealWorld.Responds RotationBST.RealWorld.Execution

`Run p s t time cost` says that `time` steps lead from `s` to `t`, and that `cost` of them are BST instructions. `Responds` is one request: accept it, run, and stop at a boundary. `Execution` serves a list of requests in order and adds up both costs. The list of requests is part of the statement, not of the state: no instruction can read it.

**Theorem (runs).** The BST instructions of a run form a [[Pointer.Trace]] between the cursors of its two states with the node data forgotten ([[LabelledCursor.Config.erase]]), with exactly `cost` instructions, and `cost ≤ time`. Two executions of the same requests from the same state reach the same state with the same costs, and executions compose.

@decl RotationBST.RealWorld.Results.physical RotationBST.RealWorld.Results.bst_cost RotationBST.RealWorld.Results.causal RotationBST.RealWorld.Results.append

Since a request enters only at a boundary, the machine cannot look ahead, and determinism makes the response to a prefix of the requests independent of what follows. This is the prefix property that [Chapter 37](deamortization.html#physical-programs-and-their-responses) takes as the definition of an online program, here for a machine with bounded state. The trace starts where the previous request left the finger, so it is a trace of one persistent finger, as in [Chapter 10](fingers.html), not a [[Pointer.Execution]], which restarts at the root.

## Real-world implementations

A machine is an implementation of a real-world BST if it works for every tree size $n$, with the same code, and meets the conditions of the papers.

@decl RotationBST.RealWorld.WordSize RotationBST.RealWorld.Initial RotationBST.RealWorld.Total RotationBST.RealWorld.EfficientFrom RotationBST.RealWorld.ProportionalTime

- `WordSize width C` says that words have enough bits to store the keys $0, \dots, n-1$, $n < 2^{\mathit{width}(n)}$, and at most $C(\lfloor\log_2(n+1)\rfloor + 1)$ bits. A word is therefore $O(\log n)$ bits, as in the definition of @demaine2013.
- `Initial s n` says that `s` is at a boundary, with the finger at the root, and that the keys in inorder are $0, \dots, n-1$.
- `Total p s n` says that after every completed execution from `s`, the machine completes a request for every key $x < n$. It is a separate obligation, because a finite program may fail or loop.
- `EfficientFrom p s C` bounds the running time by the BST cost: every request served from a state reachable from `s` takes at most $C(k + 1)$ steps if it performs $k$ BST instructions. The $+1$ pays for a request whose key is already under the finger. `ProportionalTime` is the same bound for every state and every word width, not only the reachable ones.

@decl RotationBST.RealWorld.Implementation RotationBST.RealWorld.storageWords

An `Implementation` packages one machine, a word width for every $n$ with `WordSize`, an initial state for every $n$ with `Initial`, and the certificates `Total` and `EfficientFrom`. Its constants are chosen before $n$. Its numbers of data words per node and of registers are type parameters, also fixed before $n$. `storageWords f r n` records the storage convention: three links, the key and $f$ data words per node, the $r$ registers, and four more words for the root, the finger, the request and the flag. It is a definition only, and no theorem refers to it; the compiled program below uses more registers (seven pointer registers and $r + 4$ data registers), still a constant number. The space of the compiled program is controlled directly: its records are exactly the nodes of the tree, and no instruction changes their number (theorems below).

The initial states are given, not computed. Building the initial tree, and the time this takes, is not part of the definition.

::: todo
- **No algorithm is implemented yet.** No algorithm of the book, not even move-to-root or splaying, is given as an `Implementation`.
- **From machines to algorithms.** An execution of an `Implementation` is not yet turned into an online algorithm of [Chapter 5](online.html) or a one-finger execution of [Chapter 10](fingers.html), so the bounds proved for those do not yet apply to it.
- **Compiled implementations.** The compiler of the next sections moves single runs; it does not yet turn an `Implementation`, with `Total` and `EfficientFrom`, into a pointer-machine program that serves every request in proportional time.
- **Initialization.** Building the initial tree on the pointer machine, and charging its time, and the empty tree.
- **The real-world clauses of the papers.** That the deamortization preserves real-world implementations (Theorem 7 of @bose2012), and that ComboBST and the one-finger simulation do (Theorems 3 and 5 of @demaine2013).

Roadmap [entry 10](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#10-real-world-implementations).
:::

## Tarjan's pointer machine

The machine above reads and writes the tree through its finger, but it treats the tree as a mathematical object. The papers count time on a *pointer machine* [@tarjan1979]: a fixed number of registers and a growing pool of records, all with the same fields. Registers and fields hold either pointers or data. Memory is reached only by following a pointer held in a register, and no instruction computes on pointers, so there is no address arithmetic. Every instruction costs one unit. The library uses the formalization of this machine in [CSLib Frontier](https://github.com/cslib-community/cslib-frontier), `Cslib.PointerMachine`, which also allocates records; the programs of this chapter never do. Where Tarjan's machine stops on an undefined value, this formalization reads a default value instead.

@decl RotationBST.RealWorld.PointerMachine.WordOp RotationBST.RealWorld.PointerMachine.WordTest RotationBST.RealWorld.PointerMachine.words

The data are the words of the first half, with constants, addition and subtraction, and the tests $=$ and $<$. There is no conversion from a word to a pointer.

### A first example: rotation at the root

The simplest representation of a tree has two links per record and no parent links. It is enough to move down and to rotate at the root, and it shows what the general representation must check.

@decl RotationBST.RealWorld.PointerMachine.layout RotationBST.RealWorld.PointerMachine.State RotationBST.RealWorld.PointerMachine.Record RotationBST.RealWorld.PointerMachine.Instruction RotationBST.RealWorld.PointerMachine.Tree

The layout has three pointer registers (the cursor and two temporaries), two data registers, two links per record, the key and `extra` data words. A tree is labelled with pairs (address, key). The addresses are *ghost* labels: they relate the mathematical tree to the heap, and no program can read them.

@decl RotationBST.RealWorld.PointerMachine.root RotationBST.RealWorld.PointerMachine.addresses RotationBST.RealWorld.PointerMachine.keys RotationBST.RealWorld.PointerMachine.Represents RotationBST.RealWorld.PointerMachine.Boundary

`Represents heap t` says that every node of `t` is a record at its address, with the links to its children and its key. `Boundary s t` asks more: valid pointers, distinct addresses, keys in order, the cursor on the root, and a heap that consists of the tree's records and nothing else. So no extra memory hides next to the tree.

@decl RotationBST.RealWorld.PointerMachine.accept RotationBST.RealWorld.PointerMachine.Protocol RotationBST.RealWorld.PointerMachine.Responds RotationBST.RealWorld.PointerMachine.Execution

A protocol is a program with an entry label. `Responds` starts from a state stopped at a `halt` instruction. `accept` puts the key into data register $0$ and restarts at the entry, and the program runs to the next halt, which is counted. Somewhere along the way the cursor must visit a record holding the key. Executions chain responses.

@decl RotationBST.RealWorld.PointerMachine.down RotationBST.RealWorld.PointerMachine.rotateRight RotationBST.RealWorld.PointerMachine.effects

A move down is one load. A right rotation at the root is five instructions: load the left child, load its right subtree, relink the old root's left child, relink the child's right child, and move the cursor to the new root. `effects` evaluates a straight-line program; it only names the final state, and the theorems below prove that the machine reaches it.

**Theorem (two-link representation).** Executions of a protocol are deterministic. A move down is one instruction, and a move to the left child reaches the represented left subtree. A root rotation is five instructions, keeps the boundary invariant and the number of records, and makes the same change as a move down-left followed by a rotation of the finger over its parent in [[LabelledCursor.perform]].

@decl RotationBST.RealWorld.PointerMachine.Results.causal RotationBST.RealWorld.PointerMachine.Results.navigation_time RotationBST.RealWorld.PointerMachine.Results.navigation RotationBST.RealWorld.PointerMachine.Results.rotation_time RotationBST.RealWorld.PointerMachine.Results.rotation RotationBST.RealWorld.PointerMachine.Results.rotation_bst

### Parent links and all six instructions

Moving up and rotating below the root need parent links.

@decl RotationBST.RealWorld.Linked.layout RotationBST.RealWorld.Linked.State RotationBST.RealWorld.Linked.Record RotationBST.RealWorld.Linked.Instruction RotationBST.RealWorld.Linked.Label RotationBST.RealWorld.Linked.Tree RotationBST.RealWorld.Linked.Cursor

The layout has seven pointer registers (the cursor, the root, the parent, the grandparent, the middle subtree, a null pointer and a temporary), `regs` data registers, and three links per record: left, right and parent. A label is an address together with all the data fields of the node, its key first. So a theorem that keeps the labels keeps the data too.

@decl RotationBST.RealWorld.Linked.root RotationBST.RealWorld.Linked.parent RotationBST.RealWorld.Linked.node RotationBST.RealWorld.Linked.Represents RotationBST.RealWorld.Linked.Context RotationBST.RealWorld.Linked.keys RotationBST.RealWorld.Linked.addresses RotationBST.RealWorld.Linked.Realizes

`Represents heap p t` says that `t` is stored below the parent pointer `p`, with both directions of every edge. `Context` does the same for the path from the finger to the root: each ancestor, its other subtree, and its own parent. `Realizes s c` says that the machine state stores the cursor `c`, at any depth: valid pointers, the focus and the context represented, distinct addresses, ordered keys, a heap with exactly the tree's records, the cursor register on the finger, the root register on the root, and a nonempty focus.

@decl RotationBST.RealWorld.Linked.move RotationBST.RealWorld.Linked.rotate RotationBST.RealWorld.Linked.program RotationBST.RealWorld.Linked.start RotationBST.RealWorld.Linked.run

A move is one load and a halt; both moves up follow the parent link. A rotation promotes the finger over its parent and leaves the finger on it. It relinks the middle subtree, the two nodes and the grandparent's child on the correct side, or the root register if there is no grandparent. A store through the null pointer does nothing, so an empty middle subtree needs no special case. `program` gives the code of each of the six instructions, `start` sets the program counter to $0$, and `run` evaluates a program for a given number of steps.

**Theorem (the six instructions).** If a state realizes a cursor $c$ and an instruction is legal at $c$, its program runs in at most $19$ instructions, halt included, to a state that realizes the cursor after the instruction, with the same number of records.

@decl RotationBST.RealWorld.Linked.Results.primitive

The bound $19$ is a uniform bound for all six programs; the moves take two instructions.

## Compiling a machine

The last step translates a whole real-world machine into one pointer-machine program. There is no outside dispatcher: the compiled program chooses its next block of code itself, and every jump is an instruction that costs one unit.

@decl RotationBST.RealWorld.Compiler.Target RotationBST.RealWorld.Compiler.Opcode RotationBST.RealWorld.Compiler.userReg RotationBST.RealWorld.Compiler.queryReg RotationBST.RealWorld.Compiler.seenReg RotationBST.RealWorld.Compiler.tempReg RotationBST.RealWorld.Compiler.zeroReg RotationBST.RealWorld.Compiler.field

The target is the parent-linked machine with $r + 4$ data registers: the $r$ registers of the source machine, then the request, the visited flag, a temporary for keys and a temporary for zero. The data field $i$ of a node is field $i + 1$ of its record, after the key.

@decl RotationBST.RealWorld.Compiler.stride RotationBST.RealWorld.Compiler.address RotationBST.RealWorld.Compiler.boundary RotationBST.RealWorld.Compiler.trap RotationBST.RealWorld.Compiler.entry RotationBST.RealWorld.Compiler.relocate RotationBST.RealWorld.Compiler.block RotationBST.RealWorld.Compiler.compile

Each source instruction gets a block of $24$ slots. Register and finger instructions become a few pointer-machine instructions and a jump. A BST instruction becomes its program from the previous section, relocated into the block, with its halt replaced by a jump to the block of the next label. After the blocks come four slots: the only `halt`, which is the response boundary, a trap that loops forever, and the two instructions that start a request. Unused slots, a failed `mark` and an early `finish` jump to the trap. The theorems below are about successful source runs only; they say nothing about the compiled program after an illegal move.

@decl RotationBST.RealWorld.Compiler.accept RotationBST.RealWorld.Compiler.Responds RotationBST.RealWorld.Compiler.Execution

A request is accepted only at the halt. It writes the key into the request register and enters the start code, which clears the visited flag and jumps to the source entry; both instructions are charged. Registers and records persist from one request to the next.

@decl RotationBST.RealWorld.Compiler.decode RotationBST.RealWorld.Compiler.flag RotationBST.RealWorld.Compiler.location RotationBST.RealWorld.Compiler.Image

`Image s t` relates a source state `s` to a target state `t`: some cursor with addresses is realized by `t` and decodes to the cursor of `s`, the registers and the request agree, the flag is stored as $0$ or $1$, and the program counter of `t` is the start of the block of the next source instruction, or the halt at a boundary.

**Theorem (compilation).** Assume a word width of at least one bit, and a source state and a target state related by `Image`.

1. If the source machine serves a request in $T$ steps, the compiled program responds to it in at most $19T + 3$ instructions, in a state related to the source's final state. The compiled response is only accept and run to the halt; that it visits the key follows from the source run, through the relation. For $m$ requests in $T$ steps in total, the bound is $19T + 3m$.
2. If the source serves the request in at most $C(k + 1)$ steps, where $k$ is its BST cost, the compiled program takes at most $(19C + 3)(k + 1)$ instructions.
3. No run of the compiled program changes the number of records.
4. The program has exactly $24l + 4$ instructions for a source machine with $l$ labels.
5. A request served by the compiled program ends in a unique state, with a unique instruction count.

@decl RotationBST.RealWorld.Compiler.Results.response RotationBST.RealWorld.Compiler.Results.execution RotationBST.RealWorld.Compiler.Results.proportional_time RotationBST.RealWorld.Compiler.Results.storage RotationBST.RealWorld.Compiler.Results.code_size RotationBST.RealWorld.Compiler.Results.deterministic

The $3$ per request pays for the two start instructions and the halt. The width must be positive so that the flag values $0$ and $1$ differ. The compiler moves a running time certificate from the source to the target; it does not produce one. During a rotation, the records may not represent a tree for a few instructions; the invariant holds again at the end of each source instruction.

::: caveat Scope of the compiler
The compiler simulates successful requests forward, from a given related pair of states with a nonempty tree. It does not build the initial records, handle the empty tree, or prove that a source machine terminates. Termination is the certificate `Total` of each implementation; the rest is listed in the box above.
:::
