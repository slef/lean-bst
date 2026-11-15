# Real-world BST implementations

An online BST algorithm may use the entire request prefix when selecting its next operations. The interface in [Online algorithms](online.html) permits this explicitly: `Algorithm.step` receives the history. Only BST operations are charged. That mathematical model is useful for competitive analysis, but it does not bound the memory or computation used to select those operations.

Bose, Collette, Fagerberg and Langerman distinguish this from a real-world implementation in the opening model discussion of *De-amortizing Binary Search Trees* [-@bose2012]. Such an implementation uses a pointer machine, a constant number of words per node, constant global workspace, and time proportional to its BST operations. Theorem 7 asks that the transformation preserve these additional properties.

## A finite-control word machine

`RealWorld.Machine` specifies a fixed finite instruction table. Its parameters are the number of metadata words per node, scalar registers, and code locations. These are fixed independently of the tree size, input sequence, and word width. Constants in instructions are fixed natural literals interpreted modulo the word size. Instructions contain no arbitrary Lean callbacks.

`RealWorld.State` contains the labelled tree with its persistent finger, the scalar registers, the current request, a visited flag, and the program counter. Each node has an immutable key and a fixed vector of mutable words. Words are `BitVec width`; addition and subtraction wrap modulo $2^{\mathit{width}}$. A comparison is unsigned. `WordSize` requires enough bits to represent keys and addresses and an $O(\log(n+1))$ upper bound, uniformly in $n$.

The instruction set includes register constants, copies, arithmetic, conditional branches, reading the current request and current node's key, loading and storing metadata at the finger, and the six existing pointer moves and rotations. An explicit `mark` instruction succeeds only when the finger's stored key equals the current request. A response can finish only after that mark. There is no direct access to another node's metadata by an arbitrary integer address. The RAM-like arithmetic is on the fixed register file; tree access remains local to the finger.

Every instruction costs one machine step. Only a pointer move or rotation also costs one BST operation. Invalid moves and failed checks have no successful successor; termination and successful service must be proved for an algorithm.

The semantic cursor uses a zipper to describe a linked tree and its finger. This is a mathematical representation, not a charged runtime stack. The storage convention is three links, a key and the metadata words per node, plus the fixed registers, root/finger/query words and a flag. Finite control is separate. The concrete representation and compiler below implement this semantic machine on a pointer machine. This does not assert that arbitrary Lean evaluation has the same runtime.

@decl RealWorld.Node RealWorld.Instruction RealWorld.Machine RealWorld.State RealWorld.eval RealWorld.tick

## Online input and resumable state

`accept` supplies one new key only when the machine is at a response boundary. It resets the visited flag and starts at the fixed entry location. The machine has no input-history field and cannot read future requests. It may retain information about earlier requests only in the bounded registers and node metadata. Its complete state also describes everything needed to resume an interrupted computation.

`Responds` describes one completed access. `Execution` chains completed accesses; its request list and execution witnesses are specification data, inaccessible to instructions. The uniqueness theorem says that a completed prefix determines a unique state and both costs. The append theorem composes prefixes with continuations. Together these give the retained-state formulation of online causality.

@decl RealWorld.accept RealWorld.lts RealWorld.Run RealWorld.Responds RealWorld.Execution

## What must an implementation prove?

`RealWorld.Implementation` packages a uniform program, a logarithmic word-width family, initial states satisfying `Initial`, and the total-service and runtime certificates. Its constants are outside the quantification over tree sizes. Initialization runtime remains a separate obligation.

There are separate obligations:

- Initialize a correctly ordered tree with the intended keys, charging setup separately.
- Prove `Total`: every existing key can be served after every completed valid history.
- Prove `EfficientFrom`: on states reachable from initialization, machine time per completed request is at most a fixed constant times its BST operations plus one. The request unit handles a key already under the finger.
- Use fixed code, field and register counts, and a word-width family satisfying `WordSize`.
- For a pointer-machine implementation, prove that the stored representation realizes these machine instructions and respects the same local-access discipline.

The physical-trace theorem removes scalar and metadata instructions and yields a legal trace in the existing pointer model, with exactly the recorded BST cost. It does not identify stored keys with inorder ranks for an arbitrary malformed input: that requires the ordered-key initialization invariant.

This is a model and a set of proof obligations, not a proof of Theorem 7. Applying this model to the pop-tart construction still requires a controller implementing this interface and a proof of proportional machine time.

@decl RealWorld.Initial RealWorld.Total RealWorld.EfficientFrom RealWorld.WordSize RealWorld.Implementation RealWorld.storageWords

## CSLib

The semantic model above uses CSLib's `Cslib.LTS`. A second layer now connects
BST representations to the general Tarjan-style pointer machine from
[CSLib Frontier PR #5420](https://github.com/cslib-community/cslib-frontier/pull/5420),
pinned at commit `86efa56d47a44812fab049080fba87d7635db63b`. It uses that
library's instructions, heaps and charged execution directly. The existing
CSLib pin is retained; this adds a pinned Frontier dependency.

## Concrete pointer-machine representation

`RealWorld.PointerMachine.words` supplies modular words, literal/add/subtract
operations, and equality/order tests. Pointers occupy separate fields and
registers and cannot be obtained by arithmetic. The current layout has three
pointer registers, two scalar registers, two child links per record, one key,
and a fixed number of metadata words. Addresses in the labelled specification
tree are ghost labels, not scalar values exposed to the program.

`Represents` relates an actual heap to a labelled tree. `Boundary` additionally
requires distinct node addresses, an ordered key tree, valid pointers, the
root under the cursor, and exact coverage of the allocated heap by the tree.
Consequently, no separate work heap is hidden in this boundary invariant.

@decl RealWorld.PointerMachine.words RealWorld.PointerMachine.layout RealWorld.PointerMachine.Represents RealWorld.PointerMachine.Boundary

The concrete online protocol accepts one key in a designated register and
restarts at a fixed entry label, preserving all other state. `Responds`
requires a halted starting state, a charged execution to halt, and a witnessed
visit to a record holding the requested key during that execution. `Execution`
chains responses. The history and visit witnesses are specification objects,
not extra runtime storage. Prefix determinism follows from the upstream
machine's deterministic execution.

@decl RealWorld.PointerMachine.Protocol RealWorld.PointerMachine.accept RealWorld.PointerMachine.Responds RealWorld.PointerMachine.Execution RealWorld.PointerMachine.Results.causal

A child navigation is one pointer-load instruction. A root right rotation is
five instructions: load the left child, load its right subtree, replace the
old root's left link, replace the child's right link, and move the cursor to
the new root. A standalone program additionally charges one instruction for
halt. The rotation theorem preserves the complete boundary invariant and
exact heap length, for arbitrary subtrees and metadata. Its structural change
is exactly the existing down-left followed by rotate-left-child operations.

@decl RealWorld.PointerMachine.down RealWorld.PointerMachine.rotateRight RealWorld.PointerMachine.Results.navigation_time RealWorld.PointerMachine.Results.navigation RealWorld.PointerMachine.Results.rotation_time RealWorld.PointerMachine.Results.rotation RealWorld.PointerMachine.Results.rotation_bst

The two-child representation above remains a small introductory example.
The following representation adds the parent links needed for all six
primitives.

## Parent-linked trees and all six primitives

`RealWorld.Linked.layout` has seven pointer registers: cursor, root, parent,
grandparent, middle subtree, null, and a comparison temporary. It has a fixed scalar register file and three pointer fields per record (left, right, parent),
plus the key and a fixed number of metadata words. These counts are independent
of tree size and access history. The programs use only pointer instructions;
they do not compute numeric addresses.

`Realizes` relates an actual machine state to a labelled cursor anywhere in
the BST. Its recursive focus and context predicates check both directions of
every tree edge, including the null parent of the root. It also checks pointer
validity, the root register, distinct addresses, ordered keys, and exact
coverage of the heap by the tree. Labels retain every data field, so preserving
the represented labels preserves metadata as well as keys. The context is a
proof-only zipper; it is not a runtime stack.

@decl RealWorld.Linked.layout RealWorld.Linked.node RealWorld.Linked.Represents RealWorld.Linked.Context RealWorld.Linked.Realizes

The two downward moves load the corresponding child field. Both upward moves
load the parent field; their abstract legality distinguishes the left and right
cases. Each navigation executes one load followed by halt, for two charged
instructions.

Each rotation promotes the cursor above its parent while leaving the cursor
on the promoted node. The program repairs the transferred middle subtree's
parent link, both pivot nodes, and the grandparent's appropriate child link.
When there is no grandparent it updates the root register instead. Stores
through a null middle-subtree pointer have no effect, as specified by the
upstream machine. Both directions use fixed code and terminate within nineteen
charged instructions, including halt; this is a conservative uniform bound.

@decl RealWorld.Linked.move RealWorld.Linked.rotate RealWorld.Linked.program RealWorld.Linked.start

The primitive simulation theorem states that **every legal one-step operation
of the existing labelled-cursor model has a concrete pointer-machine execution**
within that bound. The resulting state realizes exactly the resulting cursor,
and the heap has exactly the same number of records. The theorem covers every
cursor depth, both grandparent child positions, root rotations, empty and
nonempty middle subtrees, and arbitrary metadata.

@decl RealWorld.Linked.Results.primitive

Regressions include a fully verified seven-node starting representation,
non-root rotations in both directions with nonempty middle subtrees, root
register repair, parent links, and metadata preservation.

## Compiling the complete controller

`RealWorld.Compiler.compile` translates the entire finite `RealWorld.Machine`
into **one pointer-machine program**. It supports every source instruction:
constants, copies, addition and subtraction, comparisons, key and query reads,
metadata loads and stores, all six BST primitives, visit marking and finish.
Each source instruction occupies a block of twenty-four code slots. Internal
branches in a BST primitive are relocated; its final halt becomes a charged
jump to the next source instruction. There is no free per-operation restart
or external instruction-selection oracle.

The target has seven pointer registers and $r+4$ scalar registers: the source
registers plus current request, visited flag, key temporary and zero temporary.
It retains the same tree records, with three links, the key and $f$ metadata
words each. The program has exactly $24l+4$ slots for a source with $l$ labels,
independently of the number of nodes and requests. Padding and failed checks
lead to a nonhalting trap; the program has one successful halt.

@decl RealWorld.Compiler.Target RealWorld.Compiler.block RealWorld.Compiler.relocate RealWorld.Compiler.compile RealWorld.Compiler.Results.code_size

Input is accepted only at that successful halt. The external input operation
replaces the designated request register and enters the request-entry routine.
Resetting the visited flag and jumping to the source entry are two charged
instructions. Marking a visit reads the current node's key and compares it
with the request. Finish checks the stored visited flag before reaching halt.
Registers and tree storage persist between requests.

@decl RealWorld.Compiler.accept RealWorld.Compiler.Responds RealWorld.Compiler.Execution

`Image` is the full source/target invariant. It combines the parent-linked
representation with equality of user registers and request, encoding of the
visited flag, and translation of the program counter. Addresses and execution
histories occur only in the specification. The theorem assumes a represented
nonempty tree and a positive word width; the latter distinguishes the stored
zero and one used for the visited flag.

@decl RealWorld.Compiler.decode RealWorld.Compiler.Image

For a successful source request taking $T$ semantic machine steps, the same
compiled program completes the request in at most $19T+3$ pointer-machine
instructions. The three extra instructions account for request entry and
final halt. For a sequence of $m$ requests with total source time $T$, the
bound is $19T+3m$. The target endpoint represents the exact source endpoint,
including its cursor and metadata. Concrete successful responses have unique
endpoints and exact instruction counts.

@decl RealWorld.Compiler.Results.response RealWorld.Compiler.Results.execution RealWorld.Compiler.Results.deterministic

Consequently, a source certificate $T\le C(k+1)$, where $k$ is its BST work,
transfers to target time at most $(19C+3)(k+1)$. The compiler does not establish
that source certificate by itself. Separately, every compiled execution,
including prefixes and trap loops, preserves the exact record count: compiled
code contains no allocation instruction.

@decl RealWorld.Compiler.Results.proportional_time RealWorld.Compiler.Results.storage

The regression controller serves two different keys using the same compiled
program, exercises scalar arithmetic and metadata access, and returns to the
root between requests. Additional cases check both relocated rotation
directions and confirm that an unmarked finish or a mismatched mark cannot
reach the successful halt in those examples. Its initial source/target image
is proved explicitly; the examples are evaluated by Lean's kernel.

## Remaining implementation obligations

The compiler gives a forward simulation of successful source executions from
a supplied source/target image. It does not construct or charge an initial
heap, handle an empty-tree image, or prove termination for arbitrary source
controllers. Initialization, the source word-size discipline, total service,
and source proportional-time certificates remain obligations of each
algorithm. Intermediate field writes during a rotation need not represent a
complete tree; the simulation invariant holds at source-instruction boundaries.

Theorem 7 and the ComboBST implementation-preservation clauses still require
concrete finite controllers for their constructions and the corresponding
algorithm-specific storage and runtime proofs. The compiler now supplies the
machine-level connection for those controllers.
