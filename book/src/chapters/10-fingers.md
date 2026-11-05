# Many fingers

The pointer machine of [Chapter 6](pointer.html) has a single cursor, and every request starts it again at the root. A *multi-finger* BST keeps several cursors, called **fingers**, inside one tree. Each finger stays where the previous instruction left it, also from one request to the next, and any finger may run the ordinary pointer instructions: move to a child, move to the parent, or rotate its node over its parent. A request is served as soon as some finger stands on the requested key. The cost is one unit per request plus one unit per instruction, for any finger.

This chapter defines that model. It has no theorem of its own; it is a common language for two results of later chapters.

- **Lazy finger is a one-finger execution.** A static tree searched with a lazy finger, where each search starts at the node where the previous search ended ([Chapter 14](lazy-finger.html)), is a multi-finger execution with one finger and no rotations. Its cost is exactly the lazy-finger cost [[LazyFinger.costFrom]]. This is [[LazyFinger.Dynamic.Results.persistent]] in [Chapter 15](lazy-finger-hierarchy.html).
- **Fingers can be simulated from the root.** The *finger hand* of [Chapter 35](finger-hands.html), built from the BST deques and tendons of [Chapter 34](bst-deques.html), turns a multi-finger execution into an execution of the conventional pointer machine, with an overhead that is constant for a fixed number of fingers. With one finger this gives [[LazyFinger.Dynamic.Results.same_tree]]: for every tree and every sequence of valid requests, some pointer-machine execution from that same tree costs at most $464$ times the lazy-finger cost. Like every [[Pointer.Execution]], it is an offline object, an existence statement, not an online algorithm. This is the step behind the comparison of dynamic BSTs with lazy finger in Theorem 6 of Bose, Douïeb, Iacono and Langerman (2013), stated in Lean as [[LazyFinger.Dynamic.Results.optimal]].

A reader who only wants to check those statements needs the first three sections: the state, one instruction, and executions. The last section, on command streams, describes the same model as an explicit input format; nothing in the later headline statements uses it. The definitions are in `Models/Multifinger/Definitions/Abstract.lean` and `Models/Multifinger/Program/Definitions/Abstract.lean`.

## The state

@decl RotationBST.Multifinger.State RotationBST.Multifinger.State.Valid

A state with `fingers` fingers is a tree together with one inorder rank per finger. Ranks are the library's keys ([Section 1.3](shapes.html#implicit-keys)), and a rotation never changes the inorder order. So a rank names one physical node for as long as the tree is only rotated, and a finger that does not move stays on its node while the tree changes around it. Several fingers may share a node. The number of fingers is a parameter of the type; it is fixed for a whole execution.

The state does not store the zipper of [Chapter 6](pointer.html#configurations) for each finger, only its rank. Nothing is lost: a tree and a rank determine the whole cursor, focused subtree and path to the root included ([[Pointer.Results.cursor_unique]]). `Valid` says that every finger is on an actual node, that is, every rank is less than the tree size.

@decl RotationBST.Multifinger.initial

Initially, every finger is on the root, whose rank is the size of the left subtree. For the empty tree, `initial` puts every finger at rank $0$. That value only totalizes the definition: the state is then not valid, and no instruction applies to it.

## One instruction

@decl RotationBST.Multifinger.Step

`Step s i t` says that finger `i` performs one pointer instruction and turns the state `s` into `t`. The constructor reads as follows.

1. `a` is a pointer configuration ([[Pointer.Config]]) of the current tree (`a.tree = s.tree`) whose cursor is on finger `i`'s rank (`a.key? = some (s.position i)`). By [[Pointer.Results.cursor_unique]], there is only one such configuration.
2. `b` is the result of one instruction of the single-cursor machine, [[Pointer.Step]]: one of the four moves or the two rotations. Their patterns are those of [Chapter 6](pointer.html#instructions), so the cursor never moves onto an empty subtree.
3. `x` is the rank under the cursor afterwards. After a move it is the neighbouring node. After a rotation it is the same node, which is now one level higher.
4. The new state has the tree of `b`, finger `i` moves to `x`, and every other finger keeps its rank (`Function.update`).

As the docstring says, there is no teleportation: a finger can reach a node only by walking there along edges. There is no free reset to the root either. Rotations are performed only at a finger, on the node it stands on. The active finger must be on an actual node, but the other fingers are not checked. The library proves that instructions preserve `Valid`, so in executions from a valid state all fingers stay on actual nodes.

## Traces, requests and executions

@decl RotationBST.Multifinger.Trace

A trace is a sequence of steps, each at any finger. It records, after each instruction, the rank that the active finger stands on: the *touched* key. The list therefore has exactly one entry per instruction, and its length is the instruction count. The keys record where the work happened; the cost statements of the library use only the length of the list.

@decl RotationBST.Multifinger.Serves

`Serves s t x cost` mirrors [[Pointer.Serves]]. A trace `before` leads from `s` to a state `visited` in which some finger `i` stands on `x`. A further trace `after` leads to the final state `t`. The cost is $1 + |\mathit{before}| + |\mathit{after}|$: the request unit plus every instruction. Like the pointer machine, the search may keep working after the visit, and the visiting finger is arbitrary. If a finger already stands on `x`, the request costs $1$.

The difference from [[Pointer.Serves]] is in where the request starts and ends. A pointer search starts at the root configuration of its tree, and the next request starts at the root again, for free. A multi-finger request starts from the full state `s`, with every finger wherever the previous request left it, and its final state `t` is where the next request starts. Getting back to the root, if wanted, costs instructions like any other walk.

@decl RotationBST.Multifinger.Execution

An execution serves the requests in order, each request starting from the previous final state, and adds up the costs. It has the same shape as [[Execution]] and [[Pointer.Execution]]. As there, `Execution s xs t cost` says that this way of serving `xs` exists at this cost; it is not a minimum.

::: check
- **What the cost counts.** One unit per request and one per instruction, whatever the finger. A move and a rotation cost the same, as on the pointer machine. Choosing which finger acts, and which instruction, is free; this is the usual convention for BST models.
- **Persistent fingers.** Fingers are never reset. With one finger, a multi-finger execution is therefore *not* a [[Pointer.Execution]]: the latter restarts at the root for each request.
- **Requests.** A request can only be served by a finger on that very rank, so a request outside the tree has no `Serves` at all. With zero fingers (`Fin 0` is empty) no request can be served, and only the empty sequence has an execution.
:::

## How the model relates to the others

The multi-finger model sits above the pointer machine, which in turn agrees with the rotation model of [Chapter 3](accesses.html) up to constant factors ([Chapter 6](pointer.html#the-two-models-agree)).

**One finger contains the pointer machine's traces.** Any [[Pointer.Trace]] between two configurations on actual nodes is a one-finger trace with the same number of instructions and the same endpoint ranks. The library proves this as `Multifinger.pointer_trace`. Only the *requests* differ, as explained above: a multi-finger request does not get the free return to the root.

**One finger and no rotations is lazy finger.** If the single finger only moves, the tree never changes, and the cheapest way from rank $p$ to rank $x$ is the path between them in the tree. Its length is the lazy-finger distance [[LazyFinger.distance]] of [Chapter 14](lazy-finger.html). [[LazyFinger.Dynamic.Results.persistent]] states the resulting execution: from one finger at a valid rank `p` of a tree `t`, there is a one-finger execution of any valid sequence that ends with the same tree, and its cost is exactly [[LazyFinger.costFrom]]` t p xs`, that is, one unit plus the distance for each request. The navigation-only walks [[Pointer.Walk]] behind this are in [Chapter 6](pointer.html).

**Several fingers can be simulated by one.** The finger hand of [Chapter 35](finger-hands.html) represents a multi-finger state inside an ordinary BST, keeping the paths between the fingers compressed in BST deques and tendons ([Chapter 34](bst-deques.html)). Every instruction of every finger is simulated by the single root-restarting cursor of [Chapter 6](pointer.html), at an amortized cost that is constant for a fixed number of fingers. In the library's proof (`FingerHand.Hand.one_finger_execution`, not part of the reading interface), a multi-finger execution with $k$ fingers from the initial state on a nonempty tree becomes a [[Pointer.Execution]] from the same tree, serving the same requests, with cost at most $(344 + 60(k+1))$ times the multi-finger cost. The reading interface states only the case of one finger, through lazy finger. With $k = 1$ the factor is $464$, which is the constant of [[LazyFinger.Dynamic.Results.same_tree]].

## Command streams

The relation `Step` lets the finger and the instruction be anything that is legal. An algorithm in this model must name them explicitly. The library gives that input format, and an executable reading of each instruction.

@decl RotationBST.Multifinger.Opcode RotationBST.Multifinger.Command

An opcode names one of the six instructions of [[Pointer.Step]]. A command names a finger and an opcode, and nothing else: no target key, no address, no hidden data.

@decl RotationBST.Multifinger.perform

`perform op c` is the configuration after the instruction `op` at configuration `c`, or `none` if the instruction is illegal there, for instance moving to an empty child or rotating the root. Its six patterns are those of the constructors of [[Pointer.Step]], one for one, and the library proves both directions: `perform op a = some b` implies `Pointer.Step a b`, and every pointer step is `perform` of some opcode. The same decoder appears in the counting argument behind [[Pointer.Results.reachable_keys]], where a trace of $r$ instructions is written as a word of length $r$ over seven symbols.

@decl RotationBST.Multifinger.Command.Step

`Command.Step s cmd t` executes the command at its finger. It finds the configuration of the finger's rank, runs `perform`, and updates that finger's rank, exactly as in `Step`. Since the configuration is unique and `perform` is a function, the outcome is determined by `s` and `cmd`; the library proves this as `Command.Step.deterministic`.

@decl RotationBST.Multifinger.Program

A program is a legal command stream from one state to another, together with the touched keys, as in a trace. The library proves that programs and traces describe the same runs: every program is a trace with the same touched keys (`Program.trace`), every trace is the trace of some program (`trace_program`), and the number of commands is the number of touched keys. An online multi-finger algorithm is thus a rule that emits commands one at a time, and its cost is the length of its stream plus one per request.
