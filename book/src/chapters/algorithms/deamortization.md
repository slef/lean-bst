# Deamortization

Most of the good BST bounds are amortized. Splaying costs $O(\log n)$ per access on average over a sequence, but a single access can cost $\Theta(n)$. Balanced trees guarantee $O(\log n)$ per access, but none of the adaptive bounds. Bose, Collette, Fagerberg and Langerman [-@bose2012] showed that this trade-off is not necessary. Any BST algorithm can be transformed into one that has the same total cost on every sequence, up to a constant factor, and in addition serves every single access with $O(\log n)$ operations. Applied to splay trees, this gives one BST with all of splaying's amortized bounds and logarithmic worst-case accesses.

The library formalizes the abstract BST-operation part of the paper: the counterpart of its Theorem 6 for every online rotation-model algorithm, and its application to splaying. Like the paper's Theorem 6, it counts BST operations only; the private computation and storage that choose them are not bounded ([Section 37.9](#what-is-not-formalized)).

```headline deamortization
title: Every online BST algorithm can be deamortized
source: @bose2012
key: yes
theorems: Deamortization.Algorithm.Results.implementation_exists Deamortization.Algorithm.Results.total_bound Deamortization.Algorithm.Results.transfer

This is the abstract BST-operation counterpart of Theorem 6 of the paper. Let $A$ be any online BST algorithm in the rotation model, and $T$ any nonempty initial tree on $n$ keys. Then there is a single deamortized program, fixed from $A$ and $T$ before any request is known, made of two parts.

1. **Setup.** A pointer-machine trace of at most $16n$ instructions turns $T$, cursor at the root, into a tree $T''$, cursor at the root.
2. **Responses.** For every sequence $X = x_1, \dots, x_m$ of keys in $\{0, \dots, n-1\}$, the program emits one stream of pointer instructions for a single persistent finger, starting at the root of $T''$. The stream is cut into $m$ consecutive segments, one per request. During segment $j$ the finger stands on $x_j$ at least once, and response $j$ costs $c_j = 1 + (\text{length of segment } j)$. Every response is cheap, and the total is within a constant factor of $A$:

$$c_j \;<\; 251 + 195\log_2 n \quad\text{for every } j, \qquad \sum_{j=1}^m c_j \;\le\; 79360\,\bigl(m + R_A(X)\bigr),$$

where $R_A(X)$ is the number of rotations $A$ performs on $X$ from $T$. With the setup included, the total is at most $16n + 79360\,(m + R_A(X))$, and any upper bound $B$ on $m + R_A(X)$ gives the total bound $16n + 79360\,B$.

The program is **online**: if $X$ is a prefix of $X'$, then the instruction stream and the list of response costs for $X$ are prefixes of those for $X'$.

In Lean, $A$ is an [[RotationBST.Algorithm]] with cost [[RotationBST.Algorithm.totalCost]], and the program is a [[Deamortization.Algorithm.Implementation]]. `implementation_exists` constructs one; its fields carry the setup, the correctness and cost guarantees, and causality. `total_bound` adds the setup, and `transfer` replaces $m + R_A(X)$ by any real upper bound.
```

```headline splay-deamortized
title: A deamortized splay tree keeps splaying's bounds
source: @bose2012
key: yes
theorems: Splay.Deamortization.Results.implementation_exists Splay.Deamortization.Results.scanning Splay.Deamortization.Results.balance Splay.Deamortization.Results.working_set Splay.Deamortization.Results.static_optimality Splay.Deamortization.Results.static_finger Splay.Deamortization.Results.static_optimality_general Splay.Deamortization.Results.static_finger_general

For every nonempty initial tree on $n$ keys there is a deamortized splay program as in the box above, with splaying as the source algorithm $A$. Every response costs less than $251 + 195\log_2 n$. For **every** such program and every sequence $X$ of $m$ keys in $\{0, \dots, n-1\}$, let $T(X)$ be the setup cost plus the sum of the response costs. Then all of the following hold, for the same program and the same run:

- **Scanning.** For $X = 0, 1, \dots, n-1$: $T(X) \le 1111056\,n$.
- **Balance.** $T(X) \le 16n + 79360\,\bigl(m(2 + 3\log_2 n) + n\log_2 n\bigr)$.
- **Working set.** $T(X) \le 16n + 79360\,\bigl(11\sum_j (1 + \lfloor\log_2 w_j\rfloor) + 6n(1 + \lfloor\log_2 n\rfloor)\bigr)$, where $w_j$ is the working-set number of request $j$.
- **Static optimality**, if $X$ requests every key: $T(X) \le 16n + 952320\sum_j \bigl(1 + \mathrm{depth}_u(x_j)\bigr)$ for every BST $u$ on the $n$ keys.
- **Static finger**, if $X$ requests every key: $T(X) \le 16n + 952320\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$ for every natural number $f$.
- **Without the coverage hypothesis**, there are constants $C$ and $D$, the same for all $n$, all programs and all sequences, such that $T(X) \le 16n + C\bigl(m + \sum_i q_i\log_2(m/q_i)\bigr) + D\,n(1 + \lfloor\log_2 n\rfloor)$, where key $i$ is requested $q_i$ times. Likewise, with constants of its own, $T(X) \le 16n + C\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr) + D\,n(1 + \lfloor\log_2 n\rfloor)$ for every finger $f < n$.

In Lean, splaying is [[RotationBST.Splay.algorithm]], $T(X)$ is `d.startup + out.costs.sum`, and the bounds are [[RotationBST.workingSetSum]], [[RotationBST.StaticTree.cost]], [[RotationBST.Bounds.staticCost]] and [[RotationBST.Bounds.fingerCost]] of [Chapter 13](bounds.html).
```

The two boxes are all a reader needs to confirm the results. Their statements use the rotation model, the online algorithms of [Chapter 5](online.html), the pointer instructions of [Chapter 6](pointer.html) and [Chapter 10](fingers.html), the replay function of [Chapter 12](replay.html), and the three definitions of [Section 37.2](#physical-programs-and-their-responses). None of the machinery that builds the program appears in them.

The rest of the chapter has two layers. [Section 37.1](#the-plan) is a bird's-eye view of the construction, with its constants. [Section 37.2](#physical-programs-and-their-responses) to [Section 37.4](#deamortized-splay-trees) state the transformation theorem and its splay consequences again, in English and in Lean, with what each hypothesis means. [Section 37.5](#bounded-depth-simulation) to [Section 37.8](#from-rotation-algorithms-to-a-deamortized-program) open the construction: the bounded-depth simulation, the scheduler, and how they are composed. The structures they rely on are built in [Part V](part-structures.html). A reader who trusts the construction can skip those sections; a reader who wants to see where each constant comes from should read them. [Section 37.9](#what-is-not-formalized) lists what is not formalized. The definitions are in `Algorithms/Deamortization/{Scheduler,Finger,Algorithm}/Definitions/Abstract.lean`, the theorems in the `Abstract.lean` files of `Algorithms/Deamortization/{Weighted,Window,Scheduler,Finger,Replay,Algorithm}` and `Algorithms/Splay/Deamortization`.

## The plan

The paper's idea fits in two sentences. First, simulate the algorithm $A$ in a tree whose depth stays $O(\log n)$ at all times, at a constant factor in total cost (the paper's Theorem 5). Second, run that simulation, and whenever it has spent $c\log n$ operations without reaching the next requested key, walk to that key and back, which costs another $O(\log n)$ because the tree is shallow (Theorem 6). Every request is then served within $O(\log n)$ operations, and the detours at most triple the total.

The second step needs a shallow tree *at every intermediate moment*, not just between requests, because a detour can interrupt the simulation anywhere. This is what the first step provides, and it is where most of the work is. The library's chain has five links:

```
weighted stacks        pop-tarts: BSTs that implement a stack whose top is shallow
      │                ({{ref:poptarts}})
      ▼
heavy paths            the source tree, stored as pairs of pop-tarts along heavy paths,
      │                rebuilt locally after each source instruction (Sections {{num:heavy-paths}}–{{num:heavy-path-fingers}})
      ▼
bounded-depth          every source instruction becomes O(1) amortized physical
simulation             instructions, and every intermediate tree has depth
      │                ≤ 49 + 39 log₂ n ({{ref:finger-histories}}; Theorem 5)
      ▼
scheduled responses    each request consumes at most a budget of pending simulation
      │                work, then detours to the key; the simulation may lag behind
      ▼                (this chapter; Theorem 6)
applications           any rotation-model algorithm, splaying, and the combined
                       finger bound of {{ref:combined-finger}}
```

**Weighted stacks.** A pop-tart ([Chapter 44](pop-tarts.html)) is a BST that implements a stack of nodes, pushed in decreasing key order at the root, with $O(1)$ amortized BST operations per push and pop. Its leaves may carry weights. The chocolate pop-tart of the paper's Section 2 ([Chapter 45](chocolate.html)) keeps every leaf of weight $w$ at depth $O(\log(W/w))$, where $W$ is the total leaf weight, whatever the weights of the pushed leaves.

**Heavy paths.** The simulation keeps the source algorithm's tree, but stores it differently ([Chapter 46](heavy-paths.html) and [Chapter 47](recursive-heavy-paths.html)). Each heavy path is split at its bottom node into its nodes smaller and larger than that node. These two monotone sequences are stored as two pop-tarts below the bottom node, and the subtrees hanging off the path are leaves of the pop-tarts, represented recursively. Depths telescope along the dotted edges to $O(\log(W/w))$. The source's finger is represented the same way, by the path from the root to the finger turned upside down ([Chapter 48](heavy-path-fingers.html)), so the simulated finger is always at the physical root.

**Bounded-depth simulation.** [Chapter 49](finger-histories.html) packages this into a policy: a function that receives one source instruction (a move or a rotation of the source's finger) and emits a physical instruction stream that updates the representation. With unit weights it costs at most $62$ amortized physical instructions per source instruction, and at most $34 + 24\log_2 n$ in the worst case. Every intermediate physical tree, at every instruction boundary, has all depths at most $49 + 39\log_2 n$ ([[HeavyPath.Finger.History.Simulation.Interruption.Results.response_uniform]]). Measured from the cheapest representation of the starting tree, the factor is $248$.

**Scheduled responses.** The scheduler of this chapter fixes an integer budget $b$ with $49 + 39\log_2 n \le b < 50 + 39\log_2 n$. For each request it executes at most $b$ instructions of the pending simulated work. If the simulation reaches the requested key within these, the response ends there. Otherwise the finger walks to the key and back, which is cheap because the tree it walks in has depth at most $b$. The library bounds each response by five times the work it consumed, so it emits at most $5b$ instructions and costs at most $1 + 5b < 251 + 195\log_2 n$. The work that was not executed stays pending, so the simulation lags behind the requests. Each emitted instruction is charged to executed simulation work at most five times over.

**Applications.** A rotation-model algorithm is first turned into a pointer program whose recorded work is at most $64$ times its total cost (the replay planners of [Chapter 34](combo-workers.html), built on the lazy online simulation of [Chapter 6](pointer.html#running-an-online-algorithm-on-the-pointer-machine)). The constants then multiply:

| Step | Constant |
|---|---|
| Building the initial representation | setup $\le 16n$ |
| Rotation algorithm → pointer program | $64 \times$ total cost |
| Pointer program → bounded-depth simulation | $248 \times$ instructions |
| Simulation → scheduled responses | $5 \times$ executed work |
| Altogether | $64 \cdot 248 \cdot 5 = 79360$ |
| Per response | $1 + 5b < 251 + 195\log_2 n$ |

These are explicit witnesses, not optimized constants. The splay applications multiply further by splaying's own constants: $952320 = 12 \cdot 79360$ and $1111056 = 16 + 14 \cdot 79360$.

## Physical programs and their responses

The deamortized program works in the BST model of the paper: one finger that persists between requests, moves along edges and rotates at the node it stands on, each instruction at unit cost. This is the one-finger case of the model of [Chapter 10](fingers.html). Unlike the root-restarting pointer machine of [Chapter 6](pointer.html), returning to the root is not free. Instructions are [[RotationBST.Multifinger.Opcode]]s, executed on a single cursor by [[Multifinger.replay]] ([Chapter 12](replay.html)), which returns `none` at the first illegal instruction.

A program's output for a request sequence is one instruction stream. To speak of the cost of *each* response, the library records how the stream is cut:

@decl Deamortization.Scheduler.ServedStream

`ServedStream a keys c ops costs` says that the stream `ops` leads from cursor `a` to cursor `c` and serves `keys`, cut into one segment `before ++ after` per key. Within its segment, the cursor reaches a configuration `visited` whose key is the request, after the `before` part. The segments are contiguous: each starts at the cursor where the previous one ended. The cost of a response is $1 + |\mathit{before}| + |\mathit{after}|$, the request unit plus every instruction, exactly as in [[RotationBST.Multifinger.Serves]]. So the cost list has one entry per request, and sums to the number of requests plus the length of the stream.

The relation fixes the segmentation, which is what makes a per-response bound meaningful: without it, a total cost could be split into small "responses" arbitrarily. A visit may occur at the very start of the segment, with `before = []`, if the cursor already stands on the key.

@decl Deamortization.Scheduler.cursorState

`cursorState c` reads a cursor as a one-finger state of [Chapter 10](fingers.html): the tree of `c`, and one finger on the key under the cursor. The key is totalized to $0$ on an empty focus, which never occurs in the theorems below, since their cursors stand on actual nodes. Through it, the output is also stated as an ordinary [[RotationBST.Multifinger.Execution]].

@decl Deamortization.Scheduler.Output

An `Output` is what the scheduler returns for a whole request sequence: its final internal `state` ([Section 37.6](#pending-work-and-lag)), the emitted `instructions`, the number of source instructions it `consumed`, and the list of response `costs`. Only `instructions` and `costs` matter for the main theorems; the `state.cursor` field is the physical cursor at the end.

The deamortized program itself is a structure:

@decl Deamortization.Algorithm.Implementation

An `Implementation source saved` fixes the source algorithm and the initial tree `saved` as parameters. Everything else is chosen once, before any request sequence and before any cost bound that one might compare with:

- `initial` and `startup`: the physical tree on which the responses begin, and the cost of reaching it. `setup` is a [[RotationBST.Pointer.Trace]] from `saved` to `initial`, both with the cursor at the root, of exactly `startup` instructions, and `setup_bound` says $\mathtt{startup} \le 16n$. The setup is not part of any response. It restructures the arbitrary initial tree into the shallow representation, as the paper also requires when $T$ is unbalanced.
- `program`: a function from request sequences to outputs. Its value on a sequence is what the program does on that sequence.
- `correct`: for every sequence `keys` of valid ranks, the program produces an output `out` such that
  1. its instructions replay legally from `initial` to the final cursor;
  2. they form a `ServedStream` of `keys` with the response costs `out.costs`;
  3. the same run is a one-finger [[RotationBST.Multifinger.Execution]] of `keys` from the root of `initial`, of cost `keys.length + out.instructions.length`;
  4. there is one cost per request, and the costs sum to `keys.length + out.instructions.length`;
  5. the sum is at most `79360 * source.totalCost saved keys`, where [[RotationBST.Algorithm.totalCost]] counts one unit per request plus the source's rotations, from the original tree `saved`; and
  6. every response cost is below $251 + 195\log_2 n$, with $n$ = `saved.size` and the real logarithm.
- `causal`: if `program (xs ++ ys)` returns an output, then `program xs` returns one whose instructions and costs are prefixes of it.

`causal` is the paper's definition of an online algorithm, "$A(S)$ is a prefix of $A(S')$ whenever $S$ is a prefix of $S'$". Because the program is a function of the whole sequence, causality is what makes it online. Prefix preservation of the instructions alone would allow the response to $x_j$ to be split differently once later requests are known. The cost prefix fixes the segmentation as well: the first $j$ responses, as segments of the stream with their visits and costs, are the same for every continuation. Nothing done for $x_1, \dots, x_j$ depends on $x_{j+1}, \dots$. The comparison benchmarks of the next section are applied to this one program afterwards, so a single deamortized execution meets all of them at once.

::: check
- **Two trees.** The source cost is measured from `saved`, the tree the source starts from. The responses start from `initial`, after the setup. The final physical tree is not required to be the source's final tree: work that the scheduler has not yet executed when the sequence ends is never executed, and it is not needed.
- **Validity.** `correct` says nothing about sequences with a key outside $\{0, \dots, n-1\}$; the program may fail on them. Nonemptiness of `saved` is a hypothesis of the existence theorems, not a convention.
- **What is counted.** The fields count BST instructions only. `program` is an arbitrary Lean function: the computation that chooses the instructions, and whatever it remembers, are free, as in the paper's BST model. [Section 37.9](#what-is-not-formalized) comes back to this.
:::

## The transformation theorem

**Theorem (deamortization).** For every online rotation-model algorithm and every nonempty initial tree, a deamortized implementation exists.

@decl Deamortization.Algorithm.Results.implementation_exists

All guarantees are in the fields of [[Deamortization.Algorithm.Implementation]], so this one statement is the counterpart of Theorem 6. It is stated as `Nonempty`: the implementation is shown to exist, by choices made inside the proof ([Section 37.8](#from-rotation-algorithms-to-a-deamortized-program)), and is not claimed to be computable.

The next two theorems apply to *every* implementation, in particular the one just constructed. They add the setup to the response costs.

**Theorem (total cost).** For every implementation and every valid sequence $X$, the setup plus all response costs is at most $16n + 79360\,(m + R_A(X))$.

@decl Deamortization.Algorithm.Results.total_bound

**Theorem (transfer of bounds).** If the source's total cost on $X$ is at most a real number $B$, then the setup plus all response costs is at most $16n + 79360\,B$.

@decl Deamortization.Algorithm.Results.transfer

`transfer` is the tool for applications: any proved bound on the source, such as an entropy or working-set bound, becomes a bound on the deamortized program with the extra $16n$. The splay theorems of the next section are proved this way.

The paper's abstract also states a consequence for dynamic optimality: if a dynamically optimal BST algorithm exists, then one exists that answers every search in $O(\log n)$ operations. The library proves this implication.

**Theorem (dynamic optimality is preserved).** Suppose an online rotation-model algorithm $A$ is dynamically optimal for total cost: there are constants such that, from every tree, its total cost is at most $C(m + k) + Dn$ for every offline rotation-model execution of the same requests with $k$ rotations. Then there are constants $C'$ and $D'$ such that for every nonempty tree $T$ there is a deamortized implementation of $A$ from $T$ whose setup plus response costs, on every sequence, is at most $C'(m + k) + D'n$ for every offline execution of the sequence from $T$ with $k$ rotations.

@decl Deamortization.Algorithm.Results.dynamic_optimal

The hypothesis is [[RotationBST.TotallyDynamicallyOptimal]] of [Chapter 5](online.html#dynamic-optimality), and the comparator is any [[RotationBST.Execution]], so $k$ ranges over the offline optimum and everything above it. The proof is `transfer` with $C' = 79360\,C$ and $D' = 16 + 79360\,D$. The constants do not depend on $T$; the implementation does.

::: caveat
This theorem is **conditional**. It preserves dynamic optimality of an algorithm that is supplied with a proof of it. It asserts nothing about splaying, or about any other specific algorithm: no algorithm is known to satisfy the hypothesis.
:::

## Deamortized splay trees

Splaying is the paper's first application, and its abstract's first claim: a BST with the same asymptotic cost as splay trees on every sequence, and $O(\log n)$ worst-case cost per search. With [[RotationBST.Splay.algorithm]] as the source, the transformation theorem gives the program.

**Theorem (a deamortized splay program).** For every nonempty initial tree there is a deamortized implementation of splaying.

@decl Splay.Deamortization.Results.implementation_exists

Each of the following theorems holds for every implementation `d` of splaying and every completed run, so they hold simultaneously for one program on one run. They are the bounds of [Chapter 20](analysis.html) and [Chapter 21](beyond.html#sequential-access), passed through `transfer`, with the setup cost $16n$ included. In all of them, $T(X)$ = `d.startup + out.costs.sum`.

**Theorem (scanning).** Requesting all keys in increasing order costs at most $1111056\,n$, setup included.

@decl Splay.Deamortization.Results.scanning

The sequence is `List.range saved.size`, so validity is automatic. The constant is $16 + 79360 \cdot 14$, from splaying's sequential-access bound of $14n$ ([[RotationBST.Splay.Results.scanning]]), which holds from every initial tree.

**Theorem (balance).** $T(X) \le 16n + 79360\,\bigl(m(2 + 3\log_2 n) + n\log_2 n\bigr)$.

@decl Splay.Deamortization.Results.balance

**Theorem (working set).** $T(X) \le 16n + 79360\,\bigl(11\,W(X) + 6n(1 + \lfloor\log_2 n\rfloor)\bigr)$, where $W(X) = \sum_j (1 + \lfloor\log_2 w_j\rfloor)$ is [[RotationBST.workingSetSum]].

@decl Splay.Deamortization.Results.working_set

Splaying's working-set theorem bounds rotations by $10\,W(X) + 6n(1 + \lfloor\log_2 n\rfloor)$ ([[RotationBST.Splay.Results.workingSet]]). The eleventh copy of $W(X)$ pays for the $m$ request units, since $W(X) \ge m$. The startup term $6n(1 + \lfloor\log_2 n\rfloor)$ is part of the statement, multiplied like the rest.

The static bounds come in two versions, depending on whether the sequence requests every key. This *coverage* premise matters because unused keys still sit in the initial tree. Splaying's static-optimality proof uses the weights $q_i$, and its potential drops by at most $\sum_i \log_2(m/q_i)$ over the sequence. When every key is requested, every $q_i \ge 1$, and this is at most $\sum_i q_i\log_2(m/q_i)$, a part of the bound itself ([Chapter 20](analysis.html#static-optimality-theorem-2)). A key that is never requested has no term to pay for it, and an additive startup term is needed.

**Theorem (static optimality, every key requested).** If $X$ requests every key, then for every BST $u$ on the same $n$ keys, $T(X) \le 16n + 952320\,\sum_j (1 + \mathrm{depth}_u(x_j))$.

@decl Splay.Deamortization.Results.static_optimality

The right side is [[RotationBST.StaticTree.cost]]` reference xs`, the cost of serving $X$ by root searches in the fixed tree $u$. The constant is $12 \cdot 79360$, from [[RotationBST.Splay.Results.staticOptimality_fixedTree]]. Apart from the $16n$ of the setup, there is no startup term.

**Theorem (static finger, every key requested).** If $X$ requests every key, then for every natural number $f$, $T(X) \le 16n + 952320\,\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$.

@decl Splay.Deamortization.Results.static_finger

As in [[RotationBST.Splay.Results.staticFinger_all_accessed]], the finger $f$ is not required to be a key.

**Theorem (static optimality and static finger, general).** There are constants $C$ and $D$ such that for every tree on $n$ keys, every implementation and every valid sequence, $T(X) \le 16n + C\bigl(m + \sum_i q_i\log_2(m/q_i)\bigr) + D\,n(1 + \lfloor\log_2 n\rfloor)$. Likewise, with possibly other constants, $T(X) \le 16n + C\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr) + D\,n(1 + \lfloor\log_2 n\rfloor)$ for every finger $f < n$.

@decl Splay.Deamortization.Results.static_optimality_general Splay.Deamortization.Results.static_finger_general

These versions drop the coverage premise. In exchange they keep the startup term $n(1 + \lfloor\log_2 n\rfloor)$, and the constants are existential, inherited from [[RotationBST.Splay.Results.staticOptimality]] and [[RotationBST.Splay.Results.staticFinger]]. They are uniform: $C$ and $D$ are chosen before the tree, the implementation and the sequence. The bracket $m + \sum_i q_i\log_2(m/q_i)$ is [[RotationBST.Bounds.staticCost]], which is at most $3$ times the cost of every static tree, and the finger sum is [[RotationBST.Bounds.fingerCost]].

::: note Other applications in the book
The same transformation is applied, through the replay planners of [Section 37.8](#from-rotation-algorithms-to-a-deamortized-program), to the combination of GreedyASS and Tango in [Chapter 38](combined-finger.html). That chapter obtains one BST with the weighted dynamic finger bound, $O(\log\log n)$-competitiveness and $O(\log n)$ worst-case responses ([[Geometric.GreedyASS.Combination.Deamortized.Results.combined]]).
:::

## Bounded-depth simulation

The rest of the chapter opens the construction. This section is the library's form of the paper's Theorem 5, in the weighted version. It is a self-contained statement about the simulation of [Chapter 49](finger-histories.html), and the scheduler below uses its unit-weight form.

The source algorithm here is more general than a rotation-model algorithm. It is a [[HeavyPath.Finger.History.Simulation.Requests.Algorithm]]: an online rule that, given the past requests, its current *labelled cursor* ([[LabelledCursor.Config]], a tree whose nodes carry labels in some type $\alpha$, with a persistent cursor) and the next request, emits a list of source instructions that legally visits the requested key, and may keep working afterwards. Its cost is the number of instructions it emits, `(a.runFrom past c keys).1.length`. The labels carry the weights: $w$ is a function on labels, and $W$ is the total weight [[HeavyPath.mass]] of the source tree. [[HeavyPath.Positive]] asks for positive weights on the tree's labels.

**Theorem (bounded-depth simulation).** Let $c$ be a labelled source cursor on a nonempty tree, with positive weights. There are a fixed simulation policy, an initial representation and a setup trace of at most $16n$ instructions such that, for every source algorithm and every valid sequence, simulating the algorithm request by request:

1. produces the source's own final cursor, and a valid representation of it;
2. is a legal physical program from the root of the representation to its root, and a [[RotationBST.Pointer.Execution]] of the requests of cost $m$ plus its length;
3. costs at most $248$ physical instructions per source instruction;
4. leaves the source finger's key at the physical root; and
5. at every cut of the emitted stream, the intermediate physical tree has every key $x$ at depth at most $336 + 240\log_2(W/w_x)$.

@decl Deamortization.Weighted.Results.simulation

Item 5 is the strong form of Theorem 5's depth claim: it holds not only between source instructions, but at every physical instruction boundary of the emitted program. Item 4 is the paper's "the finger is always at the root of $T'$". The policy and the initial representation are chosen before the source algorithm, and they are [[HeavyPath.Finger.History.Simulation.PolicyWithin]], the bounded policies of [Chapter 49](finger-histories.html) with a structural depth certificate.

**Theorem (the simulation is online).** If simulating on `xs ++ ys` succeeds, then simulating on `xs` succeeds with a prefix of the instructions.

@decl Deamortization.Weighted.Results.online_prefix

**Theorem (the simulation program, Theorem 5).** For a family of source algorithms, one for each request sequence, there is one simulation program with the guarantees above, for the source chosen by the sequence. If the family is constant, the program is online.

@decl Deamortization.Weighted.Results.transform

The family lets the source depend on the whole sequence, which covers offline source algorithms, as in the paper's statement "for any BST algorithm $A$ … if $A$ is online, so is $A'$". The emitted instructions are prefix-preserving only when the family is constant, that is, when the source is one online algorithm.

::: check
The weighted results are not used by the deamortization theorems below, which need only unit weights. Those use the sharper unit-weight depth bound $49 + 39\log_2 n$ of [Chapter 49](finger-histories.html), proved directly for the same kind of policies.
:::

## Pending work and lag

The scheduler turns a stream of prepared request programs into responses. It knows nothing about heavy paths or pop-tarts. Its input is, for each request, the physical instruction stream that the simulation would execute for it, with two guarantees: the stream visits the requested key, and every intermediate tree along it is shallow.

@decl Deamortization.Scheduler.Height

`Height budget start ops` says that every prefix of `ops` that replays from `start` reaches a tree in which every key has depth at most `budget`. This is the property a detour needs: from any point of the pending work, any key can be reached and left in $O(\text{budget})$ instructions.

@decl Deamortization.Scheduler.Request Deamortization.Scheduler.Prepared Deamortization.Scheduler.PreparedStream

A `Request` is the target key with its physical program. `Prepared budget start request finish` says that the program replays from `start` to `finish`, that some prefix of it reaches a cursor on the target (so the program contains an actual visit), and that it satisfies `Height`. A `PreparedStream` chains prepared requests, each starting where the previous one's program ends. This chain follows the *source's* cursor, independently of what the scheduler has executed so far.

@decl Deamortization.Scheduler.State Deamortization.Scheduler.Valid Deamortization.Scheduler.initial

The scheduler's state has three parts:

```
      executed                    pending
 ─────────────────────|─────────────────────────────|
                    cursor                       planned
```

`cursor` is the actual physical cursor. `pending` is the simulation work not yet executed, and `planned` is where the simulation will be once it has all been executed. `Valid` says that the cursor is on an actual node, that `pending` replays from `cursor` to `planned`, and that it satisfies `Height`. `initial c` has nothing pending.

The gap between `cursor` and `planned` is the lag of the paper's proof: the deamortized algorithm can be ahead of the simulation in the input sequence. When a new request arrives, its program is appended after `pending` and starts at `planned`. No source instruction is ever dropped while requests keep arriving.

**Theorem (initial validity).** An initial state is valid if the cursor is on an actual node and every key of its tree has depth at most the budget.

@decl Deamortization.Scheduler.Results.initial_valid

## Serving one request

The core of a response is a statement about one window of pending work.

**Theorem (one window).** Let `ops` be a legal program from `start` to `finish` that visits the target and keeps every intermediate depth at most `budget`, with `start` on an actual node. Then there is a number `consumed` of instructions to execute, at most the budget, and a physical response `before ++ after` such that:

1. executing the first `consumed` instructions of `ops` reaches a cursor `middle`, and the rest of `ops` still leads from `middle` to `finish`;
2. `before` leads from `start` to a cursor on the target, and `after` from there to `middle`;
3. the response has at most $5 \cdot \mathtt{consumed}$ instructions, and at most $5 \cdot \mathtt{budget}$; and
4. either all of the budget was consumed, or `middle` itself is on the target.

@decl Deamortization.Window.Results.serve

This is the paper's rule, read for one request. Execute the source work; if the target is reached within the budget, stop there. Otherwise stop after the budget, and walk to the target and back. The walk stays within the tree reached after `consumed` instructions, whose depths are at most the budget, so it costs $O(\text{budget})$, and the library bounds the whole response by five times what it consumed. After the response, the physical cursor is exactly where the source work stands after `consumed` instructions: the detour returns precisely to it, so the remaining work can continue unchanged.

@decl Deamortization.Scheduler.Response Deamortization.Scheduler.Response.instructions Deamortization.Scheduler.Correct

A `Response` records the new state, the visited cursor, the two parts of the physical response and the number of pending instructions consumed. Its `instructions` are `before ++ after`. `Correct budget s request out` lists what a response must satisfy:

1. the new state is valid;
2. the planned endpoint advances by the request's whole program;
3. at most `budget` instructions are consumed, and no more than are pending, counting the new request's program;
4. the new pending work is what remains after them;
5. executing the consumed instructions leads from the old cursor to the new one;
6. `before` leads from the old cursor to a cursor on the target, and `after` from there to the new cursor; and
7. the response has at most $5 \cdot \mathtt{consumed}$ instructions, and its cost $1 + |\mathtt{instructions}|$ is at most $1 + 5 \cdot \mathtt{budget}$.

Three consequences are used repeatedly.

**Theorem (a correct response).** A correct response replays from the old cursor to the new one. It conserves work: pending plus consumed after the response equals pending before it plus the request's program. And, from a valid state, it is a one-finger [[RotationBST.Multifinger.Serves]] of the target at cost $1 + |\mathtt{instructions}|$.

@decl Deamortization.Scheduler.Results.response_replay Deamortization.Scheduler.Results.response_account Deamortization.Scheduler.Results.response_serves

## Running the scheduler

@decl Deamortization.Scheduler.Policy Deamortization.Scheduler.PolicyValid

A scheduling `Policy` is a function of the current state and the current request only, returning a response or `none`. It never sees later requests. `PolicyValid budget p` asks that, from every valid state, for every request prepared from the planned endpoint, the policy returns a correct response.

**Theorem (a valid policy exists).** For every budget there is a valid scheduling policy.

@decl Deamortization.Scheduler.Results.policy_exists

The proof applies the window theorem to the pending work followed by the new request's program, which is legal, visits the target and has bounded height, and chooses the result.

@decl Deamortization.Scheduler.run

`run p s requests` threads the state through the requests. It concatenates the response instructions, adds the consumed counts, and records the cost $1 + |\mathtt{instructions}|$ of each response.

**Theorem (scheduled run).** Let the policy be valid, the state valid, and the requests a prepared stream from its planned endpoint. Then the run succeeds, and:

1. it ends planned at the end of the stream, in a valid state;
2. its instructions replay from the cursor, and form a one-finger execution of the targets of cost $m$ plus their length;
3. pending plus consumed equals the initial pending plus all request programs;
4. it emits at most $5$ times what it consumed, and consumes at most the budget times the number of requests; and
5. it has one cost per request, summing to $m$ plus the number of instructions, each at most $1 + 5 \cdot \mathtt{budget}$.

@decl Deamortization.Scheduler.Results.run_spec

**Theorem (scheduled run, served).** Under the same hypotheses, the emitted instructions and the costs form a served stream of the targets.

@decl Deamortization.Scheduler.Results.run_served

**Theorem (prefixes).** Running on `xs ++ ys` is running on `xs` and continuing from its final state on `ys`, with outputs concatenated. Hence a run on `xs ++ ys` that succeeds extends a successful run on `xs`, in both instructions and costs.

@decl Deamortization.Scheduler.Results.run_append Deamortization.Scheduler.Results.run_prefix

`run_prefix` holds for every policy, valid or not: causality comes from the shape of `run` alone, because a policy sees only its state and the current request. This is where the causality of the final program comes from, once the preparation of the requests is causal as well.

## Preparing the source

This section composes the simulation of [Chapter 49](finger-histories.html) with the scheduler, for a source algorithm with labelled cursors, as in [Section 37.5](#bounded-depth-simulation), and unit weights.

@decl Deamortization.Finger.PreparedOutput Deamortization.Finger.prepare Deamortization.Finger.transform

`prepare` runs the source algorithm on the keys, request by request. For each key it takes the source's instructions for that key, simulates them with the policy [[HeavyPath.Finger.History.Simulation.run]], and records the resulting physical program as a [[Deamortization.Scheduler.Request]] for that key. It returns the final source cursor, the final representation and the list of requests. `transform` prepares the requests and schedules them, starting with the physical cursor at the root of the initial representation. The scheduler executes a prefix of the accumulated programs, so it may lag behind the preparation. Both policies are fixed before the keys, and the preparation sees each key only when it is requested.

The first group of results describes the preparation. The budget must be at least $49 + 39\log_2 n$, the unit-weight depth bound of the simulation; $s$ is a valid representation of the source cursor $c$, and the simulation policy is [[HeavyPath.Finger.History.Simulation.PolicyBounded]].

**Theorem (preparation).** The preparation succeeds on valid keys. It ends at the source's own final cursor, with a valid representation, one request per key, and a prepared stream from the root of the initial representation. Its total physical work plus the final potential is at most $62$ times the source's instructions plus the initial potential. Measured by the excess over the cheapest representation of the same source cursor ([[HeavyPath.Finger.History.Simulation.Minimum.excess]]), the factor is $248$.

@decl Deamortization.Finger.Results.prepare_spec Deamortization.Finger.Results.prepare_excess

**Theorem (preparation is causal).** Preparing `xs ++ ys` is preparing `xs` and continuing with history `past ++ xs`. Its requests extend those of `xs`.

@decl Deamortization.Finger.Results.prepare_append Deamortization.Finger.Results.prepare_prefix

The second group describes the composed transform.

**Theorem (initial validity).** The scheduler's initial state at the root of a valid representation is valid for every budget of at least $49 + 39\log_2 n$.

@decl Deamortization.Finger.Results.initial_valid

**Theorem (transform).** With a bounded simulation policy and a valid scheduling policy, the transform succeeds on valid keys. Its instructions are legal, serve the keys as a one-finger execution and, with the excess version, as a served stream. The responses cost at most $1 + 5 \cdot \mathtt{budget}$ each. The physical instructions, plus $5$ times the pending work and the final potential, are at most $310$ times the source's instructions plus $5$ times the initial potential. Measured by excess, the factor is $1240$.

@decl Deamortization.Finger.Results.transform_spec Deamortization.Finger.Results.transform_excess

**Theorem (transform is causal).** A successful transform on `xs ++ ys` extends a successful transform on `xs`, in instructions and costs.

@decl Deamortization.Finger.Results.transform_prefix

The last group chooses the policies, the budget and the initial representation. Two versions differ in the starting representation.

**Theorem (an initialized transform).** For a source algorithm and a source cursor on a nonempty tree, there are a bounded simulation policy, a valid scheduling policy, a budget below $50 + 39\log_2 n$, a valid representation and a setup trace of at most $16n$ instructions to reach it, such that on every valid sequence, setup and responses together cost at most $131n + m + 310 \cdot (\text{source instructions})$, and every response costs less than $251 + 195\log_2 n$.

**Theorem (a minimized transform).** As above, but the representation is the cheapest one, with zero excess, and everything is chosen before the source algorithm. Then for *every* source algorithm the physical instructions are at most $1240$ times the source's, with a served stream, and every response costs less than $251 + 195\log_2 n$.

@decl Deamortization.Finger.Results.initialized_transform Deamortization.Finger.Results.minimized_transform

The first version pays the setup and the initial potential, which is linear, in the $131n$ term. The second avoids any additive term by starting from a representation of least potential; the setup still pays $16n$ to build it. In `minimized_transform`, the policies, the budget and the representation are fixed before the source algorithm is named, so the physical machinery is the same for all sources.

**Theorem (abstract deamortization).** For a family of source algorithms, one per request sequence, and a source cursor on a nonempty tree, there are an initial representation, a setup trace of at most $16n$ instructions and one program such that on every valid sequence the program serves it as a one-finger execution and a served stream, emits at most $1240$ times the instructions of the source chosen for that sequence, and costs less than $251 + 195\log_2 n$ per response. If the family is constant, the program is causal in instructions and costs.

@decl Deamortization.Finger.Results.deamortize

This is the library's most general form of Theorem 6. As in `Weighted.Results.transform`, the family covers sources that depend on the whole sequence, and causality is claimed only for a single online source, matching the paper's "if $A$ is online, so is $A''$".

## From rotation algorithms to a deamortized program

The last step connects the abstract theorem to the algorithms of the book, which are rotation-model algorithms or root-restarting pointer programs. The bridge is the replay planner of [Chapter 34](combo-workers.html), [[Combo.Worker.Replay.Planner]]: a causal rule that, for each request, plans a pointer program from the root of its current tree back to the root, visiting the key. [[Combo.Worker.Replay.run]] counts its recorded work, the length of each plan plus $2$ per request. A planner has two sides (a `Bool`), because the combination of [Chapter 33](combining.html) runs two of them; here one side is used.

**Theorem (deamortizing a planner).** For every planner on a nonempty tree, and either side, there are an initial tree, a setup trace of at most $16n$ instructions and one causal program such that on every valid sequence the program serves it as a served stream and a one-finger execution, its costs sum to at most $1240$ times the planner's recorded work, and each response costs less than $251 + 195\log_2 n$.

@decl Deamortization.Replay.Results.deamortize

The proof labels the tree by its ranks, reads the planner as a source algorithm with a persistent cursor, and applies `Finger.Results.deamortize` with a constant family, which gives causality. Each plan starts and ends at the root, so consecutive plans chain into one program of a persistent cursor.

`implementation_exists` then takes the planner of [[Combo.Worker.Replay.Results.algorithm_planner]], which runs a rotation-model algorithm through the lazy online simulation of [Chapter 6](pointer.html#running-an-online-algorithm-on-the-pointer-machine) and records at most $64$ times its total cost. Composing gives $1240 \cdot 64 = 79360$, the constant of [[Deamortization.Algorithm.Implementation]]. [Chapter 38](combined-finger.html) uses `Replay.Results.deamortize` directly, with its own planner.

## What is not formalized

The library proves the abstract BST-operation result of Theorem 6, its unit-weight and weighted simulations (Theorem 5), and the Splay bounds above. The following parts of the paper are not formalized.

- **Theorem 7.** The paper's Theorem 7 strengthens Theorem 6 for algorithms with an amortized bound $O(nf(n) + kf(n))$, $f(n) = \Omega(\log n)$: the deamortized algorithm works in the pointer machine model with $O(1)$ words per node and $O(1)$ global variables, and computes each access in time proportional to its BST operations. None of these clauses is formalized: the bounds on private computation, on auxiliary storage (the paper's queue of pending keys, stored in the tree nodes, and its overflow argument), and execution on a finite-word machine. In the library, `program` is an arbitrary function, and the pending work of the scheduler is an unbounded list.
- **Cole's dynamic finger theorem for splaying.** The paper deamortizes all of splaying's known bounds, including the dynamic finger bound [@cole2000sorting; @cole2000proof]. The library has no proof of the dynamic finger theorem for splay trees, so it does not state it for the deamortized program. (The weighted dynamic finger bound for a different deamortized BST is the subject of [Chapter 38](combined-finger.html).)
- **Key-independent optimality** of splay trees [@iacono2005], and therefore its deamortized form, is not formalized.
- **Multi-splay trees.** The paper's application to multi-splay trees [@wang2006], a deamortized BST that is $O(\log\log n)$-competitive and has the scanning, static optimality, static finger and working-set bounds, is not formalized, since the library has no multi-splay trees. [Chapter 38](combined-finger.html) obtains a deamortized $O(\log\log n)$-competitive BST by a different route, combining GreedyASS with Tango.
- **Dynamic optimality.** [[Deamortization.Algorithm.Results.dynamic_optimal]] is an implication. No dynamically optimal algorithm is known, and none is claimed.
