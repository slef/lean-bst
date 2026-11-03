# The pointer machine

The root-access model of [Chapter 3](accesses.html) lets an access rotate anywhere in the tree and charges only for rotations. The standard BST model of the literature (Wilber; Demaine, Harmon, Iacono, Kane and Pătraşcu) is more operational. A single pointer starts at the root for each request. It moves along edges and rotates the node it points to over its parent. Every move and every rotation costs one unit, and the pointer must visit the requested key. This chapter defines that machine in Lean and proves that the two models agree up to constant factors in total cost, offline for executions and online for algorithms.

```headline pointer-model
title: The rotation model and the pointer machine agree up to constant factors
theorems: Pointer.Results.to_rotations Pointer.Results.to_pointer_lazy

Total cost means requests plus rotations ($m + R$) in the rotation model, and requests plus pointer instructions ($K$) on the pointer machine. Let $X$ be a sequence of $m$ requests and $s$ a tree.

1. **Pointers to rotations.** If the pointer machine serves $X$ from $s$ at total cost $K$, ending in tree $t$, then some root-access execution serves $X$ from $s$ with $R$ rotations and ends $q$ rotations away from $t$, where $m + R + q \le 3K$.
2. **Rotations to pointers.** If a root-access execution serves $X$ from $s$ with $R$ rotations, ending in tree $t$, then the pointer machine serves $X$ from $s$ at total cost $K$, ending $d$ rotations away from $t$, where $K + 32d \le 32R + 17m$.

The constants do not depend on the size of the tree. In both directions the final trees may differ, by a number of rotations that the bound pays for.

In Lean, rotation-model executions are [[RotationBST.Execution]], pointer executions are [[RotationBST.Pointer.Execution]], and [[RotationBST.Rotations]]` u t q` says that `q` rotations turn `u` into `t`.
```

The definitions are in `Models/Pointer/Machine/Abstract.lean` and the simulation theorems in `Models/Pointer/Abstract.lean`. The later sections walk through the readable interface of the constant-factor ("lazy") simulation, and then run it online.

## Configurations

The machine state is a *zipper*: the subtree under the cursor, plus the path back to the root. Each step of that path is recorded by a frame.

@decl RotationBST.Pointer.Frame

A frame describes one ancestor of the cursor. `left right` means the cursor is in the *left* subtree of this ancestor, whose other child is `right`. `right left` is the mirror case. The ancestor itself stores nothing more, because shapes have no keys. The constructor name says which side the cursor is on, and its argument is the sibling subtree. So `Frame.left` stores a right subtree, which is easy to misread.

@decl RotationBST.Pointer.plug RotationBST.Pointer.offset

`plug cs t` rebuilds the whole tree from the focused subtree `t` and the frames `cs`, nearest ancestor first, wrapping `t` one ancestor at a time. `offset cs` counts the keys that precede the focused subtree in inorder. A `left` frame adds nothing, since the cursor is to the left of everything in that ancestor's other subtree. A `right l` frame adds the `l.size` keys of the left sibling plus `1` for the ancestor itself.

@decl RotationBST.Pointer.Config RotationBST.Pointer.Config.tree RotationBST.Pointer.Config.key?

A configuration pairs the focus with its context. `Config.tree` is the whole tree it represents. `Config.key?` is the rank of the node under the cursor: `offset` plus the size of the focus's left subtree, which is the same offset arithmetic as in [Chapter 1](shapes.html#implicit-keys). It is `none` when the focus is empty. The initial configuration for a request on tree `s` is `⟨s, []⟩`: the cursor is on the root and the context is empty.

## Instructions

@decl RotationBST.Pointer.Step

The six instructions, each matched on the shape of the configuration:

- `downLeft`, `downRight` move to a child. The pattern `.node (.node a b) r` requires the left child to be a real node, so **the cursor never moves onto `nil`**. This is the docstring's promise that the cursor always points to an actual node when an instruction is taken.
- `upLeft`, `upRight` move to the parent, popping one frame and rebuilding the parent around the focus.
- `rotateLeftChild` applies when the cursor is a left child (top frame `.left r`). It rotates the cursor's node over its parent, so `x` with children `a, b` under a parent whose right subtree is `r` becomes `x` with children `a` and `(b r)`. The cursor stays on `x`, which is now one level higher, so one frame is consumed. On the whole tree this is a [[RotationBST.Rotate]]`.right` inside the context. `rotateRightChild` is the mirror image and corresponds to `Rotate.left`.

There is no instruction that rotates a node the cursor is not on, and there is no "jump". Each instruction costs one unit, and traces record the exact count:

@decl RotationBST.Pointer.Trace

## Serving a request

@decl RotationBST.Pointer.Serves

`Serves s t x cost` says that a search for `x` on tree `s` can end with tree `t` at the given cost. Concretely, there are configurations `visited` and `finish` and step counts `before` and `after` such that:

1. a trace of `before` instructions goes from the root configuration `⟨s, []⟩` to `visited`,
2. the cursor of `visited` is on rank `x` (`visited.key? = some x`),
3. a further trace of `after` instructions goes from `visited` to `finish`,
4. `finish` represents `t`, wherever its cursor is, and
5. `cost = 1 + before + after`: one unit for the request plus every instruction.

The search may restructure both before and after reaching `x`, and need not end at `x` or at the root. Returning the cursor to the root is free, since the next request starts again at `⟨t, []⟩`; this is the usual convention. The extra unit means that a request for the root, served with no instructions, still costs $1$.

@decl RotationBST.Pointer.Execution

A pointer execution serves the requests in order, each starting from the previous search's final tree, and adds up the costs. Its structure is the same as [[RotationBST.Execution]], with `Serves` in place of `Access`.

@viz pointer {"n": 9, "seed": 3, "requests": [6, 2, 6]}

::: exercise Serve the requests
Each button is one `Pointer.Step` constructor, enabled exactly when its pattern matches. Walk to the orange key; the panel reports when the visit condition holds and computes `1 + before + after`. You may keep rotating afterwards; "Finish request" then plugs the configuration back into a tree and starts the next search at its root.
:::

::: check
- `Serves` existentially quantifies the visit, so it describes all legal searches. An algorithm in this model is any way of choosing them.
- In the classical model the pointer may also be "reset" between accesses at no cost. Here the reset is implicit, because each `Serves` starts at `⟨s, []⟩`.
- The cost of moving and the cost of rotating are the same. Rotation-only costs, as in [Chapter 3](accesses.html), are not this model.
:::

## The two models agree

The comparison uses total cost on both sides: requests plus rotations ($m + R$) in the rotation model, and requests plus instructions in the pointer model. Executions are related directly, and each direction keeps an explicit, charged suffix of rotations at the end.

### From pointers to rotations

**Theorem (pointers to rotations).** A pointer execution of total cost $K$ from `s` to `t` gives a root-access execution from `s` to some `u` with $R$ rotations, plus $q$ further rotations from `u` to `t`, with $m + R + q \le 3K$.

@decl RotationBST.Pointer.Results.to_rotations

The proof treats each search separately. Moves cost nothing in the rotation model, and the rotations performed before the visit are kept. At the visit, the cursor is at some depth $d \le$ `before`, since each instruction changes the depth by at most one. Rotating `x` over its $d$ ancestors puts it at the root, which completes a root access. Undoing those $d$ rotations and then replaying the search's remaining rotations yields `t`. These $d + {}$(rotations after the visit) form the suffix, which is prepended to the *next* access, so the rotation execution can continue from the pointer execution's tree. Per search, the rotation cost is at most $(\text{rotations before}) + 2d + (\text{rotations after}) \le 3 \cdot \text{before} + \text{after}$, which with the request unit is at most $3 \cdot \text{cost}$. Only the last search's suffix remains pending at the end. That is the `Rotations u t q` conjunct, and its cost $q$ is included in the bound.

### From rotations to pointers, exactly

**Theorem (exact simulation).** Every root-access execution from `s` with $R$ rotations has a pointer execution from `s` with *the same final tree* and total cost at most $m + 2nR$, where $n$ = `s.size`.

@decl RotationBST.Pointer.Results.to_pointer

Each rotation is simulated separately: walk from the root to the rotated node's parent, step to the child, rotate, and walk back. A rotation at depth $d$ costs $2d + 2 \le 2n$ instructions. After all of an access's rotations the requested key is at the root, where the cursor already is, so the visit is free. The factor $n$ is necessary for this naive simulation, because the rotation model charges a deep rotation the same as a shallow one. This is why the following theorem is needed.

### From rotations to pointers, lazily

**Theorem (lazy simulation).** A root-access execution from `s` to `t` with $R$ rotations and $m$ requests has a pointer execution from `s` of total cost $C$ ending at some `u`, and $d$ deferred rotations take `u` to `t`, with
$$C + 32\,d \le 32\,R + 17\,m.$$

@decl RotationBST.Pointer.Results.to_pointer_lazy

The bound does not depend on tree size. Since $d \ge 0$, the pointer cost satisfies $C \le 32(m+R)$. Together with `to_rotations`, this makes the total costs of the two models equivalent within constant factors, for every execution and every tree.

::: caveat Final trees can differ
The lazy simulation does not end in the same tree. Rotations that the rotation model performs far from the current request are *postponed* until a later request needs them. Those still pending after the last request form the suffix `Rotations u t d`. They are not dropped: they are paid for in the bound with weight $32$, the same as executed rotations. They are simply not executed by the pointer machine. If you need the exact final tree, use `to_pointer`, which pays the factor $n$. The README states the same trade-off.
:::

## Inside the lazy simulation

The proof of `to_pointer_lazy` is too long to explain here, but its components are exposed through readable statements in `Models/Pointer/Lazy/Abstract.lean` and the definition files under `Models/Pointer/Lazy/`. Those statements are not used by the headline theorem's *statement*. They are shown so that a reader can follow the argument and check its key lemmas.

### Rotations with named endpoints

To reason about which rotations interact, the proof works on labelled trees and records each rotation by the keys of its two endpoints.

@decl RotationBST.Pointer.Lazy.RotateAt

`RotateAt x y s t` is a labelled rotation that promotes key `x` over its parent `y`. In `right`, `x` is the left child of `y`; in `left`, it is the right child. `inLeft` and `inRight` place the rotation inside a subtree whose root key `z` is arbitrary. Forgetting the endpoint labels gives back [[RotationBST.LabelledTree.Rotate]].

@decl RotationBST.Pointer.Lazy.Trace RotationBST.Pointer.Lazy.rootKey?

A `Trace` is a rotation sequence together with its program: the list of endpoint pairs `(x, y)`, in order. `rootKey?` reads the root label.

**Theorem (exchange).** If a rotation of `x` over `y` turns `s` into `t`, and a rotation of `u` over `v` turns `t` into `z`, and the four endpoints are distinct, then the two rotations can be performed in the opposite order: rotating `u` over `v` and then `x` over `y` also turns `s` into `z`.

@decl RotationBST.Pointer.Lazy.Results.commute

This holds even when one rotation is inside a subtree moved by the other: rotations are identified by their endpoint keys, not by tree positions, so they still make sense after the exchange. The hypothesis says that no endpoint of the first rotation is an endpoint of the second:

@decl RotationBST.Pointer.Lazy.DisjointPairs

### Postponing independent rotations

Repeated exchanges sort a program by any colouring of keys in which every rotation has both endpoints of the same colour.

**Theorem (postponing).** Colour the keys so that both endpoints of every rotation of a program have the same colour, and suppose the program ends with a selected key `x` at the root. Then the selected rotations alone, in their original order, form an access to `x`, and the unselected rotations, run afterwards, reach the same final tree.

@decl RotationBST.Pointer.Lazy.Results.postpone_access

In Lean: colour the keys with `color : α → Bool` so that every rotation of the program `ops` has equally coloured endpoints (`uniform`). Suppose the program ends with `x` at the root and `x` is selected (`color x = true`). Then the selected rotations alone, in their original order, already form a labelled access to `x`, and the unselected ones, run afterwards, reach the same final tree. The two counts add up to `ops.length`, so nothing is added or lost. Unselected rotations never touch the selected root's key, so they can be postponed past the access.

The proof uses a particular colouring, the connected component of the initial root in the *rotation graph*, whose edges are the endpoint pairs of the program:

@decl RotationBST.Pointer.Lazy.Connected RotationBST.Pointer.Lazy.endpointSupport RotationBST.Pointer.Lazy.componentKeys

`Connected ops` is the equivalence relation generated by the pairs in `ops`: reflexive, symmetric and transitive closure of the edges. `endpointSupport ops` lists both endpoints of every rotation, keeping duplicates, so its length is exactly `2 * ops.length`. `componentKeys color wanted t` lists, in inorder, the keys of the maximal region of colour `wanted` that contains the root of `t` and is connected in the tree. If the root has the other colour, the region is empty.

Colouring keys by "connected to the initial root in the rotation graph" makes every rotation uniform, because both endpoints of a rotation are connected to each other. In the proof (`Models/Pointer/Lazy/RootComponent.lean`), distinctness of keys then gives two facts. First, the selected keys form a connected region at the top of the initial tree. Second, that region contains at most $2r+1$ keys, where $r$ is the number of selected rotations: the root, plus at most two endpoints per rotation. This is where `endpointSupport` comes in.

### Reshaping a connected region

The selected rotations only rearrange this top region. Every subtree hanging off it is moved as a block and never entered. The proof captures such a region as a skeleton:

@decl RotationBST.Pointer.Lazy.Skeleton RotationBST.Pointer.Lazy.Skeleton.tree RotationBST.Pointer.Lazy.Skeleton.size RotationBST.Pointer.Lazy.Skeleton.fringe RotationBST.Pointer.Lazy.Skeleton.vine

A skeleton is a tree whose leaves are *holes*, each holding an entire untouched `Tree`. The same type reappears in [Chapter 7](regions.html) as the *rooted region* touched by one request, the unit of cost in the region model. `tree` fills the holes in. `size` counts only the region's own nodes, so a hole contributes $0$ however large its subtree is. `fringe` lists the hole subtrees in inorder; a region with $k$ nodes has $k+1$ of them. `vine` builds the canonical right spine whose left children are the fringe subtrees, in order, with the last one at the bottom on the right.

**Theorem (reshaping).** Two regions with the same fringe, in the same order, can be transformed into one another by a pointer trace from root to root with at most $16k$ instructions, where $k$ is the number of nodes in the first region.

@decl RotationBST.Pointer.Lazy.Results.reshape

The bound does not depend on the sizes of the fringe subtrees. The proof flattens both regions into the common vine, using at most $4k$ instructions each, and runs the second flattening backwards. Reversing a pointer trace costs at most three instructions per instruction, since undoing a rotation requires stepping to the demoted node. In total this is $4k + 3 \cdot 4k = 16k$.

### Putting it together

For one access with $r$ selected rotations, the region has at most $2r+1$ nodes. Reshaping it costs at most $16(2r+1) = 32r + 16$ instructions, and the request unit gives $32r + 17$. The requested key ends at the root, where the cursor is, so the visit is free. The unselected rotations become pending. They are prepended to the next access, where they are selected or postponed again, and each rotation is charged once, when it is finally executed or left in the final suffix. Summing over the execution gives $C + 32d \le 32R + 17m$. The README describes the same argument in prose. The last section shows how the library turns this into an *online* transformer that uses only the past and the current request.

## Running an online algorithm on the pointer machine

The lazy simulation above reorders rotations and postpones those that the current request does not need. As stated, it is an offline construction: it takes a whole execution as input. This section shows that it can also be run *online*, for the [online algorithms](online.html#online-algorithms) of [Chapter 5](online.html): each pointer step depends only on the past, the current request and a simulation state. Every online rotation-model algorithm therefore yields an online pointer algorithm with constant overhead.

The simulator maintains two trees:

@decl RotationBST.Pointer.Lazy.Online.State RotationBST.Pointer.Lazy.Online.initial

`virtual` is the tree that the rotation-model algorithm believes it has. `current` is the tree actually present in the pointer machine. The `pending` rotations that the pointer machine has not yet performed separate them, and `certificate` proves this (`Rotations current virtual pending`). Initially both trees are the input tree and nothing is pending. The state contains no future requests.

One step of the simulation is specified as a relation:

@decl RotationBST.Pointer.Lazy.Online.Transition

Given state `s` and request `x`, a result `(s', c)` is a valid transition when:

1. the pointer machine serves `x` from `s.current`, ending at `s'.current` and paying `c` ([[RotationBST.Pointer.Serves]], which includes the unit request charge);
2. the new virtual tree is exactly what the algorithm's own step produces from the old virtual tree, so the algorithm runs unmodified on its own view; and
3. an amortized bound holds with potential $32 \cdot{}$`pending`: the actual cost plus the new potential is at most $32$ times the old pending work plus the algorithm's rotations, plus $17$.

**Theorem (a transition exists).** For every algorithm, history and simulation state, and every request `x` that is a key of the virtual tree, there is a valid transition. This is the per-request form of the lazy simulation above.

@decl RotationBST.Pointer.Lazy.Online.advance_exists

The simulator *chooses* one transition:

@decl RotationBST.Pointer.Lazy.Online.advance RotationBST.Pointer.Lazy.Online.run

`advance` picks a transition with `Classical.choose`, so it is `noncomputable`. It is a mathematical function of `(a, past, s, x)`, not an executable program. An invalid request leaves the state unchanged at cost $0$; it is never reached by the theorems below, which assume validity. `run` threads the state through the sequence and appends each request to the history, exactly like [[RotationBST.Algorithm.runFrom]].

::: caveat Uncharged planning
Choosing the pointer instructions requires knowing a valid transition, and finding one involves the lazy-simulation construction on the current pending rotations. As in the rotation model, this planning is not charged. The cost bound counts pointer instructions and requests only. The library's README states this explicitly.
:::

The main theorem runs the simulator from the initial state.

**Theorem (online simulation).** Let `a` be an online rotation-model algorithm, `t` a tree and `xs` a sequence of $m$ keys of `t`, served with $R$ rotations by `a`. Running the simulator on `xs` from `t` produces a pointer execution of total cost $C$ whose final tree is `pending` rotations away from the algorithm's final tree, and $C + 32 \cdot \mathtt{pending} \le 32R + 17m$.

@decl RotationBST.Pointer.Lazy.Online.Results.simulation

The three conjuncts say:

1. **Legality.** The chosen instructions form a pointer execution serving `xs` from `t`, with final pointer tree `(run …).1.current` and cost `(run …).2`.
2. **Agreement up to the deferred suffix.** The final pointer tree reaches the final tree of the rotation-model algorithm by exactly `pending` rotations. The two executions end in the same place, except for work that has been postponed and not yet paid for.
3. **Cost.** Pointer cost plus $32$ times the pending suffix is at most $32R + 17m$, where $R$ is the algorithm's rotation count. In particular the pointer cost alone is $O(R + m) = O(T)$, with constants independent of $n$.

Causality is visible in the types (`advance` never receives the future), and the library also states it as a theorem.

**Theorem (no lookahead).** Running the simulator on `xs ++ ys` gives the same result as running it on `xs`, then continuing from the resulting state, with history `past ++ xs`, on `ys`. The costs add.

@decl RotationBST.Pointer.Lazy.Online.Results.prefix_composition

The state and cost after the prefix `xs` are therefore the same for every continuation `ys`. Nothing computed for the first requests can depend on later ones, so there is no lookahead.

Finally, the property this transfer was built for.

**Theorem (dynamic optimality transfers).** If an online algorithm is dynamically optimal in the rotation model, with total cost as the measure, then there are constants $C$ and $D$ such that its pointer-machine simulation, on every tree `t` and every sequence `xs`, costs at most $Ck + D\,n$ for every offline pointer execution of cost $k$ serving `xs` from `t`, where $n$ = `t.size`.

@decl RotationBST.Pointer.Lazy.Online.Results.dynamicOptimality

The comparison is against **every offline pointer execution** `Pointer.Execution t xs u k`. Both sides of this comparison are in the pointer model. The proof composes three bounds: an offline pointer execution of cost $k$ yields a rotation execution of total cost at most $3k$ ([[RotationBST.Pointer.Results.to_rotations]]); total dynamic optimality bounds the algorithm by that execution; and `simulation` bounds the pointer cost by the algorithm's rotation-model cost. The resulting constants are $(96C, 32D)$.

::: check
Conventional dynamic optimality is a statement about pointer-model algorithms competing with pointer-model optima. This theorem says that a proof of `TotallyDynamicallyOptimal` for any rotation-model algorithm would give exactly that: an online pointer algorithm that is dynamically optimal in the conventional sense. The hypothesis is the total-cost notion. The rotation-only `DynamicallyOptimal` is stronger, and is never needed.
:::

The working-set transfer [[RotationBST.Pointer.Lazy.Online.Results.workingSet]] has the same shape. It is stated in [Chapter 10](bounds.html#transfer-to-the-pointer-machine), after the working-set bound is defined.
