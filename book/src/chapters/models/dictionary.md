# Insertions and deletions

Every model so far serves accesses to a fixed set of keys. The classical search trees of [Part III](part-classical.html) are dictionaries. Their main results concern insertions and deletions, and the rebalancing that follows each one. This chapter defines a model for such operations, shared by all of them.

The model keeps the rank view of [Chapter 1](shapes.html#implicit-keys) and changes three things with respect to the root accesses of [Chapter 3](accesses.html):

- **Searches are charged.** An operation pays one unit for each node of the search path to the place where it acts, plus one unit per rotation. A search that changes nothing then costs $1 + \mathrm{depth}(x)$, exactly the static cost [[StaticTree.cost]] of [Chapter 13](bounds.html#comparison-with-a-fixed-tree), and nothing forces the key to the root.
- **The key set changes.** An insertion names the gap $k \in \{0, \dots, n\}$ where the new key goes; every rank from $k$ on then grows by one. A deletion names a rank; every later rank then drops by one.
- **Nodes carry balance data.** Rank-balanced trees store an integer rank, red-black trees a colour, BB[α] trees a subtree size, and scapegoat trees nothing at all. Trees with data are the labelled trees of [Chapter 1](shapes.html#labelled-trees), whose labels are the data, while keys stay inorder ranks. Changing a node's datum is counted separately from rotations, because the classical results bound the two separately.

```headline dictionary-embeds
title: Root accesses are dictionary executions, at cost at most $m + 2R$
theorems: Dictionary.Results.of_execution Dictionary.Results.static_execution

Every execution of the rotation model that serves $m$ requests with $R$ rotations is also an execution of the dictionary model, serving the same requests as accesses and ending in the same tree, at main cost at most $m + 2R$. In the other direction, searching a tree without changing it is a dictionary execution whose cost is the static search cost $\sum_j (1 + \mathrm{depth}(x_j))$.

In Lean, the executions are [[RotationBST.Execution]] and [[RotationBST.Dictionary.Execution]], and trees without data become trees with unit data by [[RotationBST.Tree.unit]].
```

The bound $m + 2R$ holds because each rotation raises the requested key by at most one level, so the search path to it, in the tree before its access, is paid for by the rotations that bring it to the root.

## Operations

@decl RotationBST.Dictionary.Op RotationBST.Dictionary.Op.Valid RotationBST.Dictionary.Op.resize RotationBST.Dictionary.Op.ValidSeq

An operation is valid on $n$ keys when its rank exists, or its gap, for an insertion. `resize` gives the number of keys after the operation, and `ValidSeq n ops` checks every operation of a sequence against the number of keys it meets. Split and join, which the splay model of [Section 23.3](beyond.html#updates) also supports, are not part of this model.

## Moves and structural changes

Between the structural changes, a tree is rearranged by rotations, which carry the data with the nodes ([[LabelledTree.Rotate]], [Chapter 4](keys.html)), and by changes of one node's datum:

@decl RotationBST.Dictionary.Edit RotationBST.Dictionary.Moves

`Moves s t a e` says that `a` rotations and `e` data edits, in any order, turn `s` into `t`.

An update changes the structure exactly once. Both insertions and deletions use one relation, read in the two directions:

@decl RotationBST.Dictionary.Splice RotationBST.Tree.TwoChildren

`Splice t x u` says that the node of rank `x` in `t` has at most one child, and that `u` is `t` with that node removed, its child taking its place. Read forwards it is a deletion. Read backwards, from `u` to `t`, it inserts a node at rank `x`, either as a new leaf or above an existing subtree. A node with two children cannot be removed directly: the classical deletions remove its predecessor or successor instead, which has at most one child, and keep the node itself. `TwoChildren` detects that case.

The simplest insertion, with no rebalancing, adds a leaf at the gap:

@decl RotationBST.Tree.insertAt RotationBST.LabelledTree.insertAt RotationBST.Tree.unit

`insertAt t g` walks down by comparing the gap with the size of the left subtree, and puts the new node in the empty position it reaches, so that the new node gets rank `g`. The labelled version takes the new node's datum as an argument: a rank-balanced tree inserts a node of rank $0$. `Tree.unit` gives a shape unit data, which is how the model treats trees that store nothing.

## Steps and executions

@decl RotationBST.Dictionary.Step

`Step s op t c e` is one operation from `s` to `t`, with main cost `c` and `e` data edits:

- **Access** to `x`: moves only. It pays $1 + \mathrm{depth}(x)$ in `s`, plus its rotations.
- **Insertion** at gap `k`: moves, then the structural change, then moves again. It pays $1 + \mathrm{depth}$ of the new node at the moment it is added, plus all rotations.
- **Deletion** of `x`: moves, then a splice of the node of rank `x`, or of its neighbour `x - 1` or `x + 1` when the node at `x` has two children, then moves. It pays $1 + \mathrm{depth}$ of the spliced node, plus all rotations. When a neighbour is spliced, the node at `x` keeps its own datum and the neighbour's is lost.

::: caveat Where the search is charged
The search charge is taken in the tree where the structural change happens, not necessarily in the tree before the operation. For the classical trees, which change the structure first and rebalance afterwards, this is the search path in the tree before the operation. An algorithm that rotates first could shorten the path, but each rotation changes a depth by at most one (`rotations_depth_reverse` below), so the rotations it pays for cover any shortcut. An insertion above an existing subtree pays the path to that subtree, not to the gap below it.
:::

@decl RotationBST.Dictionary.Execution RotationBST.Dictionary.Algorithm RotationBST.Dictionary.Algorithm.runFrom

An execution is a sequence of steps, with the costs and edits added up. An online dictionary algorithm sees the past operations, the current tree with its data and the current operation, and returns the new tree with its cost and edits. Its field `correct` certifies every answer by a `Step`, so an algorithm cannot under-report its cost.

**Theorem (basic properties).** An operation changes the number of keys as `resize` says, only valid operations have steps, and the data do not affect the main cost: forgetting them keeps every step and every execution. An online dictionary algorithm executes every valid sequence.

@decl RotationBST.Dictionary.Results.step_size RotationBST.Dictionary.Results.step_valid RotationBST.Dictionary.Results.step_unit RotationBST.Dictionary.Results.execution_unit RotationBST.Dictionary.Results.algorithm_execution

## Searches and rotations

**Theorem (depth and rotations).** If $k$ rotations turn $s$ into $t$, then every rank's depth in $s$ is at most its depth in $t$ plus $k$.

@decl RotationBST.Dictionary.Results.rotations_depth_reverse

This is the fact behind the headline result. In the rotation model, an access to $x$ ends with $x$ at the root, at depth $0$, so its depth before the access is at most the number of its rotations.

**Theorem (the two embeddings).** The rotation model embeds, at main cost at most $m + 2R$, and searching without moving costs the static cost.

@decl RotationBST.Dictionary.Results.of_execution RotationBST.Dictionary.Results.static_execution

## Splay updates as an instance

The splay tree updates of [Section 23.3](beyond.html#updates) have their own model: a forest of trees, with split and join, and a charge of one unit plus the rotations for every operation. That model stays as it is. These theorems relate it to the dictionary model:

**Theorem (splay updates are dictionary steps).** A splay access, insertion or deletion is a dictionary step on the same trees, without data, whose main cost is at most $2$, $3$ and $2$ times splay's own charge.

@decl RotationBST.Splay.Updates.Results.dictionary_access RotationBST.Splay.Updates.Results.dictionary_insert RotationBST.Splay.Updates.Results.dictionary_delete

The factors come from the search charge: splaying a key rotates once per edge of its search path, so the path is paid for by the rotations. These theorems are about single operations. The amortized bound of [Section 23.3](beyond.html#updates) is stated in splay's own forest model, and is not restated in the dictionary model.

The model deliberately stops short of a pointer machine with node allocation. That would be more faithful to an implementation. But the results of [Part III](part-classical.html) are statements about depths, rotations and balance data, and the rank view states them directly.
