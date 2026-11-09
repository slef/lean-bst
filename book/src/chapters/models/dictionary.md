# Insertions and deletions

Every model so far serves accesses to a fixed set of keys. The classical search trees of [Part III](part-classical.html) are dictionaries. Their main results concern insertions and deletions, and the rebalancing that follows each one. This chapter is the place for a model of such operations. The library has one today, but only for splay trees. The general model below is not formalized yet.

## What exists: updates for splay trees

[Section 23.3](beyond.html#updates) defines insertion, deletion, split and join for splay trees, and an execution model for sequences of them on a forest. That model already makes the choices that the general one should keep:

- **Ranks.** Trees are shapes whose keys are their inorder ranks, as in [Chapter 1](shapes.html#implicit-keys). An insertion names the gap $k \in \{0, \dots, n\}$ where the new key goes; every rank from $k$ on then grows by one. A deletion names a rank; every later rank then drops by one.
- **Cost.** Each operation is charged one unit plus its rotations.
- **No search.** The rank is supplied by the caller. The search that finds it from a comparison key is not modelled separately.

For splay trees the search is free in this accounting, because splaying a key rotates once per edge of its search path. For a balanced tree it is not: a search walks down the tree and rotates nothing.

## The general model

::: todo
A dictionary model shared by all the trees of [Part III](part-classical.html), with the splay update model as one instance. Target statements are in the roadmap, [entry 6](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#6-a-dictionary-model).
:::

The intended model keeps the rank view of the splay model and changes two things.

- **Searches are charged.** An operation on rank $x$, or on gap $k$, pays one unit for each node of its search path, plus one unit per rotation. A search that changes nothing then costs $1 + \mathrm{depth}(x)$, exactly the static cost [[StaticTree.cost]] of [Chapter 13](bounds.html#comparison-with-a-fixed-tree), and exactly what the pointer machine of [Chapter 7](pointer.html) charges for walking down.
- **Nodes carry balance data.** Rank-balanced trees store an integer rank, red-black trees a colour, weight-balanced trees a subtree size. The labelled trees of [Chapter 4](keys.html) already attach data to nodes. Changing a node's data (a promotion, a demotion, a recolouring) is counted separately from rotations, because the classical results bound the two separately.

A dictionary algorithm is then a function that takes a tree with its node data and one operation, and returns the new tree, its data and the cost. An execution is a sequence of operations, as in the splay model. The splay update model becomes an instance, with no node data, once a theorem relates the two accountings: in a splay, the search is part of the rotations.

The model deliberately stops short of a pointer machine with node allocation. It would be more faithful to an implementation. But the results of [Part III](part-classical.html) are statements about depths, rotations and balance data, and the rank view states them directly.
