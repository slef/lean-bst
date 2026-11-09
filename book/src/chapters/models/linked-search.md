# Linked searches

Theorem 9 of Bose, Douïeb, Iacono and Langerman [-@bose2016] is not about a single BST. It describes a static search structure made of many small trees. For every key $p$ there is a tree holding the keys that most often follow $p$ in the request sequence, and every node of every tree stores a pointer to the tree of its own key. A search for $x$ starts in the tree of the previous request; if $x$ is found there, the search follows the stored pointer to the tree of $x$, ready for the next request. If $x$ is not found, the search falls back to one shared tree that contains every key. Nothing is ever rotated, and the structure is built once, before the requests, from their transition frequencies.

To state such a theorem, one needs a model of computation in which these searches, and the memory they use, are counted honestly. This chapter defines that model: a *linked search* in a store of labelled trees, with an explicit cost per visited node and per followed link, and an explicit count of memory words. It is used only by the multiple-tree structure of [Chapter 30](multiple-trees.html). A reader who wants to check that chapter's theorem should read this chapter, since its statement is phrased with [[LinkedSearch.Execution]] and [[LinkedSearch.Store.words]]; nothing else in the book depends on it.

The model has two layers. The first is ordinary comparison search in a single tree whose nodes carry arbitrary, sparse keys, not inorder ranks. The second adds the links: each node carries a successor pointer, a *store* holds many trees, and a request is a search followed by a link. The definitions are in `Models/Labelled/Search/Definitions/Abstract.lean` and `Models/LinkedSearch/Definitions/Abstract.lean`, the theorems in the `Abstract.lean` files next to them.

## Searching a labelled tree

Most of the library works with unlabelled shapes and inorder ranks ([Chapter 1](shapes.html)). A small tree of the multiple-tree structure, however, contains only some of the keys, so its nodes must carry their keys. It is a [[LabelledTree]] over the natural numbers.

@decl RotationBST.Tree.labelWith

`t.labelWith keys` writes the list `keys` into the shape `t` in inorder. The root receives the entry at position `l.size`, the left subtree the first `l.size` entries, and the right subtree the rest. The construction is meant for a list with exactly one key per node. On a list of the wrong length it is still defined, with `take`, `drop` and the default label $0$, but the theorems below never use that case.

**Theorem (labelling).** If `keys` has one entry per node of `t`, then `t.labelWith keys` has shape `t` and inorder sequence `keys`. If moreover `keys` is strictly increasing, the labelled tree is a search tree ([[LabelledTree.Ordered]], [Chapter 4](keys.html)).

@decl RotationBST.LabelledTree.Search.Results.labelling RotationBST.LabelledTree.Search.Results.ordered

Search in such a tree is the textbook comparison search. The library gives it twice: as an executable function, and as a relation that says which searches are legal.

@decl RotationBST.LabelledTree.lookup

`lookup t x` returns whether `x` was found, and the number of nodes visited. At each node it compares `x` with the key and either stops or continues into one child. A failed search visits every node on its path, and searching an empty tree visits none.

@decl RotationBST.LabelledTree.Search

`Search t x found cost` is the model. A legal search compares at the current node and then follows *only* the child selected by the comparison: left if `x` is smaller, right if it is larger, and it stops with `true` if they are equal. Each visited node costs one unit. Reaching an empty child ends the search with `false` at no extra cost: the comparison at the parent has already been paid, and finding that the child pointer is null is part of it. The relation does not otherwise say how the search is carried out, so it is the reference against which the executable function is checked.

**Theorem (lookup is a legal search).** For every labelled tree and key, `lookup` performs a legal search, with exactly the result and the cost that it reports.

@decl RotationBST.LabelledTree.Search.Results.execution

**Theorem (membership).** In a search tree, `lookup` finds `x` exactly when `x` is one of its keys.

@decl RotationBST.LabelledTree.Search.Results.membership

Two cost statements connect the labelled search to the depth [[Tree.depth]] of [Chapter 1](shapes.html#depth), which is measured in edges and indexed by inorder rank.

**Theorem (cost of a hit).** Label a shape `t` with a strictly increasing list `keys` of the right length. Searching for the key at inorder position `i` visits exactly $\mathrm{depth}_t(i) + 1$ nodes.

@decl RotationBST.LabelledTree.Search.Results.hit_cost

This is the same "one plus the depth" that [[StaticTree.cost]] charges in [Chapter 12](bounds.html#comparison-with-a-fixed-tree), so a static labelled tree is charged as in the rest of the library.

**Theorem (uniform cost).** If every node of a labelled tree has depth at most $D$, then every search, successful or not, visits at most $D + 1$ nodes.

@decl RotationBST.LabelledTree.Search.Results.uniform_cost

The hypothesis is about the depths of the shape (`t.erase`), indexed by rank; it does not need the tree to be ordered. Failed searches matter here, because in the multiple-tree structure a request that is not in the local tree first fails there and only then falls back. A failed search ends below a node of depth at most $D$, so it too visits at most $D + 1$ nodes. $D$ is a real number so that it can be a logarithm.

## Stores and their memory

A linked search runs in a store of trees whose nodes carry a successor pointer.

@decl RotationBST.LinkedSearch.Entry

A node entry has a comparison `key` and a stored pointer `next` of type `ι`. The two child pointers are not part of the entry: they are the children of the surrounding [[LabelledTree]] node. The type `ι` is the type of root-cell addresses, introduced next.

@decl RotationBST.LinkedSearch.Store

A store has a finite table of *root cells*, indexed by `ι`, each holding the root of one local tree, and one more cell holding the root of a shared `fallback` tree. An address `p : ι` is a memory location, not a key: the store is never searched for `p`, it is entered at the cell `p`. The function `roots` describes the contents of the table. As the docstring warns, Lean's evaluation of that function is not part of the model and not charged; reading a cell is part of following a link, which is charged in requests below.

Memory is counted in two units.

@decl RotationBST.LinkedSearch.Store.nodes RotationBST.LinkedSearch.Store.words

`nodes` is the number of tree nodes, summed over all local trees and the fallback. Each tree is counted in full, as if it were stored separately. Trees cannot share nodes in this accounting, so it never undercounts memory. `words` charges four words per node (the key, the successor pointer and the two child pointers), one word per root cell and one for the fallback cell. The constant space of the running search, its current node and current root address, is not counted. The model treats keys and addresses as fitting in a word, as usual for a pointer machine.

## Installing the links

The multiple-tree structure first builds ordinary labelled trees and then stores a successor pointer in each node.

@decl RotationBST.LinkedSearch.attach

`attach target t` copies the labelled tree `t` and gives each node the pointer `target key`, computed from its own key. This happens once, during preprocessing. At query time, the pointer is a field of the node that has been reached; it is not computed from the requested key. In [Chapter 30](multiple-trees.html), `target` sends each key to the root cell of that key's own tree.

**Theorem (attaching links changes nothing else).** Attaching pointers preserves the shape. Searching the linked tree visits exactly the nodes that the plain search visits, and a hit returns the pointer `target x` of the found key.

@decl RotationBST.LinkedSearch.Results.shape RotationBST.LinkedSearch.Results.search

## Searching a linked tree

The search in a linked tree is the labelled search of the first section, returning the stored pointer instead of a boolean.

@decl RotationBST.LinkedSearch.lookup RotationBST.LinkedSearch.Search

`lookup` is the executable search and `Search` the legal one. The rules are those of [[LabelledTree.Search]]: compare, follow the selected child, one unit per visited node. A hit returns `some entry.next`, the found node's stored pointer, and a miss returns `none`. As before, the executable search is legal:

@decl RotationBST.LinkedSearch.Results.traversal

## Requests and executions

A request is served from the current root address, the address left by the previous request.

@decl RotationBST.LinkedSearch.Request

`Request s current x next cost` has two cases.

- **Hit.** The local tree at `roots current` contains `x`. The search visits $k$ nodes and finds the pointer `next`. Following that pointer costs one more unit, so the request costs $k + 1$.
- **Miss.** The local search visits $k$ nodes and fails. The search follows the fallback pointer, for one unit, searches the fallback tree, visiting $h$ nodes, finds `x` there, and follows its successor pointer, for another unit. The request costs $k + h + 2$.

In both cases the new current address is the pointer stored in the node where `x` was found. The failed local search is charged in full. A key that is missing from the fallback tree as well cannot be requested at all: no `Request` exists for it.

@decl RotationBST.LinkedSearch.request

`request` is the executable query rule, with the same costs. It returns `none` as the new address when even the fallback search fails.

**Theorem (a query is a legal request).** Whenever `request` returns an address, the corresponding legal request exists, with that address and with the cost that `request` computes.

@decl RotationBST.LinkedSearch.Results.query

@decl RotationBST.LinkedSearch.Execution

An execution serves a list of keys in order from an initial address `p`. Each request starts at the address returned by the previous one, and the costs add up. The initial address is an explicit parameter; in [Chapter 30](multiple-trees.html) it is the root cell of a given predecessor of the first request.

::: check
- **What a request costs.** One unit per visited node, in every tree searched, and one unit per followed pointer: the successor pointer always, the fallback pointer on a miss. Comparisons and child traversals at a node are included in its unit. Since a successful search visits at least one node, every request costs at least $2$.
- **What is not charged.** Building the store, including the choice of the trees and the computation of the pointers, happens before the requests and is not part of any cost. Lean's evaluation time of `roots` or of `lookup` is not modelled either.
- **Static model.** Nothing changes during an execution: the store is the same for every request, and only the current address moves. There are no rotations, and the library does not relate this model to the BST models of [Chapter 3](accesses.html) and [Chapter 6](pointer.html). It is a separate, explicitly specified pointer model, in which the multiple-tree bound is stated.
:::
