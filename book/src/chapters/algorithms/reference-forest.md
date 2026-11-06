# The reference forest

The analysis of GreedyASS in [Chapter 23](greedy-finger.html) compares it with a lazy finger moving in a fixed *reference tree*. That comparison has to be made one request at a time. It is made against a snapshot of the reference tree: after a search for the leaf $x$, delete the path from the root down to $x$. What is left is a forest of subtrees hanging off that path, together with $x$ itself as a one-leaf tree. Iacono and Langerman measure every GreedyASS item against the component of this forest that contains it. When the next search goes from $x$ to $y$, the forest changes by a sequence of local *merges* and *splits* along the path from $x$ to $y$, one per reference edge on that path. This is where the lazy-finger cost enters the analysis.

This section builds the reference tree, the forest, the distances that the potential of [Chapter 25](greedy-potential.html) is made of, and the merges and splits between consecutive forests. It ends with the conversion from an ordinary BST to a reference tree, which is how [Chapter 23](greedy-finger.html) turns the leaf-oriented Theorem 3.1 into the bound against ordinary lazy-finger trees. Nothing here mentions GreedyASS, except [Section 24.5](#components-that-persist), which shows that a persistent component acts as a barrier for the sweep.

::: note Do you need this section?
To check the headline results of [Chapter 23](greedy-finger.html), you do not: their statements use only ordinary trees and the lazy-finger and weighted-finger costs of [Chapter 14](lazy-finger.html). To check the statement of Theorem 3.1 ([Chapter 26](greedy-amortized.html)), you need only [[Reference.leaves]] from [Section 24.1](#leaf-oriented-trees) and [[Transitions.edges]] from [Section 24.4](#from-one-forest-to-the-next). The conversion of [Section 24.6](#from-an-ordinary-bst-to-a-reference-tree) is how the ordinary bounds follow from it. Everything else is proof machinery for [Chapter 25](greedy-potential.html) and [Chapter 26](greedy-amortized.html), to be read when following the potential argument.
:::

The definitions are in `Algorithms/GreedyASS/Reference/Definitions/Abstract.lean` and in the `Definitions/Abstract.lean` files of its submodules `Distance`, `Transitions` and `Conversion`; the theorems are in the corresponding `Abstract.lean` files.

## Leaf-oriented trees

The library's [[RotationBST.Tree]] is a bare shape whose *internal* nodes carry the keys, in inorder ([Chapter 1](shapes.html)). The paper's reference tree is *leaf-oriented*: the keys sit at the leaves, in left-to-right order, and internal nodes only route searches. The library reuses the same type and reads it differently: `Tree.nil` is a leaf, and `node l r` is an internal node whose leaves are those of `l` followed by those of `r`.

@decl Geometric.GreedyASS.Reference.leaves

`leaves t` is the number of leaves. Under this reading a tree with $k$ internal nodes has $k + 1$ leaves, so `Tree.nil` is a one-key tree rather than the empty tree. Leaves are numbered by rank. Every function of this section takes an offset `lo`, the rank of the tree's first leaf, so that a subtree can be addressed inside a larger tree: the leaves of `node l r` at offset `lo` are those of `l` at offset `lo` and those of `r` at offset `lo + leaves l`.

The analysis works with subtrees of the reference tree, and different subtrees may have the same shape. So a subtree is identified by its shape *and* its position:

@decl Geometric.GreedyASS.Reference.Component Geometric.GreedyASS.Reference.Component.last Geometric.GreedyASS.Reference.Component.Contains

A `Component` is a pair: the rank `first` of its first leaf and its `shape`. It covers the half-open interval of leaves $[\mathit{first}, \mathit{last})$, where `last = first + leaves shape`, and `Contains c key` says that the leaf `key` lies in that interval. Two components with the same shape at different offsets are different. A `Component` is only a pair of data: nothing in the type says that it occurs in a given reference tree. That fact is the predicate [[Distance.Occurs]] below, and the theorems state it where it is needed.

@decl Geometric.GreedyASS.Reference.instDecidableContains

Containment is two comparisons, so it is decidable.

## The forest of a search

@decl Geometric.GreedyASS.Reference.forest

`forest t lo searched` walks from the root towards the leaf `searched`. At each internal node it keeps the child that the search does not enter as a whole component, and recurses into the other one. At the leaf it keeps the singleton `⟨searched, nil⟩`. The proper ancestors of the searched leaf, the internal nodes on the search path, are exactly what is removed. The children that branch off to the left come before the recursive part and those that branch off to the right after it, so the list is in increasing leaf order. The forest has $d + 1$ components, where $d$ is the depth of the searched leaf: one per edge of the search path, plus the singleton.

For example, take the reference tree $t = \mathrm{node}(L, R)$ with $L = \mathrm{node}(\mathrm{nil}, \mathrm{nil})$ and $R = \mathrm{node}(\mathrm{nil}, \mathrm{node}(\mathrm{nil}, \mathrm{nil}))$. Its leaves are $0, \dots, 4$, with $L$ holding $0, 1$ and $R$ holding $2, 3, 4$. The search for leaf $3$ goes right, right, left, and

$$\mathtt{forest}\ t\ 0\ 3 = [\langle 0, L\rangle,\ \langle 2, \mathrm{nil}\rangle,\ \langle 3, \mathrm{nil}\rangle,\ \langle 4, \mathrm{nil}\rangle].$$

The search for leaf $4$ removes the same three internal nodes and gives the *same* forest. Only the searched singleton differs, $\langle 4, \mathrm{nil}\rangle$ instead of $\langle 3, \mathrm{nil}\rangle$. This is why several theorems below exclude the searched singleton by an explicit hypothesis.

The function is total. A rank beyond the last leaf is treated like a search for the last leaf, and a rank below `lo` like a search for the first. The theorems that concern the searched leaf require a valid rank.

**Theorem (layout).** A tree has one more leaf than internal nodes. The components of every forest are listed left to right with disjoint intervals, and each is a nonempty interval inside the tree's range.

@decl Geometric.GreedyASS.Reference.Results.layout

The first conjunct, `leaves t = t.size + 1`, is the dictionary between the two readings of a tree: [[RotationBST.Tree.size]] counts internal nodes. The second says that each component ends before the next one starts, and the third that $\mathit{lo} \le \mathit{first} < \mathit{last} \le \mathit{lo} + \mathtt{leaves}\ t$. These hold even for an invalid `searched`.

**Theorem (partition).** Every leaf of the tree lies in exactly one component of the forest.

@decl Geometric.GreedyASS.Reference.Results.partition

**Theorem (the searched singleton).** After a search for a valid leaf $x$, the singleton $\langle x, \mathrm{nil}\rangle$ belongs to the forest and is the only component that contains $x$.

@decl Geometric.GreedyASS.Reference.Results.searched

## Distances in the reference tree

The potential of [Chapter 25](greedy-potential.html) assigns each GreedyASS item a value built from the length of a path in the reference tree: from the item's leaf up to the root of its forest component, or up to the lowest common ancestor of two other leaves. This section defines those lengths and proves the comparisons the potential needs.

@decl Geometric.GreedyASS.Reference.Distance.depth Geometric.GreedyASS.Reference.Distance.lcaDepth Geometric.GreedyASS.Reference.Distance.lca

`depth t lo x` is the edge depth of the leaf $x$: the number of internal nodes above it. `lcaDepth t lo a b` is the edge depth of the lowest common ancestor of the leaves $a$ and $b$, and `lca t lo a b` is that ancestor's subtree, as a [[Reference.Component]]. All three descend together while both leaves are on the same side, and stop at the first node that separates them. For $a = b$ the lowest common ancestor is the leaf itself.

Positions in the tree are described by an inductive predicate:

@decl Geometric.GreedyASS.Reference.Distance.Occurs

`Occurs t lo c k` says that the component `c` is the subtree of `t` (at offset `lo`) rooted at depth `k`. The root occurs at depth $0$, and the occurrences of each child, shifted to its offset, occur one level deeper. This is what makes a component an *actual* subtree of the reference tree, rather than a pair of a shape and an offset.

The two lengths used by the potential count nodes, not edges:

@decl Geometric.GreedyASS.Reference.Distance.toLCA Geometric.GreedyASS.Reference.Distance.toRoot

- `toLCA t lo x a b = depth x - lcaDepth a b + 1` is, when $a \le x \le b$, the number of nodes on the path from the leaf $x$ up to the lowest common ancestor of $a$ and $b$, both ends included. The hypothesis $a \le x \le b$ ensures that this ancestor is an ancestor of $x$. Outside it the formula is a totalized natural-number subtraction.
- `toRoot c x = depth c.shape c.first x + 1` is the number of nodes on the path from the leaf $x$ up to the root of the component `c`, both ends included. For a singleton it is $1$.

**Theorem (lowest common ancestor).** For valid leaves $a$ and $b$, the subtree `lca a b` occurs at depth `lcaDepth a b` and contains both leaves, and every subtree that contains both occurs at that depth or above.

@decl Geometric.GreedyASS.Reference.Distance.Results.lowest_common_ancestor

**Theorem (path).** If $a \le x \le b$ are valid leaves, then `toLCA x a b` is the node count from $x$ to the root of the subtree `lca a b`.

@decl Geometric.GreedyASS.Reference.Distance.Results.path

So the arithmetic formula of `toLCA` measures what it should. The next two theorems say that widening the interval $[a, b]$ moves its lowest common ancestor up, and so lengthens the path. The first is the paper's Fact 3.1, the second is its general form.

**Theorem (Fact 3.1).** For leaves $w \le x \le y \le z$, the distance from $x$ to the lowest common ancestor of $w$ and $y$ is at most that to the lowest common ancestor of $w$ and $z$, and the distance from $y$ to the lowest common ancestor of $x$ and $z$ is at most that to the lowest common ancestor of $w$ and $z$.

@decl Geometric.GreedyASS.Reference.Distance.Results.ordered

**Theorem (enclosing intervals).** If $[b, c] \subseteq [a, d]$, then `toLCA x b c ≤ toLCA x a d` for every $x$.

@decl Geometric.GreedyASS.Reference.Distance.Results.interval

Neither statement needs valid ranks: the inequalities hold for the totalized formula. They are meaningful as path lengths only for valid leaves with $x$ between the endpoints.

Distances can be computed inside any subtree that contains the leaves in question:

**Theorem (subtrees).** If the component $c$ occurs at depth $k$ and contains $x$, $a$ and $b$, then the depth of $x$ is $k$ plus its depth in $c$, and `toLCA x a b` is the same whether computed in the whole tree or in $c$.

@decl Geometric.GreedyASS.Reference.Distance.Results.subtree

**Theorem (forest components occur).** Every component of a search forest is an actual subtree of the reference tree.

@decl Geometric.GreedyASS.Reference.Distance.Results.forest

The next theorem is the bridge between the two kinds of distance, and the reason why they are compared at all. Take a forest component $c$ that contains $x$, and leaves $a \le x \le b$. Going up from $x$, the path reaches the lowest common ancestor of $a$ and $b$ no later than the root of $c$ exactly when that ancestor is inside $c$, that is, exactly when $c$ contains $a$ and $b$.

**Theorem (component comparison).** Let $c$ be a component of the forest of some search and let $x \in c$. For valid leaves $a \le x \le b$, `toLCA x a b ≤ toRoot c x` holds if and only if $c$ contains both $a$ and $b$, and the strict reverse inequality holds if and only if $c$ misses one of them.

@decl Geometric.GreedyASS.Reference.Distance.Results.component

In [Chapter 25](greedy-potential.html), $a$ and $b$ are the neighbors of an item in the geometric point set, and this comparison decides which of its candidate values is selected. The docstring calls it "the distance comparison underlying Fact 3.2": the color assignments themselves are proved there.

**Theorem (one level up).** The root of `node l r` is one node farther from each leaf than the root of the child containing it.

@decl Geometric.GreedyASS.Reference.Distance.Results.merge

## From one forest to the next

When the search moves from leaf $x$ to leaf $y$, the forest of $x$ must become the forest of $y$. Below the lowest common ancestor of $x$ and $y$, the path to $x$ has to be put back and the path to $y$ removed. The library describes this as a sequence of elementary *events*, each of which merges two sibling components into their parent or splits a parent into its two children.

@decl Geometric.GreedyASS.Reference.Transitions.Event Geometric.GreedyASS.Reference.Transitions.Event.inverse Geometric.GreedyASS.Reference.Transitions.Event.parent

An event `split first left right` replaces the component $\langle \mathit{first}, \mathrm{node}(\mathit{left}, \mathit{right})\rangle$ by its two children, and `merge first left right` does the opposite. `parent` is the larger of the two sides, and `inverse` swaps splits and merges.

@decl Geometric.GreedyASS.Reference.Transitions.Event.introduced Geometric.GreedyASS.Reference.Transitions.Event.isMerge Geometric.GreedyASS.Reference.Transitions.merges Geometric.GreedyASS.Reference.Transitions.introductions

Two counts serve the potential argument of [Chapter 26](greedy-amortized.html). A split creates two new roots and a merge one: this is `introduced`, and `introductions` sums it along a list of events. `merges` counts the merges. New roots matter because a newly created *virgin* component carries a fixed credit ([Chapter 25](greedy-potential.html)). Merges matter because a merge may raise the potential of the items in the merged component.

The events act on lists of components:

@decl Geometric.GreedyASS.Reference.Transitions.Step Geometric.GreedyASS.Reference.Transitions.Trace

`Step roots event next` says that `next` is `roots` with one parent replaced by its two adjacent children (a split), or two adjacent children replaced by their parent (a merge). The rest of the list, `before` and `after`, is untouched. `Trace` chains steps. A step checks only shapes and offsets. Two adjacent components $\langle 0, L\rangle$ and $\langle 2, \mathrm{nil}\rangle$ can always be merged into $\langle 0, \mathrm{node}(L, \mathrm{nil})\rangle$ as far as `Step` is concerned, even though this subtree does not exist in the example tree above. Membership in the reference tree is a separate condition:

@decl Geometric.GreedyASS.Reference.Transitions.Admissible Geometric.GreedyASS.Reference.Transitions.Cut

An event is `Admissible` when its parent occurs in the reference tree. A `Cut` is the general shape of a forest: a left-to-right list of actual subtrees of the reference tree whose intervals cover every leaf. Its three fields are `ordered`, `occurs` and `covers`. Every search forest is a cut, and so is every intermediate list during a transition.

The transition itself is computed by three functions:

@decl Geometric.GreedyASS.Reference.Transitions.descend Geometric.GreedyASS.Reference.Transitions.ascend Geometric.GreedyASS.Reference.Transitions.plan

`descend t lo searched` splits the root, then the child on the searched leaf's side, and so on down to the leaf: it turns the one-component list $[\langle \mathit{lo}, t\rangle]$ into the forest of `searched`. `ascend` is its reverse, made of merges. `plan t lo old new` descends through the common ancestors of `old` and `new`, which stay removed in both forests and need no change. At their lowest common ancestor $v$ it ascends from `old` up to $v$, merging $v$'s subtree back together, and then descends from $v$ to `new`. In the example tree, `plan t 0 3 0` has five events: three merges up to the root, then two splits down to leaf $0$.

@decl Geometric.GreedyASS.Reference.Transitions.edges

`edges t lo old new` is the number of edges on the path between two leaves: the sum of their depths below the lowest common ancestor. It is $0$ for a repeated search. This is the reference tree's lazy-finger distance, and the benchmark of Theorem 3.1 adds it up over consecutive requests ([[Amortized.referenceCost]], [Chapter 26](greedy-amortized.html)). The paper counts the nodes on the path instead, which is one more, even for a repeated search; the library charges that unit separately, as one per request.

**Theorem (descending and ascending).** Descending to a leaf is a trace from the whole tree to the leaf's forest, with as many events as the leaf's depth, all admissible. Ascending is the reverse trace, with the same length.

@decl Geometric.GreedyASS.Reference.Transitions.Results.descending Geometric.GreedyASS.Reference.Transitions.Results.ascending

**Theorem (transition).** For any two leaves `old` and `new`, the plan is a trace from the forest of `old` to the forest of `new`, its length is the number of reference edges between the two leaves, and every event in it is admissible.

@decl Geometric.GreedyASS.Reference.Transitions.Results.transition

This is the central fact of the section: one event per edge of the lazy finger's path. The same length in node counts:

**Theorem (path length).** For valid leaves $x$ and $y$, the plan's length plus $2$ is the sum of the node counts from $x$ and from $y$ up to their lowest common ancestor.

@decl Geometric.GreedyASS.Reference.Transitions.Results.path

**Theorem (repeated search).** A repeated search needs no events.

@decl Geometric.GreedyASS.Reference.Transitions.Results.repeated

The potential argument looks at the forest after every single event, not only at the two ends. The next theorems say that each intermediate list is again a partition of the leaves by actual subtrees.

**Theorem (preservation).** An admissible trace turns a cut into a cut.

**Theorem (intermediate cuts).** Split the plan from `old` to `new` anywhere into a completed part and a remaining part. There is a cut that the completed part reaches from the forest of `old`, and from which the remaining part reaches the forest of `new`.

**Theorem (ownership).** In a cut, every leaf lies in exactly one component.

@decl Geometric.GreedyASS.Reference.Transitions.Results.preservation Geometric.GreedyASS.Reference.Transitions.Results.intermediate Geometric.GreedyASS.Reference.Transitions.Results.ownership

Each event moves the root of a leaf's component by at most one level, which is what makes the change in potential per event bounded:

**Theorem (local distance).** Let a single step go from an ordered list `roots` to `next`, and let $a \in$ `roots` and $b \in$ `next` both contain the leaf $x$. After a split, $x$'s node count to its root is the same or one smaller. After a merge, it is the same or one larger.

@decl Geometric.GreedyASS.Reference.Transitions.Results.local_distance

**Theorem (distance along a trace).** Along an admissible trace starting from a cut, the node count from a valid leaf to the root of its component changes by at most the number of events.

@decl Geometric.GreedyASS.Reference.Transitions.Results.sequence_distance

Finally, the counts of new roots and merges:

**Theorem (new roots).** A single step introduces at most `event.introduced` components that were not there before. Along a trace, the components of the final list that were not in the initial list are at most `introductions events`.

@decl Geometric.GreedyASS.Reference.Transitions.Results.local_roots Geometric.GreedyASS.Reference.Transitions.Results.new_roots

**Theorem (budget).** For any list of events, root introductions plus merges equal exactly twice the number of events.

@decl Geometric.GreedyASS.Reference.Transitions.Results.birth_budget

A split contributes $2 + 0$ and a merge $1 + 1$. This identity is where the constant $24$ of Theorem 3.1 comes from: [Chapter 26](greedy-amortized.html) pays $12$ units for each new virgin root and at most $12$ units of item potential for each merge, so a transition with $e$ events costs at most $12 \cdot 2e = 24e$, and $e$ is the number of reference edges between consecutive searches.

## Components that persist

Suppose a component $c$ belongs to the forests of a whole stretch of consecutive searches. Then no search in the stretch lands inside $c$, except possibly at its own singleton leaf, because a search inside $c$ would remove $c$'s root. So the searches stay on one side of $c$. This section proves that, and then draws the geometric consequence for GreedyASS: a key accessed in $c$ blocks the sweep, so that no point of the stretch is added beyond it on the far side. [Chapter 25](greedy-potential.html) uses this to show that each GreedyASS row touches at most two *non-virgin* components, those that were already accessed while they were roots (the paper's Lemma 3.7).

**Theorem (one side).** If a component $c$ belongs to the forests of two valid searches $x$ and $y$, and is neither searched singleton, then $x$ and $y$ are both to its left or both to its right.

@decl Geometric.GreedyASS.Reference.Results.side

**Theorem (one side for a stream).** The same holds for a whole nonempty sequence of searches: if $c$ belongs to all their forests and is none of their singletons, then all the searches lie to the left of $c$, or all lie to its right.

@decl Geometric.GreedyASS.Reference.Results.stream

Without the singleton exclusion the statement would be false: in the example tree, the singleton $\langle 3, \mathrm{nil}\rangle$ belongs to the forests of both $3$ and $4$, but the search for $3$ is inside it. The weak form below covers this case, relative to a single key of the component:

**Theorem (weak side).** If $c$ belongs to the forests of all searches in a sequence and contains the leaf $k$, then all searches are $\le k$, or all are $\ge k$.

@decl Geometric.GreedyASS.Reference.Results.point_side

The geometric consequence uses the sweep [[Geometric.greedySweep]] of [Chapter 21](greedy.html) and the run [[Geometric.fill]] of [Chapter 8](geometry.html), which adds its rows one time step at a time. Suppose that at time `stamp` the point $(\mathit{accessed}, \mathit{stamp})$ was added, with $\mathit{accessed}$ in $c$, and that $c$ then persists. The searches stay on one side of $c$, say the left. Intuitively, the old point acts as a wall: a later point to its right would have to be visible from a request to its left, across the column of $\mathit{accessed}$, and the latest point of that column blocks every such rectangle.

**Theorem (access barrier).** Let $P$ be a point history with all times at most `stamp` and containing $(\mathit{accessed}, \mathit{stamp})$, and let $c$ contain `accessed`. Let `first :: xs` be a sequence of valid searches whose forests all contain $c$, none of them at $c$'s singleton. Then either all searches lie left of $c$ and every point that GreedyASS adds on `xs` after time `stamp` has key at most `accessed`, or all lie right of $c$ and every such point has key at least `accessed`.

@decl Geometric.GreedyASS.Reference.Results.access

In the intended use, `first` is the search of time `stamp`, whose row contained `accessed`, and `xs` are the following searches. The sweep runs on `xs` from the history `P`, starting at time `stamp + 1`. The hypothesis on $P$ is only [[Geometric.History]], so the theorem does not assume that $P$ was produced by GreedyASS, or even that it is arborally satisfied.

**Theorem (weak barrier).** The same with the weak sides of `point_side`: if all forests of `xs` contain $c$, then either all searches and all new points are at most `accessed`, or all are at least `accessed`. Searches of $c$'s singleton are allowed.

@decl Geometric.GreedyASS.Reference.Results.barrier

## From an ordinary BST to a reference tree

Theorem 3.1 is stated for leaf-oriented reference trees, while the lazy-finger cost of [Chapter 14](lazy-finger.html) is defined for ordinary BSTs, whose internal nodes carry the keys. The paper bridges the two with a simple conversion that keeps each key's position in the inorder and at most doubles depths.

@decl Geometric.GreedyASS.Reference.Conversion.convert

Each node of the ordinary tree, with key $k$, becomes a small gadget whose leaves are the leaves of the converted left subtree, then the leaf $k$, then the leaves of the converted right subtree:

- with two children, `node (convert l) (node nil (convert r))`: an internal node for the left part, and below it on the right a second internal node separating the leaf $k$ from the right part;
- with only one child, a single internal node separating $k$ from that child;
- with no children, the leaf $k$ alone.

Missing children are contracted rather than turned into leaves, so the converted tree has exactly one leaf per key, in inorder: leaf rank $x$ is key rank $x$. Descending from a node to its left child costs one reference edge, and to its right child two. The empty tree has no keys but is sent to `nil`, which has one leaf. This is a totalized value, and the theorems that need a key count assume a nonempty tree.

**Theorem (population).** A nonempty tree with $n$ keys converts to a reference tree with $n$ leaves.

@decl Geometric.GreedyASS.Reference.Conversion.Results.population

**Theorem (depth).** The leaf of key $x$ has edge depth at most $2\,d(x) + 2$ in the converted tree, where $d(x)$ is the depth of $x$ in the original tree, with the root at depth $0$.

@decl Geometric.GreedyASS.Reference.Conversion.Results.depth

**Theorem (distance).** For keys $x, y$ of $t$, the number of reference edges between their leaves is at most $2\,\delta_t(x, y) + 4$, where $\delta_t$ is the edge distance [[LazyFinger.distance]] in $t$.

@decl Geometric.GreedyASS.Reference.Conversion.Results.distance

Summing over a request sequence gives the comparison of the two benchmarks. Recall that the leaf-oriented benchmark [[Amortized.referenceCost]] charges one unit per request plus the reference edges between consecutive requests, with no initial traversal. The lazy-finger cost [[LazyFinger.costFrom]]` t p xs` charges one unit per request plus the distance in $t$ from the previous request, starting from the key $p$, and [[LazyFinger.cost]] starts at the root.

**Theorem (benchmark comparison).** For a BST $t$, a valid start key $p$ and valid requests $X$,

$$\mathtt{referenceCost}(\mathtt{convert}\ t, 0, X) \le 5\,\mathrm{LF}_t(p, X),$$

and the same holds for the root-start cost $\mathrm{LF}_t(X)$ when $t$ is nonempty.

@decl Geometric.GreedyASS.Reference.Conversion.Results.cost_from Geometric.GreedyASS.Reference.Conversion.Results.cost

Each request contributes $1 + e$ on the left, with $e \le 2\delta + 4$ reference edges, and $1 + \delta$ on the right, so the ratio is at most $5$. The first request contributes $1$ on the left and at least $1$ on the right. So the bound holds for *every* valid start key $p$: the leaf-oriented benchmark does not charge the walk to the first request at all.

::: check
- **Offsets.** The conversion statements use offset `0` for the reference cost and shift ranks by `lo` in `depth` and `distance`, so that the converted tree can be placed anywhere.
- **The empty tree.** `population` and `cost` assume `0 < t.size`. In `cost_from` the hypothesis `p < t.size` already forces the tree to be nonempty.
:::
