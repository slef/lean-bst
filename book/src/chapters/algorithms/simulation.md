# From points back to trees

An online geometric algorithm ([Chapter 8](geometry.html)) answers each request by naming a set of keys: the row of points it adds at the current time. It never says how a binary search tree would touch those keys, or what shape the tree would be in. [Chapter 9](equivalence.html) shows that, offline, a point set can always be turned back into a BST execution of comparable cost, but that conversion builds a treap ordered by the *next* time each key is touched ([Chapter 20](treaps.html)), which requires knowing the future.

Demaine, Harmon, Iacono, Kane and Pătraşcu (2009) showed that the future is not needed. Every online geometric algorithm can be simulated by an online BST algorithm whose cost is a constant times the number of points, plus a startup term. Their construction keeps the tree heap-ordered by the *last* time each key was touched. Keys touched at the same time are grouped into a "supernode", stored as a split tree ([Chapter 21](split-trees.html)) so that it can be broken apart cheaply when later rows touch some of its keys. Applied to GreedyASS ([Chapter 16](greedy.html)), this makes the geometric greedy algorithm an online BST algorithm, so its conjectured dynamic optimality is a statement about binary search trees.

The library formalizes this simulation as a single fixed algorithm, in the sense of [[RotationBST.Algorithm]], whose cost is linear in the geometric point count. Here is the theorem in its basic form.

```headline online-simulation
title: Every online geometric algorithm is an online BST algorithm
source: Demaine, Harmon, Iacono, Kane and Pătraşcu, *The geometry of binary search trees* (2009)
key: yes
theorems: Geometric.Simulation.Results.online_simulation

Fix an initial BST $T$ on $n$ keys and an online geometric algorithm $A$ on those keys: at each time, $A$ sees the request and the points added so far, and adds a row of points that contains the request and keeps the point set arborally satisfied. Then there is an online BST algorithm, chosen before any request is known, such that for every sequence $X$ of keys from $\{0,\dots,n-1\}$, serving $X$ from $T$ takes at most

$$6018\,P_A(X) + 6016\,n$$

rotations, where $P_A(X)$ is the number of points $A$ adds on $X$. In particular, GreedyASS ([Chapter 16](greedy.html)) is an online BST algorithm whose cost is linear in its number of points.

In Lean, $A$ is a [[Geometric.OnlineAlgorithm]], its point count is [[Geometric.rowCost]], and the BST algorithm is an [[RotationBST.Algorithm]], whose `cost` counts rotations.
```

This section states the four versions of the theorem and outlines the proof. The statements are in `Algorithms/Simulation/Abstract.lean`. They mention only the models: rotation executions, online algorithms, the geometric definitions and the pointer machine. Nothing about supernodes or split trees appears in them.

## The simulation theorem

Fix a key universe of size $n$ and an online geometric algorithm `A` ([[Geometric.OnlineAlgorithm]]). For a request sequence `xs`, [[Geometric.rowCost]]`A.step 0 ∅ xs` is the number of points `A` adds when it runs from an empty history at time $0$: the geometric cost of `A` on `xs`. The first theorem fixes the initial tree.

**Theorem (online simulation).** Let `tree` be a BST on $n$ keys and $A$ an online geometric algorithm on $n$ keys. There is a BST algorithm such that, for every sequence $X$ of keys less than $n$, it serves $X$ from `tree` with at most $6018\,P_A(X) + 6016\,n$ rotations, where $P_A(X)$ is `rowCost A.step 0 ∅ X`.

@decl RotationBST.Geometric.Simulation.Results.online_simulation

::: check
- **One algorithm for all sequences.** The existential `∃ algorithm` comes before `∀ xs`. The algorithm is chosen knowing `tree` and `A`, but not the requests. Since it is an [[RotationBST.Algorithm]], each step receives only the past requests, the current tree and the current request ([Chapter 5](online.html)). This is what makes the simulation online.
- **Rotations only.** `algorithm.cost` counts rotations ([[RotationBST.Algorithm.cost]]). Request charges are added in `normalized_simulation` below.
- **Geometric cost includes the requests.** Every legal row contains its request ([[Geometric.Completion]]), so `rowCost` is at least `xs.length`. A sequence of repeated requests for the current root costs one point per request and zero rotations.
- **The algorithm is not executable.** The proof chooses it with `Classical.choose` from existence statements, so `algorithm.step` is a mathematical function. Costs count rotations only, and the planning behind each step is not charged, as everywhere in the rotation model.
:::

The algorithm above is built for one initial tree. A single algorithm can serve every initial tree of the given size, at the price of a slightly larger startup term.

**Theorem (uniform simulation).** For every $n$ and every online geometric algorithm $A$ on $n$ keys, there is a BST algorithm such that, for every initial tree on $n$ keys and every sequence $X$ of keys less than $n$, it uses at most $6018\,P_A(X) + 6018\,n$ rotations.

This is the online equivalence of the geometric and BST models, stated in [Chapter 9](equivalence.html) as [[Geometric.Equivalence.Results.online_bst]], next to the offline equivalences. The proof fixes one reference shape. On the first request, the algorithm rotates whatever tree it is given into that shape, using at most $2n$ rotations ([[Geometry.reset]], [Chapter 3](accesses.html#any-shape-to-any-shape)), and from then on it behaves like the algorithm of `online_simulation` for the reference shape. The startup term grows from $6016n$ to $6018n$. The same reset wrapper, which works for any online algorithm, also turns Tango into an algorithm for every initial tree ([Chapter 19](tango.html)).

The conventional cost of a BST algorithm also charges one unit per request ([Chapter 5](online.html#two-cost-measures)). Since the geometric cost already pays one point per request, the conversion costs one more unit per point.

**Theorem (conventional cost).** Under the same hypotheses, there is a BST algorithm whose total cost, rotations plus one unit per request, is at most $6019\,P_A(X) + 6018\,n$ from every initial tree on $n$ keys.

@decl RotationBST.Geometric.Simulation.Results.normalized_simulation

Finally, the simulation also runs on the pointer machine of [Chapter 6](pointer.html). The causal transformer [[Pointer.Lazy.Online.run]] takes any rotation-model algorithm and runs it on the pointer machine, starting from [[Pointer.Lazy.Online.initial]], postponing rotations that the current request does not need. Applying it to the simulated algorithm gives a pointer strategy.

**Theorem (pointer simulation).** Under the same hypotheses, there is a BST algorithm whose pointer-machine run, from every initial tree on $n$ keys and on every sequence $X$ of keys less than $n$, is a legal pointer execution serving $X$, with at most $192593\,P_A(X) + 192576\,n$ pointer instructions.

@decl RotationBST.Geometric.Simulation.Results.pointer_simulation

The first conjunct says that the transformer's instructions form a pointer execution ([[Pointer.Execution]]) that serves `xs` from `tree`, ending at the transformer's current tree with the transformer's cost. The second bounds that cost. The constants are those of the transformer, [[Pointer.Lazy.Online.Results.simulation]]: pointer cost is at most $32R + 17m$, where $R$ is the algorithm's rotation count and $m$ the number of requests. With $R \le 6018\,P + 6018\,n$ and $m \le P$, where $P$ is the point count, this gives
$$32 \cdot 6018 = 192576 \text{ per key}, \qquad 192576 + 17 = 192593 \text{ per point}.$$

::: check
- The four occurrences of `Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs` are the same term: the final simulation state and its accumulated cost. `.1.current` is the tree actually present in the pointer machine, and `.2` is the cost.
- As in [Chapter 6](pointer.html), the final pointer tree need not equal the final tree of the rotation-model algorithm. The difference consists of postponed rotations that no request needed. They are not executed, and the bound does not have to pay for them.
:::

::: note The constants
None of the constants is meant to be sharp. They come out of a straightforward accounting. Creating a supernode costs, per key, the rotations that build it plus a stored credit large enough for every split it will ever undergo. Together these are at most $6016$ per key. Two more units per point pay for rotating the request to the root inside the extracted region and for undoing those rotations afterwards. The initial tree is treated as a single supernode containing all $n$ untouched keys, which accounts for the $6016\,n$.
:::

## GreedyASS as a binary search tree

The point of the theorem is that geometry can be used to design BST algorithms. GreedyASS adds, for each request, the minimal legal row ([[Geometric.GreedyASS.Results.greedy_minimum]]), and it is an online geometric algorithm ([[Geometric.greedyASS]]). Instantiating `A` with it in `normalized_simulation` gives an online BST algorithm whose total cost on every sequence is at most $6019$ times the number of points GreedyASS adds, plus $6018\,n$.

In the other direction, every BST execution with $r$ rotations on $m$ requests yields an arborally satisfied set of at most $2r + m$ points ([[Geometric.Equivalence.Results.rotations_to_ass]]). Together with the simulation, this means that GreedyASS is dynamically optimal as a BST algorithm, up to the additive term, if and only if its point count is within a constant factor of the minimum arborally satisfied superset of the requests. Whether this holds is the geometric form of the dynamic optimality conjecture for Greedy (Lucas, 1988; Munro, 2000; Demaine et al., 2009). It is open, and the library does not claim it.

::: caveat Not claimed
The library proves no upper bound on the number of points GreedyASS adds, beyond what follows from the definitions. Known results about Greedy, such as its access lemma and the working-set bound (Fox, 2011), are not formalized. The simulation transfers whatever bound one proves for a geometric algorithm, with a constant factor, but the bound itself must come from elsewhere.
:::

## Why the past suffices

The offline conversion of [Chapter 9](equivalence.html) keeps the tree as a treap ordered by next-touch times: the key that will be needed soonest is at the root. An online algorithm cannot know these priorities, but it knows the *last* touch of every key, `Geometric.lastTouch`. The simulation maintains the tree as a max-heap on last-touch times (`Geometric.HistoryHeap`), so that the most recently touched keys are near the root.

The first observation is that this is the right order for the next row. Suppose the new row touches a key $x$, and $y$ is a key that was touched more recently than every key strictly between $x$ and $y$. In a last-touch heap, such a $y$ is an ancestor of $x$. Then the rectangle spanned by the new point $(x, t)$ and the last touch of $y$ contains no other old point. Looking at the row's touched key closest to $y$ in that rectangle shows that arboral satisfaction forces the row to touch $y$ itself. Hence the keys of a legal row form a connected region containing the root, apart from one complication.

That complication is ties. All keys touched in the same row share their last-touch time, and a heap says nothing about their arrangement among themselves. The geometric argument above applies only to strictly more recent keys, so a new row may touch some keys of an old row and not others. The simulation therefore treats each maximal group of keys with the same last-touch time, within the interval delimited by more recent keys, as one *supernode*. The tree is a heap of supernodes, each supernode is a BST on its keys, and the gaps between a supernode's keys hold the recursively represented subtrees of less recently touched keys.

## How the simulation works

Serving a request has four phases. Each is a rotation sequence on the actual tree, and the proof tracks a state consisting of the geometric history, the nested supernode structure, and a *canonical* tree for that structure.

1. **Ask the geometric algorithm.** The algorithm computes `A.step time x P` from the history `P` and the request `x`. This is the row that the BST must touch, and only the past is consulted.
2. **Extract the row.** Starting from the root supernode, the simulation splits each supernode that the row touches so that the touched keys rise to the top and the untouched parts remain as intact subtrees. It recurses into the gaps the row reaches. The touched keys of a supernode are carved out by splits whose cost is logarithmic in the smaller side ([[SplitTree.Results.nearer_endpoint]]). After extraction, the touched keys form a rooted region whose fringe consists of untouched subtrees, the same picture as the rooted regions of [Chapter 7](regions.html).
3. **Access.** The request belongs to the row, so it lies in this region, which has one node per row point. Rotating it to the root inside the region takes fewer rotations than the region has nodes, and completes the [[RotationBST.Access]] that the algorithm must perform.
4. **Rebuild, later.** The touched keys now share the latest touch time, so in the canonical tree they form one new supernode at the top, stored as a fresh split tree ([[SplitTree.Results.finger_construction]]). Reaching that canonical tree from the accessed one means undoing the access rotations and then rebuilding. These rotations are not needed to serve the current request, so they are recorded as a *debt*, and the next request starts by performing them.

The amortization uses two kinds of stored potential. The *debt* is the number of rotations separating the actual tree from the canonical one. The *credit* of a supernode with $s$ keys is a constant times its number of multiway nodes, plus $3000\,(2s - \lfloor\log_2(s+1)\rfloor)$. The second term is the reserve from the proof of [[SplitTree.Results.linear_accounting]], scaled by a constant number of rotations per unit of split charge. Splits draw on the credit of the supernode being split. Creating a supernode deposits its whole lifetime credit at once, and that deposit is paid by the keys of the new row, one row point each. This is how the constant $6016$ per point, and $6016$ per key for the initial supernode, arises.

The online algorithm itself is a replay. Given the past requests, the algorithm recomputes the simulation state that the past has produced, checks that the tree it is handed is the tree that state predicts, and performs the next certified step. If the tree differs, which never happens along a run from the intended initial tree, it falls back to [[RotationBST.moveToRoot]], so that the [[RotationBST.Algorithm]] interface is satisfied on every input. Because each step consults only the history and the current request, the algorithm is fixed before the request sequence, which is what the order of the quantifiers in the theorems states.

::: details Where the pieces are
The proof is about seventy modules under `Algorithms/Simulation` and uses the internal two-ended split trees of `Structures/SplitTree`. The geometric lemma about rows touching their more recent boundary keys is in `Algorithms/Simulation/LastTouch`. Extraction, rebuilding and supernode creation are in `Algorithms/Simulation/Supernode/{Extraction,Rebuild,Create}`, and the policy and its bounds are in `Supernode/Policy`. None of these modules is part of the reading interface. The four theorems above are the only statements a reader has to trust, and their statements reach only the model definitions listed under each of them.
:::
