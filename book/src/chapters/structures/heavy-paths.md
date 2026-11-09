# One heavy path

The deamortization of [Chapter 37](deamortization.html) runs an arbitrary source BST algorithm inside a tree that it keeps balanced in a weighted sense: whatever shape the source tree takes, every key $i$ stays at depth $O(\log(W/w_i))$ in the tree that is actually stored, where $w_i$ is the key's weight and $W$ the total weight. This is Theorem 5 of Bose, Collette, Fagerberg and Langerman [-@bose2012], and its formal counterpart is [[Deamortization.Weighted.Results.simulation]]. The simulation stores the source tree through its *heavy-path decomposition*. Each heavy path is kept as a pair of pop-tarts, the weighted stacks of [Chapter 44](pop-tarts.html) and [Chapter 45](chocolate.html). The subtrees hanging off a path are stored inside the pop-tarts as weighted leaves, and they are represented in the same way, recursively.

This section is the first of four on that representation. It covers the decomposition itself and the representation of a *single* heavy path by a pair of pop-tarts, with its off-path subtrees treated as opaque payloads.

```headline heavy-paths-pair
title: A heavy path stored in two pop-tarts
source: @bose2012
theorems: HeavyPath.Results.path_exists HeavyPath.Results.light_bound HeavyPath.Paired.Results.extract_build HeavyPath.Paired.Results.located_key_bound

Let $t$ be a tree whose nodes carry weights, and let $W$ be its total weight. Each node has a *solid* edge to its heavier child (the left child on a tie); its other child edge is *light*.

1. If all weights are nonnegative, every node $x$ with $w(x) > 0$ is reached from the root along a path with at most $\log_2(W/w(x))$ light edges.
2. If all weights are positive and $t$ is nonempty, the solid path from the root ends at a leaf $x$. Let $\ell$ be its number of edges. Starting at the root, the pointer machine turns $t$ into a tree $p$ with $x$ at the root, a valid Chocolate pop-tart of the path's nodes smaller than $x$ as its left subtree, and a mirrored one of the larger nodes as its right subtree. Each path node enters its pop-tart together with its off-path subtree, as one leaf of weight equal to the node's weight plus the subtree's. The cost of the trace plus the potential of the two pop-tarts is at most $24\,\ell$, and $w(x) + M = W$, where $M$ is the total leaf weight of $p$. The rank at the root of $p$ is the rank of $x$ in $t$.
3. In every valid pair $p$ of leaf weight $M$, a key inside a leaf of weight $w > 0$ has depth at most

$$8 + 7\log_2(M/w) + d,$$

where $d$ is its depth inside the leaf's subtree.

Item 1 is `path_exists` with `light_bound`, item 2 is `extract_build` and item 3 is `located_key_bound`. Depths count edges, and ranks are inorder positions from $0$.
```

The headline is the step that the paper iterates. Item 3 bounds the depth of a key inside one off-path subtree by its depth in that subtree plus $O(\log(M/w))$. Applied once per heavy path along the way to a key, the logarithms telescope to $O(\log(W/w_i))$. That recursion is [Chapter 47](recursive-heavy-paths.html).

::: note Do you need this section?
Only to follow the proof of the deamortization. The intermediate simulation theorem [[Deamortization.Weighted.Results.simulation]] uses [[HeavyPath.mass]] and [[HeavyPath.Positive]] from this section, together with the policies of [Chapter 49](finger-histories.html). A reader who only wants to understand that statement needs the section on the decomposition below and can skip the rest. The definitions are in `Structures/HeavyPath/Definitions/Abstract.lean` and `Structures/HeavyPath/Paired/**/Definitions/Abstract.lean`, the theorems in the `Abstract.lean` files next to them.
:::

## The heavy-path decomposition

The source tree is a [[LabelledTree]], whose nodes carry labels of an arbitrary type `α` (in the deamortization, the labels are inorder ranks). A weight function `weight : α → ℝ` gives each label a weight. The library never stores weights in the tree, and introduces no new tree type. Positions in the tree are described with the labelled zippers of [Chapter 12](replay.html): a [[LabelledCursor.Frame]] is one ancestor, `.left x r` when the focus is the left child of the node labelled `x` with right subtree `r`, and `.right l x` symmetrically. A [[LabelledCursor.Config]] is a focus subtree with its list of frames, innermost first.

### Weights and mass

@decl RotationBST.HeavyPath.mass RotationBST.HeavyPath.Nonnegative RotationBST.HeavyPath.Positive

`mass weight t` is the total weight of the nodes of `t`. The paper writes $W$ for the mass of the whole tree. `Nonnegative` and `Positive` ask that every node of `t` have nonnegative, or positive, weight. Positivity is the standing hypothesis of the decomposition theorems below. The deamortization assumes it for the source tree, and with unit weights it holds trivially.

@decl RotationBST.HeavyPath.Results.mass_nonnegative RotationBST.HeavyPath.Results.mass_positive RotationBST.HeavyPath.Results.unit_positive RotationBST.HeavyPath.Results.unit_mass

Nonnegative weights give a nonnegative mass, and positive weights give a nonempty tree a positive mass. Unit weights are positive, and with unit weights the mass is the number of nodes, `t.erase.size`, where [[LabelledTree.erase]] forgets the labels.

### Solid and light edges

@decl RotationBST.HeavyPath.LeftHeavy

`LeftHeavy weight l r` says that the solid edge of a node with subtrees `l` and `r` goes left: the left subtree is at least as heavy as the right one. Ties go left, as in the paper. The relation compares masses, so with zero weights an empty child can be "heavy".

@decl RotationBST.HeavyPath.Results.right_light_half RotationBST.HeavyPath.Results.left_light_half

These two lemmas are the reason heavy paths work. If the solid edge goes left, the right subtree has at most half the mass of the node's whole subtree, and symmetrically. So each light edge halves the mass, at least.

@decl RotationBST.HeavyPath.Path

`Path weight t y lights depth` records one root-to-node path in `t`, ending at a node labelled `y`. `depth` counts its edges and `lights` counts its light edges. Each constructor takes one step down and records whether that step followed the solid edge (`leftSolid`, `rightSolid`) or not (`leftLight`, `rightLight`). The relation follows a particular occurrence of the label, so repeated labels cause no ambiguity.

@decl RotationBST.HeavyPath.Results.path_exists RotationBST.HeavyPath.Results.lights_le_depth RotationBST.HeavyPath.Results.path_mass RotationBST.HeavyPath.Results.light_bound RotationBST.HeavyPath.Results.unit_light_bound

**Theorem (light edges).** With nonnegative weights, if $y$ is reached by a path with $k$ light edges, then $2^k w(y) \le W$. Hence, if $w(y) > 0$, then $k \le \log_2(W/w(y))$. With unit weights, $k \le \log_2 n$.

Every label occurring in the tree has such a path (`path_exists`). `path_mass` is the halving argument iterated, and `light_bound` takes its logarithm. This is the paper's remark that "any path from the root to a node $x$ of weight $w$ uses at most $\log W/w$ dotted edges".

@decl RotationBST.HeavyPath.Results.path_context RotationBST.HeavyPath.Results.path_access

These connect a `Path` to the zippers and to the pointer machine. A path of depth $d$ to `y` gives a context `cs` of $d$ frames that plugs the subtree rooted at `y` back into `t`. `path_access` adds a [[Pointer.Trace]] of exactly $d$ instructions, the descent from the root of the erased tree to that node, together with the light-edge bound.

### The heavy path from the root

@decl RotationBST.HeavyPath.SolidContext

`SolidContext weight focus cs` says that every frame of `cs` follows the solid edge: going up from `focus`, each ancestor's other subtree is no heavier (for a `.left` frame) or strictly lighter (for a `.right` frame). These are exactly the `LeftHeavy` conventions, with the tie broken to the left.

@decl RotationBST.HeavyPath.frameMass RotationBST.HeavyPath.frameKey

A frame of a heavy path is the unit that goes into a pop-tart. `frameKey` is its separator, the ancestor's label. `frameMass` is its *charge*: the separator's weight plus the mass of its off-path subtree. This is the weight of the pop-tart leaf that will hold the frame. The charges of the frames along a path, plus the mass of the focus, add up to the mass of the whole tree, so each node's weight is charged exactly once.

@decl RotationBST.HeavyPath.lowerKeys RotationBST.HeavyPath.upperKeys

Along a heavy path from $y$ down to its endpoint $x$, the paper splits the nodes into $L(y,x)$, those smaller than $x$, and $R(y,x)$, those larger. A `.right l x` frame has its separator to the left of the focus, so it belongs to $L$. A `.left x r` frame belongs to $R$. `lowerKeys` and `upperKeys` list these separators in frame order, from the endpoint up.

@decl RotationBST.HeavyPath.extend RotationBST.HeavyPath.extract

`extract weight t` follows solid edges from the root of `t` and returns the endpoint as a cursor configuration: its focus is the endpoint's subtree and its context the frames of the path, innermost first. `extend` appends one more frame at the outer end, which is how the recursion builds the context. The walk stops when the heavy child is empty. With positive weights the heavy child of a node with a nonempty subtree is nonempty, so the endpoint is a leaf. With zero weights it can stop earlier, at a node whose only nonempty subtree has mass $0$, and that subtree is kept in the focus. `extract` is noncomputable only because it decides `LeftHeavy` on real numbers classically.

@decl RotationBST.HeavyPath.Results.extract_tree RotationBST.HeavyPath.Results.extract_nonempty RotationBST.HeavyPath.Results.extract_solid RotationBST.HeavyPath.Results.extract_mass RotationBST.HeavyPath.Results.extract_trace RotationBST.HeavyPath.Results.extract_order RotationBST.HeavyPath.Results.extract_positive RotationBST.HeavyPath.Results.extract_terminal RotationBST.HeavyPath.Results.extract_path

What `extract` returns, for any weights:

- `extract_tree`: plugging the focus back into the context gives `t`. Nothing is lost or reordered.
- `extract_nonempty`: a nonempty tree has a nonempty endpoint subtree.
- `extract_solid`: the context is solid.
- `extract_mass`: the mass of `t` is the mass of the focus plus the sum of the frame charges.
- `extract_trace`: the pointer machine walks from the root to the endpoint in exactly as many instructions as there are frames.
- `extract_order`: in an ordered tree, `lowerKeys` is decreasing, `upperKeys` is increasing, and every key of the focus lies strictly between the two lists. Reading from the endpoint up, the paper's $L$ grows downward and $R$ grows upward, which is why the two halves need stacks of opposite orientations.

And with positive weights:

- `extract_positive`: the focus is positive and every frame has a positive charge.
- `extract_terminal`: the endpoint is a leaf `.node .nil x .nil`.
- `extract_path`: that leaf is reached by a `Path` with no light edge, whose depth is the number of frames.

@decl RotationBST.HeavyPath.Results.decomposition

`decomposition` bundles the facts used later: the endpoint is a leaf $x$, the configuration is `t` itself, the context is solid, $W = w(x) + \sum$ charges, the path has no light edge, and the descent has an exact trace.

## A heavy path as a pair of stacks

Following the paper (its Figure 4), a heavy path ending at $x$ is stored with $x$ at the root, the separators of $L$ in a pop-tart as its left subtree, and those of $R$ in another pop-tart as its right subtree. Each separator brings its off-path subtree along, as one opaque leaf of the pop-tart:

```text
      source tree                      paired representation

          y1                                     x
         /  \                                /       \
       A1    y2                    pop-tart L         pop-tart R
            /  \                  A1 y1 A3 y3 .       . y2 A2
          y3    A2
         /  \
       A3    x
```

Here $A_1 < y_1 < A_3 < y_3 < x < y_2 < A_2$ in key order, so $L = \{y_1, y_3\}$ and $R = \{y_2\}$. Under each pop-tart its inorder is listed: the separators are its internal nodes, the $A_i$ are leaves holding whole subtrees, and `.` is the empty leaf next to $x$. The physical tree has the same inorder as the source; only the shape differs.

In the library this is *paired*: a [[HeavyPath.Paired.Stacks]] is the pair of Chocolate pop-tarts, and the path endpoint is the root between them.

### The pair

@decl RotationBST.HeavyPath.Paired.Stacks

`lower` stores $L$ and `upper` stores $R$, each as a Chocolate [[PopTart.Chocolate.Layer]]. A Chocolate pop-tart is efficient when its leaves are pushed in decreasing key order. Moving up from the endpoint, $L$ receives its separators in decreasing order, as required, but $R$ receives them in increasing order. So `upper` is kept in *reflected* coordinates, and it is mirrored when it is laid out physically.

@decl RotationBST.HeavyPath.Paired.Stacks.tree RotationBST.HeavyPath.Paired.Stacks.mass RotationBST.HeavyPath.Paired.Stacks.potential RotationBST.HeavyPath.Paired.Stacks.Valid RotationBST.HeavyPath.Paired.Stacks.empty

- `tree` is the physical tree: a root (the endpoint) with the decoded lower pop-tart on the left and the mirrored decoded upper pop-tart ([[Tree.mirror]]) on the right. Its leaves are the stored payload subtrees.
- `mass` is the total leaf weight of both pop-tarts. The endpoint's own weight is not included. Thus $w(x) + M = W$ in the headline.
- `potential` is the sum of the two Chocolate potentials, natural numbers.
- `Valid` asks both layers to be valid Chocolate pop-tarts at level $0$ ([[PopTart.Chocolate.Layer.Valid]]).
- `empty` is a path consisting of its endpoint only: both stacks hold just one empty leaf of weight $0$. That empty leaf stays at the bottom of each stack throughout. It is the endpoint's empty child, and it is why the fringes below always end with `(.nil, 0)`.

@decl RotationBST.HeavyPath.Paired.lowerSlots RotationBST.HeavyPath.Paired.upperSlots

The leaves a list of frames contributes: each `.right l x` frame gives the lower slot `(l.erase, mass l + w(x))`, and each `.left x r` frame gives the upper slot `(r.erase, w(x) + mass r)`. The weight of a slot is the frame's `frameMass`.

### Pushing the next ancestor

@decl RotationBST.HeavyPath.Paired.Stacks.push RotationBST.HeavyPath.Paired.Stacks.pushCost

`push weight frame p` extends the path by one more ancestor. The frame goes into the stack on its side, as one leaf: the erased off-path subtree (mirrored first for the upper stack, so that decoding restores it) with the frame's charge. Physically, the endpoint sits just below the new ancestor. One rotation lifts it over that ancestor; the cursor then enters the selected pop-tart, the pop-tart's push rebalances it, and the cursor comes back. `pushCost` counts this exactly: the Chocolate [[PopTart.Chocolate.Layer.pushCost]] plus three.

@decl RotationBST.HeavyPath.Paired.Stacks.build RotationBST.HeavyPath.Paired.Stacks.buildCost

`build` pushes a list of frames, innermost first, and `buildCost` adds up the push costs.

@decl RotationBST.HeavyPath.Paired.Results.empty_valid RotationBST.HeavyPath.Paired.Results.push_trace RotationBST.HeavyPath.Paired.Results.push_valid RotationBST.HeavyPath.Paired.Results.push_amortized RotationBST.HeavyPath.Paired.Results.push_mass RotationBST.HeavyPath.Paired.Results.push_lower_size

**Theorem (push).** Let $p$ be a valid pair, physically the child of the ancestor in `frame`, inside any further context `cs`. With the cursor at the root of $p$, there is a pointer trace of exactly `pushCost` instructions that ends with the cursor at the root of the pushed pair, inside `cs`. If the frame's charge is nonnegative, the result is valid, its mass grows by the charge, and

$$\texttt{pushCost} + \Phi(p') \le 23 + \Phi(p).$$

The empty pair is valid. Only nonnegative charges are needed, not positive ones. The trace in `push_trace` exists for every pair, valid or not, because it describes the physical rebalancing. `push_lower_size` tracks the rank of the endpoint: the lower pop-tart grows by `l.size + 1` for a `.right l x` frame and by nothing for a `.left` frame, which is the [[Pointer.offset]] of the frame. Since the endpoint's rank is the size of the lower pop-tart, the root of the pair always has the endpoint's source rank.

@decl RotationBST.HeavyPath.Paired.Results.build_trace RotationBST.HeavyPath.Paired.Results.build_valid RotationBST.HeavyPath.Paired.Results.build_amortized RotationBST.HeavyPath.Paired.Results.build_mass RotationBST.HeavyPath.Paired.Results.build_lower_size RotationBST.HeavyPath.Paired.Results.build_fringe RotationBST.HeavyPath.Paired.Results.empty_build_fringe

The same facts for `build`, by induction. Building $k$ frames costs at most $23k$ amortized. The fringe lemmas say exactly which leaves the two pop-tarts hold, in physical inorder. The lower fringe is `lowerSlots` reversed, outermost first, followed by the old fringe. The mirrored upper fringe is the old one followed by `upperSlots`, innermost first. From the empty pair, each fringe has the empty leaf on the endpoint's side. So the physical tree has the source inorder, payload by payload and separator by separator.

### From the source tree to the pair

**Theorem (pairing the heavy path from the root).** Let $t$ be a nonempty tree with positive weights, let $x$ be the endpoint of its heavy path from the root, and let $\ell$ be the path's number of edges. Build the pair $p$ from the path's frames, starting from `empty`. Then $p$ is valid and $w(x) + M(p) = W$. With the cursor at the root of $t$, a pointer trace of some cost $c$ turns $t$ into the tree of $p$ with the cursor back at the root, and $c + \Phi(p) \le 24\,\ell$. The root of $p$ holds the endpoint's rank.

@decl RotationBST.HeavyPath.Paired.Results.extract_build

The trace walks down the path, $\ell$ instructions, and then pushes the $\ell$ frames back up, at amortized cost $23$ each, from potential $0$. The last conjunct compares [[Pointer.Config.key?]] of the two configurations: the physical root is the rank of the source endpoint.

@decl RotationBST.HeavyPath.Paired.Results.extract_build_labelled

The labelled version, for an ordered labelled tree `t`. Some labelled tree `u`, with the shape of the pair, the same inorder labels as `t`, and still ordered, is reached from `t` by a sequence of labelled rotations ([[LabelledTree.Rotations]]). The rotation count is at most the trace cost. So the transformation is an ordinary sequence of BST rotations that carries each label with its node. The off-path subtrees are left untouched: each is erased and stored as is.

### Depth inside the pair

The pair inherits the weighted depth bound of the Chocolate pop-tart ([[PopTart.Chocolate.Results.weighted_depth]]). That bound places a leaf of weight $w$ at depth at most $7 + 7\log_2(M_s/w)$ in its stack $s$. The pair adds one edge for its root and uses the mass $M$ of both stacks, which is at least $M_s$.

@decl RotationBST.HeavyPath.Paired.Results.lower_depth RotationBST.HeavyPath.Paired.Results.upper_depth RotationBST.HeavyPath.Paired.Results.lower_access RotationBST.HeavyPath.Paired.Results.upper_access

A leaf occurrence ([[PopTart.WeightedTree.SlotAt]]) at depth $d$ in the lower pop-tart, or in the physically oriented upper one, with weight $w > 0$, satisfies $d + 1 \le 8 + 7\log_2(M/w)$. The `access` versions add the navigation: if the payload is nonempty, the cursor reaches its root from the root of the pair in exactly $d+1$ instructions, through a context that plugs it back into the pair.

@decl RotationBST.HeavyPath.Paired.Results.lower_key_depth RotationBST.HeavyPath.Paired.Results.upper_key_depth RotationBST.HeavyPath.Paired.Results.lower_key_bound RotationBST.HeavyPath.Paired.Results.upper_key_bound RotationBST.HeavyPath.Paired.Results.lower_separator_bound RotationBST.HeavyPath.Paired.Results.upper_separator_bound

The same, by key. A [[PopTart.WeightedTree.LocatedSlot]] also records the payload's inorder offset in its pop-tart. A key of rank `x` inside the payload then has rank `offset + x` in the pair, or `lower size + 1 + offset + x` on the upper side, past the endpoint. Its [[Tree.depth]] in the pair is exactly the slot's depth plus one plus its depth inside the payload (`*_key_depth`), hence at most $8 + 7\log_2(M/w)$ plus its depth inside the payload (`*_key_bound`). The separator that comes with the payload, just after it on the lower side and just before it on the upper side, is at depth at most $7 + 7\log_2(M/w)$.

@decl RotationBST.HeavyPath.Paired.Results.located_depth RotationBST.HeavyPath.Paired.Results.located_mass RotationBST.HeavyPath.Paired.Results.located_key_bound RotationBST.HeavyPath.Paired.Results.located_successor_bound RotationBST.HeavyPath.Paired.Results.located_predecessor_bound

**Theorem (depth in a pair).** View a valid pair as a single weighted tree: the endpoint at the root, the lower pop-tart on the left, and the physically oriented upper pop-tart on the right. Let a payload with charge $w > 0$ sit in it at depth $d$ and inorder offset $o$. Then:

- $d \le 8 + 7\log_2(M/w)$, and $0 \le w \le M$;
- a key of rank $o + k$, the $k$-th key of the payload, has depth at most $8 + 7\log_2(M/w)$ plus its depth in the payload;
- the keys just after and just before the payload, when they exist, have depth at most $7 + 7\log_2(M/w)$.

These are the forms used later. The recursion of [Chapter 47](recursive-heavy-paths.html) applies `located_key_bound` once per heavy path and telescopes. The successor and predecessor bounds let a search that ends between two payloads, or at a separator, be charged to the payload next to it.

## Substitution: payloads other than the source subtree

So far the off-path subtrees go into the pop-tarts unchanged. In the recursive representation, each of them is itself restructured before it is stored, and later sections even keep different physical layouts for equal source subtrees. *Substitution* generalizes the pair to an arbitrary physical payload function, while keeping the charges of the source.

@decl RotationBST.HeavyPath.Paired.framePayload RotationBST.HeavyPath.Paired.replaceFrame

`framePayload` is a frame's off-path source subtree. `replaceFrame payload frame` is the physical [[Pointer.Frame]] on the same side, with `payload` applied to that subtree.

@decl RotationBST.HeavyPath.Paired.Stacks.pushWith RotationBST.HeavyPath.Paired.Stacks.buildWith RotationBST.HeavyPath.Paired.Stacks.buildWithCost RotationBST.HeavyPath.Paired.lowerSlotsWith RotationBST.HeavyPath.Paired.upperSlotsWith

`pushWith weight payload` stores `payload l` (or the mirror of `payload r`) instead of the erased subtree. The charge is still the frame's `frameMass`, computed from the *source* subtree. The physical layout of a payload therefore never changes the weights that the pop-tarts see. `buildWith`, `buildWithCost` and the `*SlotsWith` lists are the corresponding generalizations. The cost of each push is the same `pushCost`, which does not depend on the payload.

@decl RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_trace RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_valid RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_amortized RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_mass RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_lower_size RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_trace RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_valid RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_amortized RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_mass RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_lower_size RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_fringe

The push and build theorems of the previous section, with payloads: the same exact traces, now starting under the substituted frames; the same validity condition; the same amortized bound of $23$ per push; the same masses; and the same fringe description with `*SlotsWith`.

@decl RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_erase RotationBST.HeavyPath.Paired.Substitution.Results.pushWith_congr RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_congr

With `payload = erase`, `buildWith` is `build`. The two congruence lemmas say that only the payload's values on the frames' own subtrees matter, so the payload function may be changed elsewhere, for instance when the fuel of a recursive construction changes.

@decl RotationBST.HeavyPath.Paired.Substitution.Results.replaced_plug_size RotationBST.HeavyPath.Paired.Substitution.Results.buildWith_size RotationBST.HeavyPath.Paired.Substitution.Results.replaced_offset

If every payload has the size of its source subtree, nothing moves in rank. The substituted context plugs to a tree of the source size, the built pair has the size of the source tree, and the substituted frames have the same inorder offset as the erased ones. This is how ranks in the physical tree are translated back to the source.

## Exposure: popping the topmost ancestor

A push makes the heavy path one node longer at the top. The opposite operation removes the topmost ancestor, the one farthest from the endpoint, and makes it the physical root again, with its payload on its side and the rest of the path, still paired, below it. The topmost frame of the heavy path from the root holds the source root itself, so exposing it makes the source root the physical root, with its off-path payload on its side. [Chapter 47](recursive-heavy-paths.html) uses this to expose the source root and join it back.

@decl RotationBST.HeavyPath.Paired.Stacks.Represents RotationBST.HeavyPath.Paired.Stacks.exposeCost

`p.Represents weight payload cs` says that `p` is a valid pair that stores exactly the frames `cs` with payloads `payload`. Both fringes, read in stored coordinates, are the expected slot lists followed by the empty leaf. The pop-tart *shapes* are not fixed. Any valid Chocolate history with the right fringe is allowed, and a pop need not undo the shape of the push it reverses. `exposeCost` is the cost of the exposure: the cursor enters the stack on the frame's side, the stack pops ([[PopTart.Chocolate.Layer.popCost]]), and four more instructions return to the endpoint, descend and rotate the popped separator to the root.

@decl RotationBST.HeavyPath.Paired.Exposure.Results.lower_trace RotationBST.HeavyPath.Paired.Exposure.Results.upper_trace

The physical part. If the lower pop-tart pops a leaf, the crumb `crumb`, leaving `rest` ([[PopTart.Chocolate.Layer.pop]]), then a trace of `popCost + 4` instructions turns the pair into a root with `crumb`'s tree on the left and the remaining pair on the right; the root is the separator. The upper case is the mirror image.

@decl RotationBST.HeavyPath.Paired.Exposure.Results.empty_represents RotationBST.HeavyPath.Paired.Exposure.Results.push_represents RotationBST.HeavyPath.Paired.Exposure.Results.build_represents RotationBST.HeavyPath.Paired.Exposure.Results.represents_sizes

`empty` represents the empty path, a push with a nonnegative charge appends its frame, and so `buildWith` represents its frames. Two representations of the same frames have the same lower, upper and total sizes, even if their shapes differ. The rank of the endpoint therefore depends only on the path, not on the pop-tart history.

@decl RotationBST.HeavyPath.Paired.Exposure.Results.expose_frame

**Theorem (exposure).** If $p$ represents the frames `cs ++ [frame]`, where `frame` is the topmost ancestor, then some pair `rest` represents `cs`, and a trace of exactly `exposeCost frame` instructions turns the tree of $p$ into the topmost separator at the root, its substituted payload on its side and `rest` as its other child. Moreover

$$\texttt{exposeCost} + \Phi(\mathit{rest}) \le 24 + \Phi(p), \qquad M(p) = M(\mathit{rest}) + \texttt{frameMass}(\mathit{frame}).$$

Together with push, this makes the top of the path a stack with constant amortized cost per operation: frames enter by `pushWith` and leave by `expose_frame`.

## Population: worst-case costs

The deamortization needs more than amortized bounds: every single response must cost $O(\log n)$. The Chocolate pop-tart bounds the cost of one push and one pop by the logarithm of its number of leaves ([[PopTart.Chocolate.Results.push_worst_case]], [[PopTart.Chocolate.Results.pop_worst_case]]). In a pair, the number of leaves of each stack, its *population*, is at most the number of nodes of the pair.

@decl RotationBST.HeavyPath.Paired.Population.Results.leaf_count_size RotationBST.HeavyPath.Paired.Population.Results.pair_population

A weighted tree has between $1$ and $|t| + 1$ leaves, where $|t|$ counts its internal nodes. In a pair, each stack has between $1$ and $|p|$ leaves, since the endpoint is a node outside both stacks.

@decl RotationBST.HeavyPath.Paired.Population.Results.push_cost_bound RotationBST.HeavyPath.Paired.Population.Results.expose_cost_bound

**Theorem (worst-case push and exposure).** For a valid pair with at most $n$ nodes, one push, with the instruction that enters it from the ancestor, costs at most $10 + 14\log_2 n$, and one exposure costs at most $10 + 10\log_2 n$.

These bounds hold for each operation separately, without potential, and for any frame. They count the nodes of the pair, payloads included, so $n$ can be taken to be the size of the whole tree.

## Interruption: depth at every instruction

The deamortized algorithm does not run the simulation in whole operations. It interleaves source work with the service of requests, and it may stop a push or a pop between any two instructions and serve a request from the tree as it stands. Depth bounds that hold only before and after a push are not enough. The interruption lemmas bound the depth of every key at every instruction boundary, relative to its depth at the start, using [[Pointer.TraceWithin]] traces, which check an invariant on every intermediate tree.

@decl RotationBST.HeavyPath.Paired.Interruption.Results.lower_pop RotationBST.HeavyPath.Paired.Interruption.Results.upper_pop RotationBST.HeavyPath.Paired.Interruption.Results.lower_push RotationBST.HeavyPath.Paired.Interruption.Results.upper_push RotationBST.HeavyPath.Paired.Interruption.Results.push_frame

**Theorem (interruptible pushes and pops).** The exposure traces of `lower_trace` and `upper_trace` can be taken so that every intermediate tree has the size of the starting tree, and every rank $x$ has depth at most $4\,d(x) + 10$, where $d(x)$ is its depth in the starting tree. Likewise for a push that starts from the tree in which the new ancestor is the physical root, with its payload on one side and the pair on the other, and the cursor at that root. It takes `pushCost + 1` instructions, the stack's push cost plus four, and can be done so that every intermediate depth is at most $4\,d(x) + 16$.

`lower_push` and `upper_push` state the push for a raw payload and charge. `push_frame` states it for a source frame with a substituted payload, ending at `pushWith`. The bounds are pointwise and linear in the starting depth, so they compose with the logarithmic depth bounds of the starting tree. The predicate quantifies over all natural numbers `x`, including ranks outside the tree, where [[Tree.depth]] is a totalized value. The bound holds for those as well, and is used only for actual keys. The policies of [Chapter 49](finger-histories.html) carry certificates of this kind for each emitted program (their `PolicyWithin` condition). That is how the depth bound at every cut in [[Deamortization.Weighted.Results.simulation]] is obtained.
