# Splaying

Splay trees, introduced by Sleator and Tarjan in 1985, are the best-known self-adjusting BST. They store no balance information. After every access they move the accessed node to the root by a fixed rotation pattern, and the analysis shows that this alone yields $O(\log n)$ amortized cost, and much more on structured sequences. This section defines the algorithm, proves it is a legal BST algorithm, and shows it can be run on the pointer machine. Its cost guarantees come in the next two sections. [Chapter 14](analysis.html) proves the balance theorem, static optimality, the static finger bound and the working-set bound. [Chapter 15](beyond.html) treats updates, long splays, snapshots and sequential access.

```headline splay-correct
title: Splaying is a legal BST algorithm
source: @sleator1985
theorems: Splay.Results.correct

For every binary search tree $t$ on $n$ keys and every key $x$ of $t$, splaying $x$ is a root access: a sequence of legal rotations that ends with $x$ at the root. The number of rotations is exactly the count the algorithm reports, and it is less than $n$.

In Lean, the algorithm is [[RotationBST.Splay.run]], which returns the new tree and its rotation count. `correct` concludes an [[RotationBST.Access]], the certified notion of "bring $x$ to the root by rotations, at this cost" from [Chapter 3](accesses.html).
```

Bottom-up splaying, as defined in Section 2 of the splay tree paper [@sleator1985], searches for the requested node $x$ and then repeats *splaying steps* until $x$ is the root. A step looks at $x$, its parent $p$ and its grandparent $g$:

- **zig**: if $p$ is the root, rotate $x$ over $p$;
- **zig-zig**: if $x$ and $p$ are both left children, or both right children, rotate $p$ over $g$, then $x$ over $p$;
- **zig-zag**: otherwise, rotate $x$ over $p$, then $x$ over $g$.

Zig and zig-zag are exactly what [move-to-root](move-to-root.html) does; only zig-zig differs. That one change turns $\Theta(n)$ amortized rotations per request into $O(\log n)$.

The library implements this without parent pointers, in two purely functional phases. `locate` performs the search and returns the search path as a *zipper*: the subtree rooted at $x$, together with the list of its ancestors. `splayAt` then consumes that list two ancestors at a time. This section goes through both, checks each equation against the three cases above, and then states what has been proved about the result.

## Searching with a zipper

The search path is recorded with the frames of the pointer machine ([Chapter 5](pointer.html)). A frame describes one ancestor from the point of view of its child on the path: [[RotationBST.Pointer.Frame|Frame.left r]] means "the path went into the *left* child of this ancestor, whose right subtree is `r`", and `Frame.right l` is the mirror image. A list of frames, nearest ancestor first, is enough to rebuild the whole tree around a focused subtree; this is [[RotationBST.Pointer.plug|plug]]. The rank of the focused subtree's smallest key is [[RotationBST.Pointer.offset|offset]] of the context: every `.right l` frame contributes the `l.size + 1` keys of its left subtree and root.

@decl RotationBST.Splay.locate

This is ordinary search by rank. At `node l r`, the root has rank `l.size` within the subtree. A smaller `x` continues in `l` with the same relative rank. A larger `x` continues in `r` with relative rank `x - l.size - 1`. That subtraction is only evaluated when `x > l.size`, so it never truncates. The recursive result's context is extended *at the end* by the frame for the current node (`c.context ++ [.left r]`). The current node is the farthest ancestor of everything found below it, so the finished context lists the nearest ancestor first and the root last.

The returned [[RotationBST.Pointer.Config|Config]] has the subtree rooted at $x$ as its focus, and the context as its ancestor list. If `x` is out of range, the search falls off the tree and the focus is `.nil`.

::: check
The library proves that `locate` does what this description says, for every rank in range. Plugging the context back around the focus gives the original tree. The focus is the node of rank `x`, which is [[RotationBST.Pointer.Config.key?|key?]] `= offset context + l.size`. The context is shorter than the tree size. This is the lemma `Splay.locate_correct`.

The number of frames is also exactly the ordinary search depth: `(locate t x).context.length = t.depth x` (`Splay.locate_depth`, with [[RotationBST.Tree.depth]] from [Chapter 1](shapes.html)). Both lemmas are proof-level facts, outside the reading interface, so their Lean is not quoted here.
:::

## The splaying steps

@decl RotationBST.Splay.splayAt

`splayAt l r cs` splays the node $x$ = `node l r` up through its ancestor list `cs`. Each of the seven equations is one case of the description above. Below, $x$'s subtrees are $l$ and $r$, its parent is $p$ and its grandparent is $g$. Trees are written in parenthesized inorder, so $(A\,p\,B)$ is a node $p$ with left subtree $A$ and right subtree $B$, and nodes appear in increasing key order.

1. `[]`: $x$ has no ancestors, so it is already the root. The result is `node l r`.
2. `[.left b]`: $x$ is the left child of the root $p$, whose right subtree is $b$. A **zig** rotates $x$ over $p$:
   $$((l\,x\,r)\,p\,b) \;\to\; (l\,x\,(r\,p\,b)),$$
   which is `.node l (.node r b)`.
3. `[.right a]`: the mirror image, a **zig** with $x$ the right child of the root:
   $$(a\,p\,(l\,x\,r)) \;\to\; ((a\,p\,l)\,x\,r).$$
4. `.left b :: .left c :: cs`: $x$ is the left child of $p$, which is the left child of $g$. Here $b$ is $p$'s right subtree and $c$ is $g$'s right subtree. A **zig-zig** rotates $p$ over $g$, then $x$ over $p$:
   $$(((l\,x\,r)\,p\,b)\,g\,c) \;\to\; (l\,x\,(r\,p\,(b\,g\,c))).$$
   The new subtree of $x$ has left child $l$ and right child `.node r (.node b c)`. That pair becomes the new focus, and splaying continues with the remaining ancestors `cs`.
5. `.right a :: .right b :: cs`: the mirror **zig-zig**. Here $a$ is $p$'s left subtree and $b$ is $g$'s left subtree:
   $$(b\,g\,(a\,p\,(l\,x\,r))) \;\to\; (((b\,g\,a)\,p\,l)\,x\,r).$$
6. `.right a :: .left b :: cs`: $x$ is the right child of $p$, which is the left child of $g$. A **zig-zag**:
   $$((a\,p\,(l\,x\,r))\,g\,b) \;\to\; ((a\,p\,l)\,x\,(r\,g\,b)).$$
7. `.left b :: .right a :: cs`: $x$ is the left child of $p$, which is the right child of $g$. The mirror **zig-zag**:
   $$(a\,g\,((l\,x\,r)\,p\,b)) \;\to\; ((a\,g\,l)\,x\,(r\,p\,b)).$$

In each displayed transformation, the subtrees appear in the same left-to-right order on both sides, and so do $p$, $g$ and $x$. Equations 6 and 7 have the same right-hand side, `splayAt (.node a l) (.node r b) cs`, because both zig-zags leave $x$ between its two former ancestors. Only the variable names say which ancestor ends up on which side.

::: check
- A **zig** happens only when exactly one ancestor is left, that is, when $p$ is the root of the *whole* tree, as in the paper. With two or more ancestors, the step is always a double one.
- Splaying never plugs anything back into the tree. The new subtree of $x$ is carried as the focus, and the intermediate whole tree is `plug cs (.node l r)`. At the end the context is empty and $x$ is the root.
- The equations alone do not show that the double steps are the paper's rotation sequences, as opposed to some other restructuring with the same result. The correctness lemma below fixes this, because its proof gives the rotations explicitly. In the zig-zig case they are two root rotations at the grandparent's position, `.right` then `.right`: first $p$ over $g$, then $x$ over $p$. In the zig-zag case they are `.inLeft .left` then `.right`: first $x$ over $p$ inside $g$'s left subtree, then $x$ over $g$. These derivations are checked by the kernel.
- The library's tests separate zig-zig from rotating $x$ twice: `Splay.run` on a three-node left path, requesting key $0$, gives the right path, while [[RotationBST.moveToRoot]] gives a different tree.
:::

**Theorem (splaying a focus).** Let $x$ be the root of the subtree `node l r`, sitting below the ancestors `cs` in the tree `plug cs (node l r)`. Then `splayAt l r cs` is reached from that tree by a root access to $x$, whose rank is `offset cs + l.size`, using exactly `cs.length` rotations, one per ancestor. In the library this is `Splay.splayAt_correct`, the lemma from which [[RotationBST.Splay.Results.correct]] below is derived.

This is the invariant behind everything that follows; "root access" is in the sense of [Chapter 3](accesses.html). A zig uses one rotation for one frame, and a double step uses two rotations for two frames, so the count is exact.

## The splay function

@decl RotationBST.Splay.run

`run t x` searches, then splays, and reports the splayed tree with its rotation count. That count is `c.context.length`, the number of ancestors of $x$: its depth. If the search ends at `.nil` (because `x` is out of range), `run` returns the tree unchanged with cost $0$. No theorem relies on this case; every statement about `run` assumes `x < t.size`.

@viz splay {"n": 11, "shape": "left-path", "x": 3}

The figure runs a transcription of `locate`, `splayAt` and `run`. Each **Step** applies one equation, and the corresponding line of `splayAt` above is highlighted. The panel shows the remaining context in the same notation as the Lean source. A left path on $n$ keys is the classical bad start: one access to a deep key roughly halves the depth of every node on the path. Use **Keep result** to request another key from the splayed tree.

## Correctness

**Theorem (correctness of splaying).** For every tree $t$ and every rank $x < |t|$, `run t x` returns a tree and a count $k$ such that the tree is reached from $t$ by a root access to $x$ using exactly $k$ rotations, and $k < |t|$.

@decl RotationBST.Splay.Results.correct

For every rank in range, the pair returned by `run` is certified by an `Access`. The rotations are legal (each is a `Rotate` step in the sense of [Chapter 2](rotations.html)), the final root has rank `x`, the cost is exactly the reported count, and that count is less than `t.size`. The proof combines `locate_correct` with `splayAt_correct`: `plug` of the context around the focus is `t`, and `offset cs + l.size = x`.

## Splay as an online algorithm

To compare splaying with other algorithms over whole request sequences, it is packaged as an online algorithm. The certificate the package requires is the correctness theorem again, in the form the package asks for.

**Theorem (splay step).** For every tree $t$ and every rank $x < |t|$, the pair returned by `run t x` is a root access to $x$ at the reported cost.

@decl RotationBST.Splay.step_correct RotationBST.Splay.algorithm

An [[RotationBST.Algorithm|Algorithm]] ([Chapter 6](online.html)) is a step function from the past requests, the current tree and the current request, together with a certificate that each valid step is an `Access`. Splay's step is `run t x`. The first argument, the request history, is ignored (the `_`). The analysis weights of [Chapter 9](analysis.html) appear nowhere. Splay is online in the strictest sense: it sees only the current shape and the current request.

From here on, `algorithm.cost t xs` is the total number of splay rotations over the sequence `xs`, and `algorithm.totalCost t xs` adds one unit per request ([Chapter 6](online.html)).

## A pointer implementation

The rotation model charges nothing for walking down the tree. This splay implementation is nevertheless realizable on the single-cursor pointer machine of [Chapter 5](pointer.html), with the same final tree and constant overhead.

**Theorem (splaying on the pointer machine).** For every tree $t$ and every sequence $X$ of valid ranks, there is a pointer-machine execution that serves $X$ from $t$, ends in exactly the tree that splaying produces, and costs at most $3(m + R)$, where $m + R$ is splaying's total cost (requests plus rotations).

@decl RotationBST.Splay.Results.pointer_execution

The proof follows each access on the pointer machine. The search costs one downward move per frame. A zig is one rotation instruction. A zig-zag is two rotation instructions with the cursor staying on $x$. A zig-zig needs four: move up to $p$, rotate $p$ over $g$, move back down to $x$, rotate $x$ over $p$. An access to depth $d$ therefore costs at most $1 + d + 2d$, and over a sequence the pointer cost is at most $m + 3R \le 3(m+R)$. The final tree is *exactly* `(algorithm.runFrom [] t xs).1`, not merely some tree reachable from it, so the comparison is with the same execution.

::: note What is not charged
Search by rank compares `x` with `l.size`. The Lean function recomputes subtree sizes, but the cost models count abstract BST operations, not the evaluation time of the Lean code. In a conventional implementation with stored keys, the same branch is decided by one key comparison per node, which the pointer machine already pays for with the move.
:::

::: exercise Splay versus move-to-root
Set the figure to a **left path** with $n = 15$ and request key $0$, then keep the result and request key $1$, then key $2$. Each access costs its depth, and the depths fall quickly. [[RotationBST.moveToRoot|Move-to-root]] on the same sequence leaves a path of nearly the same depth after each access ([Chapter 12](move-to-root.html#why-it-is-not-enough)). This is the standard example where single rotations are $\Theta(n)$ amortized while splaying is $O(\log n)$.
:::
