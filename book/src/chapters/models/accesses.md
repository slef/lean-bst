# Accesses and executions

In the usual pointer model a search walks from the root to the requested key, and restructuring is whatever the algorithm does along the way. The library's basic model is the *root-access* rotation model instead, in the style of Wilber. To serve a request for $x$, the algorithm performs any rotations it likes, anywhere in the tree, and must finish with $x$ at the root. Its cost is the number of rotations. [Chapter 5](pointer.html) proves that this model and a conventional pointer machine agree up to constant factors.

This chapter defines the model: a root access [[RotationBST.Access]] serves one request, and an execution [[RotationBST.Execution]] serves a whole sequence. These two definitions are what "a legal BST algorithm" and "the offline optimum" mean in every later theorem. The chapter then shows that the model is not too restrictive. Every existing key can be brought to the root with fewer than $n$ rotations, and only existing keys can be. Any shape can be turned into any other shape of the same size with at most $2n$ rotations, which is why the initial tree matters only additively.

```headline rotation-reset
title: Any tree can be rotated into any other with at most $2n$ rotations
theorems: Geometry.reset

Let $s$ and $t$ be binary trees with the same number $n$ of nodes. Then some sequence of at most $2n$ rotations turns $s$ into $t$.

In Lean, `Geometry.reset` concludes `∃ k ≤ 2 * s.size, Rotations s t k`, where [[RotationBST.Rotations]] `s t k` says that exactly `k` rotations turn `s` into `t`.
```

## Root accesses

@decl RotationBST.Access

`Access s t x k` holds when `k` rotations turn `s` into `t` and the root of `t` has rank `x`. The root of `node l r` has rank `l.size` ([Chapter 1](shapes.html#implicit-keys)), so "`x` is at the root" is written `l.size = x`. An empty final tree has no root, so `nil` gives `False`.

::: check
- The rotations are unrestricted. They need not lie on the search path, and they may touch parts of the tree the search never visits. This is deliberate: `Access` describes everything an algorithm is *allowed* to do. Particular algorithms, such as splaying, satisfy it with specific rotation sequences, and the [simulation theorems](pointer.html) show that the freedom does not make the model stronger than a pointer machine by more than a constant factor.
- The cost is rotations only. A request whose key is already at the root can be served by `Access s s x 0`. This is why the conventional total cost in [Chapter 6](online.html) adds one unit per request.
- The definition is a `Prop`, not a function: it says which outcomes are legal, not how to compute one.
:::

An access can only request an existing key.

**Theorem.** If $k$ rotations turn $s$ into a tree whose root has rank $x$, then $x < |s|$.

The library proves this as `Access.in_range`: rotations preserve size, and the root of a tree of size $n$ has rank below $n$.

## Executions

An offline execution serves a whole request sequence, one root access after another:

@decl RotationBST.Execution

`Execution t xs u k` holds when the requests `xs` can be served in order, starting from `t` and ending at `u`, with `k` rotations in total. Each request is served by an `Access` from the tree left by the previous one, and the costs add. Since the strategy is existentially quantified, `Execution` describes every legal offline strategy at once. In particular the offline optimum for `t` and `xs` is the least `k` for which some `Execution t xs u k` exists. [Chapter 6](online.html) compares online algorithms against all executions directly, rather than defining this minimum.

Executions also preserve size.

**Theorem.** If an execution serves a sequence from $s$ and ends at $t$, then $s$ and $t$ have the same number of nodes.

This is `Execution.size_eq`, by induction on the execution. Both lemmas are proof-level facts, in `Models/Rotation/Basic.lean`; no theorem statement mentions them.

## Which requests can be served

Every existing key can be brought to the root, and only existing keys can.

**Theorem (accessibility).** Let $t$ have $n$ nodes. Rank $x$ can be brought to the root of $t$ with fewer than $n$ rotations if and only if $x < n$.

@stmt RotationBST.access_exists_iff

The bound `k < t.size` is the depth of $x$ in the worst case. The proof is constructive. It runs [[RotationBST.moveToRoot|moveToRoot]], which rotates $x$ over each of its ancestors in turn, deepest first, and so uses exactly as many rotations as $x$ has ancestors. The statement mentions only the model; move-to-root appears in its proof alone. [Chapter 12](move-to-root.html) presents it as an algorithm, and explains why it is a good witness but a poor strategy.

Lifting `access_exists_iff` to sequences gives the exact executability condition. Sizes never change, so a sequence can be served exactly when every requested rank is below the initial size.

**Theorem (executability).** A request sequence $X$ can be served from $t$ by some execution if and only if every request in $X$ is less than $|t|$.

@stmt RotationBST.execution_exists_iff

The hypothesis `∀ x ∈ xs, x < t.size` appears in nearly every theorem about request sequences in later chapters. It is precisely this condition.

## Any shape to any shape

Rotations connect all shapes of a given size, and linearly many suffice.

**Theorem (reset).** If $s$ and $t$ both have $n$ nodes, then at most $2n$ rotations turn $s$ into $t$.

@stmt RotationBST.Geometry.reset

The proof rotates both shapes into the right spine `.node .nil (.node .nil …)` with at most $n$ rotations each, then reverses the second sequence; rotations are reversible (`Rotations.symm`). The bound $2n$ is the classical one, up to the additive constant in the $2n-6$ of Sleator, Tarjan and Thurston [-@sleator1988], which the library does not attempt.

An access may therefore be preceded by a reset to any shape, at an extra cost of at most $2n$.

**Theorem (reset before an access).** Let $s$ and $t$ have $n$ nodes. If $k$ rotations access $x$ in $t$ and end at $u$, then at most $2n + k$ rotations access $x$ in $s$ and end at the same $u$.

@stmt RotationBST.Geometry.reset_before_access

For offline executions, the initial shape therefore matters only additively, by at most $2n$ rotations. Online algorithms cannot simply reset, and the bounds of [Chapter 7](bounds.html) instead charge an explicit startup term of the form $D \cdot n(1+\lfloor \log_2 n\rfloor)$.

::: exercise Bring a key to the root
The orange node is the request. Rotate until it is at the root. The panel tracks the derivation of `Rotations s t k` and checks the access condition `l.size = x` on the current tree. Move-to-root uses exactly the depth of the requested node; try to finish in that many rotations.
:::

@viz rotate {"tree": ".node (.node .nil (.node (.node .nil .nil) (.node .nil (.node .nil .nil)))) (.node .nil .nil)", "target": 4, "title": "Access s t 4 k"}
