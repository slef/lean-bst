# Accesses and executions

In the usual pointer model a search walks from the root to the requested key, and restructuring is whatever the algorithm does along the way. The library's basic model is the *root-access* rotation model instead, in the style of Wilber. To serve a request for $x$, the algorithm performs any rotations it likes, anywhere in the tree, and must finish with $x$ at the root. Its cost is the number of rotations. [Chapter 5](pointer.html) proves that this model and a conventional pointer machine agree up to constant factors. This chapter defines the model.

## Root accesses

@decl RotationBST.Access

`Access s t x k` holds when `k` rotations turn `s` into `t` and the root of `t` has rank `x`. The root of `node l r` has rank `l.size` ([Chapter 1](shapes.html#implicit-keys)), so "`x` is at the root" is written `l.size = x`. An empty final tree has no root, so `nil` gives `False`.

::: check
- The rotations are unrestricted. They need not lie on the search path, and they may touch parts of the tree the search never visits. This is deliberate: `Access` describes everything an algorithm is *allowed* to do. Particular algorithms, such as splaying, satisfy it with specific rotation sequences, and the [simulation theorems](pointer.html) show that the freedom does not make the model stronger than a pointer machine by more than a constant factor.
- The cost is rotations only. A request whose key is already at the root can be served by `Access s s x 0`. This is why the conventional total cost in [Chapter 6](online.html) adds one unit per request.
- The definition is a `Prop`, not a function: it says which outcomes are legal, not how to compute one.
:::

An access can only request an existing key:

@stmt RotationBST.Access.in_range

## Executions

An offline execution serves a whole request sequence, one root access after another:

@decl RotationBST.Execution

`Execution t xs u k` holds when the requests `xs` can be served in order, starting from `t` and ending at `u`, with `k` rotations in total. Each request is served by an `Access` from the tree left by the previous one, and the costs add. Since the strategy is existentially quantified, `Execution` describes every legal offline strategy at once. In particular the offline optimum for `t` and `xs` is the least `k` for which some `Execution t xs u k` exists. [Chapter 6](online.html) compares online algorithms against all executions directly, rather than defining this minimum.

Executions also preserve size:

@stmt RotationBST.Execution.size_eq

## Which requests can be served

Every existing key can be brought to the root, and only existing keys can:

@stmt RotationBST.access_exists_iff

The bound `k < t.size` is the depth of $x$ in the worst case. The proof is constructive: the library's move-to-root baseline rotates $x$ over each of its ancestors in turn, deepest first. It is an ordinary executable function, not part of any statement:

@decl RotationBST.moveToRoot

The recursive call exposes $x$ at the root of the subtree that contains it, and one more rotation (`Rotate.right` or `Rotate.left`, applied inside the parent) lifts it one level. Move-to-root is a different algorithm from splaying ([Chapter 8](splay.html)), and the library's tests check that the two differ.

Lifting `access_exists_iff` to sequences gives the exact executability condition. Sizes never change, so a sequence can be served exactly when every requested rank is below the initial size:

@stmt RotationBST.execution_exists_iff

The hypothesis `∀ x ∈ xs, x < t.size` appears in nearly every theorem about request sequences in later chapters. It is precisely this condition.

## Any shape to any shape

Rotations connect all shapes of a given size, and linearly many suffice:

@stmt RotationBST.Geometry.reset

The proof rotates both shapes into the right spine `.node .nil (.node .nil …)` with at most $n$ rotations each, then reverses the second sequence; rotations are reversible ([[RotationBST.Rotations.symm]]). The bound $2n$ is the classical one, up to the additive constant in Sleator, Tarjan and Thurston's $2n-6$, which the library does not attempt.

An access may therefore be preceded by a reset to any shape, at an extra cost of at most $2n$:

@stmt RotationBST.Geometry.reset_before_access

For offline executions, the initial shape therefore matters only additively, by at most $2n$ rotations. Online algorithms cannot simply reset, and the bounds of [Chapter 7](bounds.html) instead charge an explicit startup term of the form $D \cdot n(1+\lfloor \log_2 n\rfloor)$.

::: exercise Bring a key to the root
The orange node is the request. Rotate until it is at the root. The panel tracks the derivation of `Rotations s t k` and checks the access condition `l.size = x` on the current tree. Move-to-root uses exactly the depth of the requested node; try to finish in that many rotations.
:::

@viz rotate {"tree": ".node (.node .nil (.node (.node .nil .nil) (.node .nil (.node .nil .nil)))) (.node .nil .nil)", "target": 4, "title": "Access s t 4 k"}
