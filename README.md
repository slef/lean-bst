# lean-bst

Lean formalizations of binary search trees using **unlabelled tree shapes**,
with keys represented by their zero-based inorder ranks. The library includes:

- correspondence with labelled BSTs and the conventional pointer model;
- executable bottom-up splaying, its working-set bound, and further classical results;
- arborally satisfied sets, offline BST equivalence, GreedyASS, and a causal online geometric-to-BST simulation;
- an executable Tango-style policy with an `O(log log n)` competitive bound.

The public mathematical interface is in `Abstract.lean` files. The development
is kernel-checked locally; it has not been submitted to or reviewed by
[Complexitylib](https://github.com/cslib-community/complexitylib) or CSLib.

## Build and validation

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
python3 scripts/check_imports.py
lake build --wfail
```

[lean-toolchain](lean-toolchain) pins Lean **4.36.0-rc2**.
[lakefile.toml](lakefile.toml) pins CSLib at
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`; Mathlib is a transitive dependency.
These are this repository's pins, not a claim of compatibility with current upstream revisions.

```lean
import RotationBST
```

imports the complete library. The default build includes
[RotationBSTTests](RotationBSTTests.lean). Checks cover library import reachability,
public statement boundaries, regression examples, and the axiom dependencies of
all imported library declarations. The axiom audit permits only `propext`,
`Classical.choice`, and `Quot.sound`; it rejects dependencies such as `sorryAx`.
The project uses `autoImplicit = false` and explicit module exports.

## Where to start

Following [abstractlean](https://github.com/slef/abstractlean), definitions and
result statements are separated from proof implementations. Result abstracts
use `#check_bst_abstract` to check that their statements depend only on explicitly
listed readable foundations. The [checker](RotationBST/AbstractAudit/Check.lean)
is local to this repository; upstream abstract registration is separate work.

| Topic | Entry point |
|---|---|
| Shapes, rotations, and root accesses | [Model](RotationBST/Model/Abstract.lean) |
| Arbitrary labels and BST ordering | [Representation](RotationBST/Representation/Abstract.lean), [ordering](RotationBST/Representation/Ordering/Abstract.lean) |
| Mathlib `BinaryTree Unit` correspondence | [Mathlib interface](RotationBST/Representation/Mathlib/Abstract.lean) |
| Online algorithms and cost conventions | [Online](RotationBST/Online/Abstract.lean) |
| Pointer machine and model simulations | [Machine](RotationBST/Pointer/Machine/Abstract.lean), [simulations](RotationBST/Pointer/Abstract.lean) |
| Splay algorithm and results | [Algorithm](RotationBST/Splay/Algorithm/Abstract.lean), [overview](RotationBST/Splay/Abstract.lean) |
| Working-set, static-optimality, and static-finger implications | [Generic implications](RotationBST/Bounds/Implications/Abstract.lean) |
| ASS, GreedyASS, and online geometry | [Arboral overview](RotationBST/Arboral/Abstract.lean) |
| Offline geometric equivalence | [Equivalence](RotationBST/Arboral/Equivalence/Abstract.lean) |
| Uniform causal geometric-to-BST simulation | [Online simulation](RotationBST/Arboral/Online/LastTouch/Supernode/Policy/Results/Abstract.lean) |
| Tango policy and competitive bounds | [Executable policy](RotationBST/Tango/Algorithm/Executable/Abstract.lean), [bounds](RotationBST/Tango/Algorithm/Abstract.lean) |

For exposition, see the [interactive textbook](book/README.md) and
[PDF source](docs/main.texlish). The [scope audit](docs/formalization-audit.txt)
records the checked interfaces and implementation variants. Lean statements are
authoritative for exact hypotheses and constants.

## Model and cost conventions

A shape determines a unique labelled tree for any fixed inorder key list of
matching length. For strictly increasing keys, this gives the usual BST ordering
invariant. Labelling and erasure preserve rotation traces and their costs; accesses
to distinct explicit keys correspond to accesses to their inorder ranks.

In the simple model, a rotation can occur anywhere in the tree. An `Access`
finishes with the requested key at the root. Write `n` for the number of keys,
`m` for the request count, and `R` for the rotation count. Normalized total cost
is `T = m + R`: a root access may require zero rotations, so request charges
cannot be dropped from multiplicative comparisons.

The [pointer machine](RotationBST/Pointer/Machine/Abstract.lean) starts each search
at the root, charges parent/child moves and rotations, and requires a visit to
the requested key. The [model simulations](RotationBST/Pointer/Abstract.lean) prove:

- A pointer execution of cost `K` gives a root-access execution and a final
  restoration suffix with combined request-plus-rotation cost at most `3K`.
- A root-access execution gives a pointer execution of cost `C` and a final
  deferred suffix of `d` rotations with `C + 32d ≤ 32R + 17m`.
- Exact final-tree agreement is also available through an eager simulation,
  with the weaker size-dependent bound `m + 2nR`.

The [causal transformer](RotationBST/Pointer/Lazy/Online/Abstract.lean) extends the
constant-factor simulation to online algorithms and proves prefix composition.
The model charges abstract BST operations, **not** the evaluation time of Lean
functions, subtree-size computation, or planning. General simulations use
classical choice; the splay and Tango request operations are executable.

## Splay results

The implementation is bottom-up **zig / zig-zig / zig-zag** splaying. It uses
only the current shape and requested rank, without analysis weights or history.
It exposes the requested key, and its rotation count equals the original search
depth. The weighted access lemma is proved with positive weights and logarithmic
subtree potential.

The library proves results corresponding to the nine numbered theorems in
Sleator and Tarjan's 1985 paper. Constants and conventions are explicit in the
linked statements; this is not a formalization of every implementation variant
in that paper. All logarithms below are base two.

| Result | Checked form |
|---|---|
| [Balance](RotationBST/Splay/Balance/Abstract.lean) | `T ≤ m(2 + 3 log n) + n log n`. |
| [Static optimality](RotationBST/Splay/StaticOptimality/Abstract.lean) | Frequency-entropy bound; when every key occurs, `T ≤ 4(m + Σ qₓ log(m/qₓ))` without startup. Also compared with every fixed BST. |
| [Static finger](RotationBST/Splay/StaticFinger/Abstract.lean) | Bound in `Σ(1 + log(\|x−f\|+1))`, using rank distance and an explicit startup allowance; a coverage hypothesis removes startup. |
| [Working set](RotationBST/Splay/WorkingSet/Abstract.lean) | `R ≤ 10 WS + 6n(1 + floor(log n))`. First use has working-set number `n`; later uses count distinct intervening keys plus one. |
| [Unified](RotationBST/Splay/Unified/Abstract.lean) | `T ≤ 11 U + 8n(1 + floor(log n))`, using the per-access minimum of frequency, fixed-finger, and working-set terms. |
| [Updates](RotationBST/Splay/Updates/Abstract.lean) | Rank-based access, insertion, deletion, split, and join. Initially empty forests cost at most `Σⱼ(5 log(nⱼ+1)+3)`, where `nⱼ` counts participating keys. |
| [Long splay](RotationBST/Splay/Conditional/Abstract.lean) | Conditional splaying bounds total restructuring by `2Σₓ log(W/w(x))`; unit weights give `2n log n`. This is not a bound on all search costs. |
| [Snapshot](RotationBST/Splay/Snapshot/Abstract.lean) | Independent requests with distribution `p` and uniform stopping give expected static search cost at most `5 + 3H(p) + n(1+log n)/m`, for `m > 0`. Zero probabilities are allowed. |
| [Scanning](RotationBST/Splay/Scanning/Abstract.lean) | Accessing `0, …, n−1` from any initial shape costs at most `14n` normalized operations, or `40n` pointer operations. |

Here [WS](RotationBST/WorkingSet/Abstract.lean) sums
`1 + floor(log₂(working-set number))`; [U](RotationBST/Bounds/Unified/Abstract.lean)
is the **1985 fixed-finger unified bound**. The later dynamic unified-bound
conjecture is not asserted.

The implications **working set ⇒ static optimality ⇒ static finger** are proved
for every `Algorithm`, independently of splay. A separate
[entropy lower bound](RotationBST/Bounds/StaticTree/Abstract.lean) connects the
frequency formulation to search cost in every fixed comparison tree.
The concrete splay algorithm also has a pointer implementation preserving its
final shape and satisfying a working-set bound.

## Arboral geometry

An **arborally satisfied set (ASS)** is a finite set of key/time points such that
every pair with different keys and times spans a closed rectangle containing a
third point. Boundary points count. See the concise
[definition](RotationBST/Arboral/Definitions/Abstract.lean).

The [offline equivalence](RotationBST/Arboral/Equivalence/Abstract.lean) proves:

| Conversion | Bound and initial-tree convention |
|---|---|
| ASS ↔ rooted-region execution | Exact point-count / touched-region-cost equivalence, with a free initial tree. |
| Rotation execution → ASS | At most `2R + m` points. |
| Pointer execution → ASS | At most `6C` points for pointer cost `C`. |
| ASS → pointer execution | At most `33G` operations for `G` points; the initial tree may depend on future requests. |
| ASS → rotation execution | Normalized cost at most `2n + 99G` from any prescribed initial shape. |

A rooted-region operation visits its request and rearranges a connected region
while preserving its exact inorder fringe. The offline construction uses
next-touch treaps; its future-dependent choices are separate from the online proof.

[Online geometric algorithms](RotationBST/Arboral/Online/Abstract.lean) complete
one row at a time using the old point set and current request. Their row-point
cost equals the cardinality of the resulting ASS solution. The standard
**GreedyASS sweep** is proved legal, and every legal current-row completion
contains its points, so it is the unique minimum-cardinality completion of that
row. This local minimum is not a claim of global optimality.

The [causal simulation](RotationBST/Arboral/Online/LastTouch/Supernode/Policy/Results/Abstract.lean)
proves that, for every geometric online algorithm on `n` keys, **one BST policy**
works for all initial trees of size `n` and all valid request sequences. Its bounds are:

```text
rotations              ≤ 6018 G + 6018 n
requests + rotations   ≤ 6019 G + 6018 n
```

A fixed causal pointer strategy has a linear bound as well. The proof represents
last-touch supernodes using shared split trees, extracts the current row, and
rebuilds its exposed keys. A nested potential pays for splitting, rebuilding,
root visits, and deferred restoration across all rows. These constants are not
claimed to be sharp. Neither splay nor GreedyASS is proved dynamically optimal.

## Tango

The [executable Tango-style policy](RotationBST/Tango/Algorithm/Executable/Abstract.lean)
maintains preferred paths and their ordered nesting, compiles preference changes
into cuts and joins, and serves each requested rank. It uses **splay-based auxiliary
trees** with amortized bounds; the original red-black auxiliary implementation
is not formalized.

[Wilber's interleave lower bound](RotationBST/Tango/LowerBound/Abstract.lean) is
proved against geometric, rotation, and pointer executions. The
[competitive theorem](RotationBST/Tango/Algorithm/Abstract.lean) compares a fixed
policy with every offline rotation execution on the same key universe. If the
reference tree has height `H`, the policy's normalized cost is at most

```text
(56 log₂ H + 16)(R + m) + (14 log₂ H + 4)n.
```

The policy starts from its reference tree; the comparator may start from any
shape of the same size. An executable balanced reference exists for every `n`,
with height at most `floor(log₂ n) + 1`, yielding the doubly logarithmic competitive
factor and a separate initialization term. Planning and reference lookup time
are outside the abstract rotation cost.

## Scope and upstream work

The [scope audit](docs/formalization-audit.txt) maps the requested results to their
exported statements. Relevant limits and follow-up work are:

- Top-down and semisplaying variants are not implemented.
- Updates operate on local ranks and ordered forests. Computing ranks from new
  comparison keys and allocation-aware pointer updates are not formalized.
- Kernel checking proves the stated propositions; it does not establish runtime
  complexity of uncharged planning or stronger unstated variants.
- Upstream integration still needs API and namespace review, contribution-sized
  packaging, upstream linters, and abstract registration. Dependency pins and
  local audits alone do not establish upstream compatibility or acceptance.

## Documentation

The [interactive textbook](book/README.md) has its own extraction, build, and test
instructions. Its source is in `book/`; the Lean abstracts remain authoritative
when checking theorem scope.

The [PDF source](docs/main.texlish) includes tree diagrams and extracted Lean
snippets. With `texlish@0.2.0`, `latexmk`, and the TeX packages listed in the
[documentation workflow](.github/workflows/docs.yml) installed, run:

```sh
python3 docs/extract_snippets.py
make -C docs
```

The PDF is written to `docs/build/main.pdf` and published as a CI artifact.

## References and provenance

- Sleator and Tarjan, [*Self-Adjusting Binary Search Trees*](https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf), JACM, 1985.
- Derryberry, [*Adaptive Binary Search Trees*](https://www.cs.cmu.edu/~jonderry/thesis.pdf), 2009; model comparisons.
- Kakimura and Terai, [*A Refined Analysis of the Sequential Access Theorem for Splay Trees*](https://arxiv.org/abs/2609.19746), 2026; the scanning proof uses their ghost-marking and right-spine-potential approach, with a looser constant.
- Demaine, Harmon, Iacono, Kane, and Pătraşcu, [*The Geometry of Binary Search Trees*](https://people.csail.mit.edu/mip/papers/arboral/paper.pdf), SODA, 2009.
- Demaine, Harmon, Iacono, and Pătraşcu, [*Dynamic Optimality—Almost*](https://erikdemaine.org/papers/Tango_SICOMP/paper.pdf), SIAM Journal on Computing, 2007.

Elementary rotation-composition, move-to-root, and linear-reset arguments were
adapted from the alternate `origin/state-elimination` branch at `5f0159d` and
independently checked. Its broader research claims were not imported. Move-to-root
is retained as a separate baseline, not used as a substitute for splaying.
