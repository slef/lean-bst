# lean-bst

Lean proofs about binary search trees represented by their **unlabelled shapes**.
Keys are zero-based inorder ranks. The library implements bottom-up splaying and
proves its weighted access lemma, working-set bound, static consequences, and
several further results from Sleator and Tarjan's 1985 paper.

The development now includes constant-factor simulations between the rotation
and pointer models, a causal simulator, and a linear sequential-access theorem.
It proves versions of all nine numbered theorems in the 1985 paper, with the
precise assumptions and cost conventions listed below. This is a substantial
local development, not yet an upstream-reviewed submission.

## Build

```sh
lake exe cache get
python3 scripts/check_imports.py
lake build --wfail
```

The project pins Lean **4.36.0-rc2** and CSLib commit
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`, with Mathlib supplied transitively.
These match the inspected [Complexitylib](https://github.com/cslib-community/complexitylib)
configuration. The elementary model uses `Std`; the analytic proofs use Mathlib.
`import RotationBST` imports the complete library. The default build also checks
[RotationBSTTests.lean](RotationBSTTests.lean), including guarded kernel-axiom audits. All variables are explicitly bound
(`autoImplicit = false`), and every library file uses Lean’s module system with
explicit public exports. The test target also audits the axiom dependencies of
all imported library declarations.

## Read the statements first

Following [abstractlean](https://github.com/slef/abstractlean), the public reading
interface consists of short `Abstract.lean` files. Elementary definitions are
shared explicitly between these abstracts; proof machinery is imported through
separate bridges. Some bridges only import a proof module because the public and
internal statements already use exactly the same definitions.

Start with [Splay/Abstract.lean](RotationBST/Splay/Abstract.lean) for the splay overview.
The main definitions and interfaces are:

| Topic | Readable file |
|---|---|
| Shapes, labelled trees, rotations, root accesses | [Model/Abstract](RotationBST/Model/Abstract.lean) |
| Arbitrary-key representation and exact rotation/access costs | [Representation/Abstract](RotationBST/Representation/Abstract.lean) |
| Textbook BST ordering invariant | [Representation/Ordering/Abstract](RotationBST/Representation/Ordering/Abstract.lean) |
| Mathlib `BinaryTree Unit` equivalence | [Representation/Mathlib/Abstract](RotationBST/Representation/Mathlib/Abstract.lean) |
| Online algorithms and cost conventions | [Online/Abstract](RotationBST/Online/Abstract.lean) |
| Conventional pointer machine | [Pointer/Machine/Abstract](RotationBST/Pointer/Machine/Abstract.lean) |
| Constant-factor model simulations | [Pointer/Abstract](RotationBST/Pointer/Abstract.lean) |
| Causal rotation-to-pointer transformer | [Pointer/Lazy/Online/Abstract](RotationBST/Pointer/Lazy/Online/Abstract.lean) |
| Executable zig, zig-zig, zig-zag splay | [Splay/Algorithm/Abstract](RotationBST/Splay/Algorithm/Abstract.lean) |
| Splay as an online algorithm | [Splay/Online/Abstract](RotationBST/Splay/Online/Abstract.lean) |
| Weighted subtree mass and potential | [Splay/Potential/Abstract](RotationBST/Splay/Potential/Abstract.lean) |
| Working-set number and bound | [WorkingSet/Abstract](RotationBST/WorkingSet/Abstract.lean) |
| Frequency entropy and static-finger costs | [Bounds/Abstract](RotationBST/Bounds/Abstract.lean) |
| Fixed-BST benchmark and entropy lower bound | [Bounds/StaticTree/Abstract](RotationBST/Bounds/StaticTree/Abstract.lean) |
| Generic implications between bounds | [Bounds/Implications/Abstract](RotationBST/Bounds/Implications/Abstract.lean) |

This is a hierarchical reading interface. The public result abstracts run
`#check_bst_abstract` with explicit lists of readable foundation modules. The
[local checker](RotationBST/AbstractAudit/Check.lean), adapted from Complexitylib,
traverses theorem statements and definition bodies and rejects unlisted local
implementation dependencies. Regression tests exercise both accepted and rejected
boundaries. Unlike upstream's namespace-wide command, it audits the current
file's declarations, permitting result files to share a namespace. Upstream
registration and independent semantic review still remain.

## Checked splay results

Write `n` for the initial number of keys and `m` for the request count. All logs
are base two. `R` counts rotations; `T = m + R` is normalized total cost.
The algorithm does not store or inspect any of the analysis weights.

| Result | Checked statement / convention |
|---|---|
| Correctness | Every valid access exposes its requested rank; rotations equal search depth and are fewer than `n`. |
| Weighted access lemma | `R + ΔΦ ≤ 3(log W − log s(x)) + 1`, also weakened to the node's own weight. [Abstract](RotationBST/Splay/AccessLemma/Abstract.lean) |
| Balance, paper Theorem 1 | `T ≤ m(2 + 3 log n) + n log n`. [Abstract](RotationBST/Splay/Balance/Abstract.lean) |
| Static optimality, Theorem 2 | With every key accessed, `T ≤ 4(m + Σ qₓ log(m/qₓ))`, without startup. Unused keys are allowed in the general property with startup. [Abstract](RotationBST/Splay/StaticOptimality/Abstract.lean) |
| Static finger, Theorem 3 | Uniform bound in `Σ(1 + log(|x−f|+1))`, with startup; startup can be removed when every key occurs. Distance is **rank distance**. [Abstract](RotationBST/Splay/StaticFinger/Abstract.lean) |
| Working set, Theorem 4 | `R ≤ 10 WS + 6n(1 + floor(log n))`. First access has working-set number `n`; repeated access counts distinct intervening keys plus one. [Abstract](RotationBST/Splay/WorkingSet/Abstract.lean) |
| Unified, Theorem 5 | `T ≤ 11 U + 8n(1 + floor(log n))`, where `U` takes the minimum of frequency, fixed-finger, and working-set logarithms **at each access**. [Definition](RotationBST/Bounds/Unified/Abstract.lean), [theorem](RotationBST/Splay/Unified/Abstract.lean) |
| Updates, Theorem 6 | Rank-based access, insertion, deletion, split, and join on initially empty forests cost at most `Σⱼ(5 log(nⱼ+1)+3)`, where `nⱼ` counts only participating keys. Arbitrary initial forests have an explicit startup term. [Algorithms](RotationBST/Splay/Updates/Algorithm/Abstract.lean), [execution](RotationBST/Splay/Updates/Execution/Abstract.lean), [results](RotationBST/Splay/Updates/Abstract.lean) |
| Long splay, Theorem 7 | For threshold `6 log(W/w(x))+2`, total **restructuring** is at most `2Σₓ log(W/w(x))`; unit weights give `2n log n`, independently of the number of searches. [Abstract](RotationBST/Splay/Conditional/Abstract.lean) |
| Snapshot, Theorem 8 | Independent requests with probabilities `p`; stop uniformly before one of the first `m>0` requests. Expected static search cost is at most `5 + 3H(p) + n(1+log n)/m`. Zero probabilities are allowed. [Finite expectation definitions](RotationBST/Splay/Snapshot/Definitions/Abstract.lean), [theorem](RotationBST/Splay/Snapshot/Abstract.lean) |
| Scanning, Theorem 9 | Accessing ranks `0, …, n−1` from any initial shape costs at most `13n` rotations, `14n` normalized operations, and `40n` pointer operations. [Abstract](RotationBST/Splay/Scanning/Abstract.lean) |

The generic implications **working set ⇒ static optimality ⇒ static finger**
are proved for every `Algorithm`, independently of splay. They use sequence
inequalities, including grouping inter-access gaps and a logarithmic sum bound.
A prefix-code argument also proves that entropy cost is at most three times the
ordinary search cost in **every fixed BST**. This connects the frequency formulation to competitiveness against every fixed
comparison tree. When
every key occurs, splay costs at most twelve times any fixed-tree search cost.

The unified theorem is the **1985 fixed-finger** theorem, not the later dynamic
unified-bound conjecture. Conditional splaying leaves short searches unchanged;
it is therefore analyzed as a pointer search, not falsely certified as a root
access. Its restructuring theorem does not bound all search costs independently
of `m`. Updates use local ranks and concatenate ordered key sets on join; they
are not operations on an unchanging global rank universe. Their input includes
the insertion/split rank; the library does not yet formalize computing that rank
from an arbitrary new comparison key or the full pointer machine with allocation.

## What the model correspondence proves

- Every shape has exactly one labelling by any fixed inorder key list of matching
  length. The local left/root/right ordering invariant is proved equivalent to
  strictly increasing inorder traversal. Thus an increasing list gives exactly
  one conventional BST of each shape, and rotations preserve that invariant.
- Erasing labels preserves rotations, and arbitrary-key labelled rotation traces
  correspond exactly to shape traces with the same count. For distinct keys, accesses also correspond exactly to accesses of the
  key at the requested inorder position.
- Every existing rank is accessible; a sequence is executable exactly when all
  its ranks exist. Two equal-size shapes can be reset in at most `2n` rotations.
- A pointer execution of cost `K` gives a root-access execution with a charged
  final rotation suffix and total cost at most `3K`.
- Eagerly replaying a general shape execution with `R` rotations gives a pointer
  execution with the same final tree and cost at most `m + 2nR`.
- The lazy simulation gives a pointer execution of cost `C` and a final rotation
  suffix of length `d`, with `C + 32d ≤ 32R + 17m`. This is a constant-factor
  bound independent of tree size. Final shapes agree after the deferred suffix.
- A causal transformer makes this bound available for every certified online
  rotation algorithm. Each step uses only the current request, history and
  simulation state; a prefix-composition theorem rules out lookahead. Its
  planning uses classical choice and is uncharged in the abstract model.
  Generic working-set guarantees and conditional normalized dynamic optimality
  transfer through this simulator.
- For the concrete splay algorithm, a pointer execution preserves its final tree
  and costs at most `m + 3R`. In particular its pointer working-set bound is
  `31 WS + 18n(1 + floor(log n))`.

The lazy proof first commutes rotations with disjoint endpoint keys. It then
selects the rotation-graph component of the current root. Those keys form a
connected rooted region with at most two endpoints per selected rotation plus
the root. A checked vine construction reshapes this region in linear pointer
cost without entering its fringe subtrees. Deferred work is carried to later
requests and charged once. The [exchange and region interface](RotationBST/Pointer/Lazy/Abstract.lean)
and [causal simulator](RotationBST/Pointer/Lazy/Online/Abstract.lean) expose these results.

The scanning proof uses unlabelled ghost-marked trees and a quadratic
right-spine potential adapted from [Kakimura and Terai (2026)](https://arxiv.org/abs/2609.19746).
It charges middle zig-zig pairs to potential decrease and the top steps to a
constant per request. The proof establishes a generous linear constant; it does
not claim that paper's sharper `5.5n` bound.

A root access can cost zero rotations. Dropping the request charge is therefore
not a valid multiplicative normalization. The library proves that adding it
preserves the working-set property. The original `DynamicallyOptimal` retains
rotation-only accounting; `TotallyDynamicallyOptimal` uses normalized cost.
Neither is proved for splay.

The cost model charges abstract BST operations, not evaluation time of the Lean
functions that compute subtree sizes or search histories. The general online
interface permits uncharged planning and full request history; splay itself uses
only its current tree.

## Remaining work and upstream submission

1. Further variants and applications from the paper, including top-down and
   semisplaying. The implementation here is the original bottom-up splay.
2. Comparison-key updates and a pointer machine with allocation; the current
   update theorem uses supplied local ranks and a forest of shapes.
3. Upstream API integration: CSLib namespaces, a narrower exported helper surface, upstream linters,
   and upstream abstract registration. The local statement boundaries, Mathlib
   tree interoperability, module exports and explicit binders are checked.
   No submission or upstream compatibility build has been made.

The dependency versions are aligned, but that alone does not establish submission
readiness. [Complexitylib's contribution guide](https://github.com/cslib-community/complexitylib/blob/main/CONTRIBUTING.md)
favors small independently useful contributions and checked clients. The model,
splay implementation, analytic lemmas, and sequence inequalities should be split
into separately reviewable contributions.

## Sources and provenance

- Sleator and Tarjan, [*Self-Adjusting Binary Search Trees*](https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf), JACM 32(3), 1985, pp. 652–686.
- Derryberry, [*Adaptive Binary Search Trees*](https://www.cs.cmu.edu/~jonderry/thesis.pdf), 2009, especially Sections 2.2 and 3.4 for model comparisons.
- Kakimura and Terai, [*A Refined Analysis of the Sequential Access Theorem for Splay Trees*](https://arxiv.org/abs/2609.19746), 2026.
- [abstractlean](https://github.com/slef/abstractlean) and [Complexitylib's abstract conventions](https://github.com/cslib-community/complexitylib/blob/main/abstracts/README.md).

The alternate `origin/state-elimination` branch at `5f0159d` was inspected, not
merged. Only its rotation composition/lifting, constructive move-to-root baseline,
and linear reset arguments were adapted and independently rechecked. Its broader
research claims are not imported. Move-to-root remains a separate baseline and
is explicitly tested to differ from zig-zig splaying.

## Explanatory document

[docs/main.texlish](docs/main.texlish) explains the elementary model with vector
tree figures and extracted Lean snippets. With Texlish and the documented TeX
packages installed, run:

```sh
python3 docs/extract_snippets.py
make -C docs
```

The output is `docs/build/main.pdf`; CI publishes it as an artifact. The source
abstracts remain authoritative for the full theorem statements and assumptions.
