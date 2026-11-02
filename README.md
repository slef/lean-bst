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

## Arboral geometry and Tango foundations

The new [arboral abstract](RotationBST/Arboral/Abstract.lean) and
[Tango abstract](RotationBST/Tango/Abstract.lean) are checked. The offline geometric equivalence and Wilber lower bound are now
proved. A fixed online Tango-style policy now has a checked competitive bound.
Its preference edits and request serving are now executable. The causal
ASS-to-BST conversion is also proved, with one BST policy uniform over all
initial trees of the given size and all valid request sequences.

An arborally satisfied set (ASS) is a finite set of key/time points such that
every pair with different keys and times spans a **closed** rectangle containing
a third point. The six-line definition is in
[Arboral/Definitions/Abstract.lean](RotationBST/Arboral/Definitions/Abstract.lean).
Points on rectangle boundaries count; adding arbitrary points need not preserve ASS.

Checked geometry results include:

- Removing future rows preserves ASS; each rectangle has a witness on a side
  incident to either chosen corner.
- The standard GreedyASS sweep projects old points whose rectangle with the
  current request is empty. It produces an ASS set, and every legal current-row
  completion contains its points. Consequently its minimum completion is unique.
- An independent exhaustive minimum-row implementation is also verified.
  Enumeration time is not geometric point cost; the sweep is the primary algorithm.
- Online algorithms see only the old point set and current request. Their total
  row cost is exactly the cardinality of the resulting offline geometric solution.
  Prefix execution is independent of the continuation.
- Conversely, any bounded offline ASS solution can be exposed as legal rows with
  exactly the same cost. A minimum offline geometric solution exists, and every
  solution costs at least the number of requests.
- Touches forming rooted connected regions of a **fixed** BST have an ASS view.

The [offline equivalence abstract](RotationBST/Arboral/Equivalence/Abstract.lean)
now connects these point sets to actual BST executions:

- ASS cardinality is **exactly** the cost of a rooted-subtree execution when its
  initial tree is free. A rooted operation visits its request and rearranges a
  connected region while preserving the exact inorder fringe.
- A rotation execution with `R` rotations and `m` requests gives an ASS solution
  with at most `2R + m` points. A pointer execution of cost `C` gives at most `6C`.
- An ASS solution of size `G` has a pointer realization of cost at most `33G`,
  with a future-dependent initial tree.
- From any prescribed initial shape on `n` keys, it has a rotation execution
  with normalized cost at most `2n + 99G`. No final shape is prescribed.

The proof constructs next-touch treaps offline. It proves that heapifying the
active region leaves every untouched fringe subtree intact; equal priorities
need no arbitrary tie-breaking assumption. The reverse direction maintains a
latest-touch heap and obtains ASS views of rooted-region executions. The lazy
rotation normal form supplies small regions and charges deferred work once.

**The online ASS-to-BST conversion is still missing.** The future-priority
construction is not causal, even when the supplied points came from GreedyASS.
Complete split hierarchies now have a concrete linear-total-cost implementation.
Its integration into a causal geometric simulation remains necessary; the
existing causal rotation-to-pointer simulator does not supply that integration.
The last-touch priority update and the required parent-boundary touches are now
proved in [Online/LastTouch/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Results/Abstract.lean).
Canonical root supernodes are now defined as all maximal last-touch keys in an
interval. They are nonempty on every nonempty interval; legal rows touch the
supernode boundaries of gaps they enter, and newly touched keys become exactly
the interval’s new root supernode. These definitions use only recorded history.
See [Supernode/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Results/Abstract.lean).
Supernode shapes can now carry arbitrary untouched gap subtrees: every
key-only rotation lifts at identical cost, preserves the ordered fringe, and
accesses the correct full-tree rank after accounting for gap sizes. Complete
split hierarchies therefore retain their linear bound in supernode keys,
independently of the sizes of their gaps. See
[Embedding/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Embedding/Results/Abstract.lean).
An equal-priority layer invariant now links canonical supernodes with recursively
heap-ordered gaps. Lifted rotations preserve the entire last-touch heap, absolute
active keys, and gap offsets. Promoting the active keys after rearrangement
now establishes the current-row layer and exactly the new canonical supernode;
intervals missed by a row retain their old layers and canonical keys. These
local update lemmas do not yet construct the full causal simulation. See
[Layer/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Layer/Results/Abstract.lean).
The smaller-side logarithmic charges also have a checked linear bound for every
split hierarchy, in [Online/Split/Abstract.lean](RotationBST/Arboral/Online/Split/Abstract.lean).
The endpoint-based split implementation and its linear hierarchy bound are now
verified below; the last-touch supernode simulation is still missing.
The concrete 2–3–4 representation is started in
[Online/Split/Multiway/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Results/Abstract.lean):
its binary encoding preserves key count, balanced size bounds are checked, and
root sibling borrowing/merging preserves balance with at most four rotations.
Repairs of the first and last child also cover 3- and 4-node parents, preserving
balance in at most five rotations; merges consume exactly one node inside these
larger parents. Their interface is
[Multiway/Edges/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Edges/Results/Abstract.lean).
The computed context reassembly preserves exact local rotation counts and node
reserve decreases at arbitrary depth. Same-height replacements preserve global
balance; root contraction is explicitly excluded from that balance lemma. See
[Multiway/Context/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Context/Results/Abstract.lean).
Minimum extraction is now executable and checked: it exposes rank zero using
actual rotations, removes exactly one key, preserves balance, and costs at most
seven rotations per level. A wide root retains its height; a minimal root can
shrink by one level. See
[Multiway/Extract/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Extract/Results/Abstract.lean).
Balanced joins are now executable in both directions, with at most three
rotations per level of height difference and at most one level of root growth.
The splitter uses a join with root absorption: equal-height minimal roots merge
into a full root with zero rotations and no height increase. Any join that does
increase height creates a minimal root. These local height invariants are in
[Join/Compact/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Join/Compact/Results/Abstract.lean).
The joins support an arbitrary-rank splitter that exposes the requested key and
retains balanced multiway representations of both remaining intervals, with
exact sizes and a certified rotation count. Neither output is taller than the
input, and splitting takes at most fourteen rotations per input level. The
cost proof charges joins to increases in the rebuilt intervals’ heights. See
[Multiway/Join/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Join/Results/Abstract.lean)
and [Multiway/Partition/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Multiway/Partition/Results/Abstract.lean).
These operations use the ordinary binary encoding; the smaller-side finger
bound for splitting remains unfinished.
The minimum-finger spine now has a checked reconstruction and search invariant.
Choosing the nearer endpoint crosses at most
`Nat.log2 (min rank (size - 1 - rank) + 1) + 1` multiway levels; see
[Split/Finger/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Results/Abstract.lean).
This bounds levels in the stored path, not yet BST rotations for a full split.
A concrete minimum-finger comparison BST is now constructed by rotations, with
initialization cost at most three rotations per key. Its root is the minimum;
the off-path subtrees retain their internal shapes. See
[Finger/Binary/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Results/Abstract.lean).
A remainder-carrying conversion now improves the construction bound to at most
three rotations per multiway level, including before an enclosing separator.
Combining that conversion with balanced splitting preserves minimum-finger
views on both outputs in at most `23 * height` rotations, or
`23 * height + 1` with an enclosing remainder. See
[Conversion/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Conversion/Results/Abstract.lean)
and [Partition/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Partition/Results/Abstract.lean).
Finger ascent now computes a balanced containing interval of height at most
`Nat.log2 (rank + 1) + 1`, with an exact reconstruction of the untouched outer
context. Its view plus the retained remainder equals the original finger BST.
Splitting that interval therefore exposes the requested key in at most
`23 * (Nat.log2 (rank + 1) + 1) + 1` rotations in the full input tree. See
[Locate/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Locate/Results/Abstract.lean).
A direct join now attaches a taller right sibling while retaining the left
finger, in at most four rotations per level of height difference. The same
bound holds before an arbitrary enclosing remainder. For a one-level deficit,
absorbing a non-full sibling removes one enclosing multiway node; a full sibling
restores the parent height. See
[Join/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Join/Results/Abstract.lean).
The repairs now compose through the full enclosing context, stopping once the
expected height is restored. The complete minimum-finger splitter returns two
balanced finger trees with exact interval sizes and a certified rotation count.
See [Repair/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Repair/Results/Abstract.lean)
and [Finger/Partition/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Partition/Results/Abstract.lean).
The whole repair cascade now has a checked amortized bound: with two credits
per multiway node, a one-level deficit costs at most 16, and an initial height
gap `g` costs at most `6 * g + 26`. Propagating steps each remove an enclosing
node that pays their rotations. The local splitter’s node allocation is now also charged: a complete
minimum-finger split satisfies
`cost + 2 * (left.nodes + right.nodes) <= 2 * input.nodes +
85 * (Nat.log2 (rank + 1) + 1) + 29`. This includes all context repairs and
retains both output reserves for subsequent splits. A shared two-endpoint representation is now constructed around a median root:
the left side stores a minimum finger and the right side a maximum finger,
with side sizes within a factor of two. Construction uses at most twenty
rotations per input level, and the root-selected endpoint distance is at most
twice the nearer-end distance (with the usual additive one). See
[TwoEnded/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Results/Abstract.lean).
For split maintenance, a height-based invariant is also verified: the side
heights differ by at most one. Constructing this form around the existing root
costs at most `6 * height`; its chosen endpoint satisfies
`log2(distance + 1) <= 2 * log2(nearer distance + 1) + 2`. An executable
rebalance restores this invariant in at most `12 * max(side heights) + 6`
rotations and does nothing when the invariant already holds. See
[Height/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Height/Results/Abstract.lean).
The maximum-finger local splitter now has exact rotation witnesses, costing
at most `23 * height`, or `23 * height + 1` when retaining an enclosing
smaller-key remainder. A last-child context identity identifies that local
view inside the original finger tree without additional rotations. See
[Maximum/Partition/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Maximum/Partition/Results/Abstract.lean).
Maximum-finger localization now retains the original rightmost context and
finds a balanced interval of height at most `log2(distance + 1) + 1`.
Exposing its requested key in the full input tree costs at most
`23 * (log2(distance + 1) + 1) + 1`, including the enclosing remainder
and its rank offset. See
[Maximum/Locate/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Maximum/Locate/Results/Abstract.lean).
Maximum-finger sibling attachment is also verified: joining a shortened
interval to a taller left sibling preserves its finger view in at most four
rotations per level of height difference, including with an enclosing remainder.
The result is balanced and has the sibling’s height or one additional level. See
[Maximum/Join/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Maximum/Join/Results/Abstract.lean).
Maximum-finger context repair now has an executable cascade, exact rotation
witnesses, and balance preservation. It stops once the focused interval regains
its expected height; the unchanged outer context is retained without rotations.
See [Maximum/Repair/Context/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Maximum/Repair/Context/Results/Abstract.lean).
The cascade now also has amortized node accounting: with two credits per
multiway node, a one-level deficit costs at most 16 and an initial height gap
`g` costs at most `6 * g + 26`. The complete maximum-finger splitter combines
localization, exposure, and repair; both outputs are balanced reusable maximum
views, and their sizes are exactly `size - 1 - distance` and `distance`. Its
amortized bound is `cost + 2 * (left.nodes + right.nodes) <=
2 * input.nodes + 85 * (log2(distance + 1) + 1) + 29`. See
[Maximum/Partition/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Maximum/Partition/Results/Abstract.lean).
The endpoint splitters are now combined into shared-root exposure, with exact
rotations, correct output sizes, and balanced stored pieces. Exposure retains
both output node reserves and costs at most
`170 * log2(min(rank, size - 1 - rank) + 1) + 285` amortized. See
[TwoEnded/Expose/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Expose/Results/Abstract.lean).
This exposure bound excludes output normalization. Normalization and the complete
shared split are now executable and verified: both outputs (including empty
intervals) regain the shared height invariant, with exact rotations and sizes.
Normalizing a single-finger piece costs at most nine times its height; new
node reserves are bounded by the normalization cost plus two nodes. See
[TwoEnded/Normalize/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Normalize/Results/Abstract.lean).
Height-lowering repair cascades now have a checked reserve-release lemma for
both endpoints. If the retained side loses height, the sum of both output
node counts plus the original height is at most the input node count plus
`30 * (log2(distance + 1) + 1) + 4`. A one-level cascade that reaches the root
removes exactly one node per ancestor. These bounds provide the reserve needed
to pay for shared-root rebuilding. The retained side’s height loss is also
bounded by `log2(distance + 1) + 1`; consequently normalization allocates at
most `3 * log2(chosen distance + 1) + 10` nodes beyond the exposed outputs,
independently of the old total height. The complete shared split now has a
checked amortized bound including every normalization and rebuilding rotation:
`cost + 14 * (left.nodes + right.nodes) <= 14 * input.nodes +
3000 * (log2(min(rank, size - 1 - rank) + 1) + 1)`. Both output reserves
are retained. Recursively composing the splits now realizes every same-size
complete hierarchy from a valid shared interval with exact rotations and total
cost at most `6014 * size`. Initialization from an ordinary balanced multiway
encoding costs at most an additional `6 * height`. See
[TwoEnded/Hierarchy/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Hierarchy/Results/Abstract.lean).
Partial split execution is now verified as well: plans may stop at any interval,
retaining its shared state for later splits. Exact rotations, validity of all
retained intervals, and a linear total bound including their unspent reserves
are proved in
[TwoEnded/Partial/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Partial/Results/Abstract.lean).
Current finite sets of supernode ranks now generate executable partial plans.
Selection exposes exactly the requested ranks in sorted order, retaining valid
intervals between them and preserving the linear bound with unspent reserves.
See [TwoEnded/Select/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Select/Results/Abstract.lean).
Full-tree touches can now be pulled back to key-only supernode ranks. The
rank embedding is strictly increasing; its selected image is exactly the row’s
intersection with that supernode’s active keys, and cardinalities agree. See
[Supernode/Ranks/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Ranks/Results/Abstract.lean).
A lifetime budget now covers arbitrary interleavings of later partial plans on
retained leaves. Every split pays from its interval’s existing credit, and
`total cost + remaining credit <= 6014 * initial size` holds across any number
of refinements, with exact rotations and preserved validity. No fresh linear
allowance is given on each row. See
[TwoEnded/Lifetime/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/TwoEnded/Lifetime/Results/Abstract.lean).
New supernodes can now be initialized from any key-only shape. A computed
balanced target exists for every size; actual reshaping uses at most twice the
number of keys in rotations. Creation plus its entire lifetime splitting credit
costs at most `6016 * promoted keys`. The lifted theorem preserves gap trees
and offsets and establishes the current-row layer. See
[Supernode/Create/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Create/Results/Abstract.lean).
A concrete nested state now stores a shared split representation at each
supernode and a finite ordered child list with exactly one entry per gap. Its
recursive canonical invariant implies the full last-touch heap property, with
exact child offsets. A represented empty-history state is constructed for every
universe size. See
[Supernode/Nested/Results/Abstract.lean](RotationBST/Arboral/Online/LastTouch/Supernode/Nested/Results/Abstract.lean).
The nested invariant now has a locality theorem: a row missing an interval
preserves its entire represented subtree. Promoting exactly an assembled layer’s
active keys also preserves all represented children and establishes the new
canonical supernode, using exact child-hole membership and offsets.
The rank interface also proves that entering an embedded child gap forces
each existing adjacent parent key into the legal row, for arbitrary parent
shapes and gap subtrees.
Consecutive surviving parent intervals now have a concrete retention operation:
it slices the child list and preserves the full recursive representation,
including canonical roots and absolute child offsets, for any valid replacement
key shape of the required size.
Parent selection now materializes the shared split hierarchy as an exposed
region with canonical nested subtrees at its holes. Empty parent intervals
retain their original child gap. The implementation has an exact full-BST
rotation proof with the splitter's cost, independent of attached child sizes.
The selected region now provably exposes exactly the row's intersection with
the old parent keys. Child-region attachment has an executable composition
operation with exact rotation counts and preservation of the hole invariants.
Recursive row extraction is now implemented and proved to expose exactly the
legal row within its interval, preserving canonical nested states in every
hole and recording exact rotations. Entering a subtree forces a parent key
to be exposed, which makes every recursive hole strictly smaller and proves
that the size-based recursion bound suffices. Rebuilding is now implemented
and proved to produce the next canonical stored state while preserving the
ordered nested children. Its rotation cost plus the newly allocated splitting
credit is at most 6016 times the exposed-key count. Total nested potential
accounting is now proved: extraction spends only existing credit, and the
concrete next-state update satisfies `rotations + new credit <= old credit +
6016 * row cardinality`. Request-visiting root accesses and sequence composition
are also proved, charging all deferred restoration work. Every geometric run
admits an execution with at most `6018 * row point count + 6016 * initial size`
rotations. The causal choices are now packaged as a single BST `Algorithm`
for each supplied initial tree, chosen before the request sequence, with the
same bound simultaneously for every valid sequence. A first-request shape
conversion strengthens this to one policy for all initial trees of size `n`,
with rotation cost at most `6018 * row point count + 6018 * n`. The top-level
`online_bst` theorem exposes this quantifier order explicitly. The normalized
request-plus-rotation bound is `6019 * row point count + 6018 * n`; a fixed
causal pointer strategy has a checked linear bound as well.
BST search in this concrete minimum-finger view now costs at most
`5 * Nat.log2 (rank + 1) + 6` edges. A concrete splay realizes the same bound
in rotations. That access theorem does not assert preservation of the finger
representation. Local first-child repairs now preserve the concrete finger view
in at most three rotations, including with any larger-key remainder appended.
See [Finger/Binary/Repair/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Repair/Results/Abstract.lean).
Minimum extraction now composes those repairs while preserving the finger
encoding of the remaining balanced tree. It removes exactly one key and costs
at most three rotations per multiway level, also inside an enclosing interval.
See [Finger/Binary/Extract/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Extract/Results/Abstract.lean).
Repeated minimum extraction now has a checked amortized bound of
`12 * initial nodes + 3 * extractions`; draining all keys takes at most
`15 * initial keys` rotations. The proof uses height-weighted first-child credits
and retains the finger representation between deletions. See
[Extract/Amortized/Results/Abstract.lean](RotationBST/Arboral/Online/Split/Finger/Binary/Extract/Amortized/Results/Abstract.lean).
Arbitrary-key splitting and complete hierarchies now use the shared two-endpoint
implementation above; their application to geometric supernodes supplies the
causal online simulation and its nested potential bound.

For Tango, the library defines the reference-tree regions, interleave quantity,
and online preference-switch count on unlabelled shapes. It proves that total
switches equal the interleave quantity, bounds every downward path by reference
height, and verifies the size and height of perfect reference trees. The reference
node itself belongs to its left region, as in the Tango paper; first observations
initialize preferences without counting as switches.

The [Wilber lower-bound abstract](RotationBST/Tango/LowerBound/Abstract.lean)
proves `IB ≤ 2G` for every ASS solution, `IB ≤ 4R + 2m` for every rotation
execution, and `IB ≤ 12C` for every pointer execution, for any reference tree
on the same universe. Its proof establishes that transition points remain fixed
until touched, that different reference cuts have distinct transition points,
and that a mismatch potential pays for all interleavings. Initial preferred
settings add at most `n` to the switch count.

The executable preferred-path decomposition is also checked: its paths partition
all reference keys without duplicates, have no empty components, and have length
at most the reference height. After a request updates preferences, the requested
key belongs to the component starting at the reference root. Every computed path
is a downward reference path. Its depth suffix is an interval in auxiliary key
order, with two extreme keys selecting exactly that suffix; these statements are
in [Paths/Geometry/Results/Abstract.lean](RotationBST/Tango/Paths/Geometry/Results/Abstract.lean).

The splay-based auxiliary operations now have checked costs in the full BST:
auxiliary rotations preserve every attached fringe subtree, and executable
auxiliary splaying has exactly the lifted rotation count. Prefix/suffix cuts and
front/back joins cost at most `3 log₂ H + 1` amortized rotations; interior cuts
cost at most `6 log₂ H + 2`, and interior joins at most `8 log₂ H + 2`, where `H`
bounds the participating auxiliary nodes. The potential counts only auxiliary
nodes, independently of attached subtree sizes. Statements are in
[Auxiliary/Abstract.lean](RotationBST/Tango/Auxiliary/Abstract.lean) and
[Auxiliary/Interval/Abstract.lean](RotationBST/Tango/Auxiliary/Interval/Abstract.lean).

The whole BST now has an explicit marked representation. Its invariant records
the preferred-path partition and identifies the root preferred path. Initial
singleton components satisfy this invariant with zero global potential.
A stronger maintenance invariant additionally fixes the ordered nesting of
components to the reference marking. A regression test exhibits a state that
satisfies the partition/root condition but has incorrect lower nesting. Canonical
reference markings satisfy the stronger invariant for every request history;
auxiliary rearrangements and root access preserve it. The statements are in
[State/Nesting/Results/Abstract.lean](RotationBST/Tango/State/Nesting/Results/Abstract.lean).
The nesting signature determines subtree sizes and all component key sets, so
matching the reference nesting alone establishes the full maintenance invariant.
It also matches attached components at identical absolute key offsets. Every nonempty reference fringe component
can be located in the actual maintained BST together with its marked boundary
context at that exact offset, distinguishing repeated unlabelled subtree shapes.
Local operations embedded there retain exactly their rotation count
and global potential change; see
[State/Context/Results/Abstract.lean](RotationBST/Tango/State/Context/Results/Abstract.lean).
Auxiliary rotations preserve all marked fringe subtrees and component key sets;
root-component access costs at most
`3 log₂(height reference) + 1` amortized rotations against the full-state
potential. Prefix, suffix, and interior cuts and joins also produce actual
marked states with the corresponding bounds. Their public statements are in
[State/Abstract.lean](RotationBST/Tango/State/Abstract.lean) and
[State/Updates/Abstract.lean](RotationBST/Tango/State/Updates/Abstract.lean).

An executable preference-update log now records changed node keys and their old
and new preferences, in root-to-request order. It has no repeated node within a
request, skips unchanged choices, and preserves its prefix when requests are
appended. Its total length is exactly `preferenceChanges`, at most `IB + n`, and
at most `4 R + 2 m + n` against every offline rotation execution. See
[Preferences/Updates/Results/Abstract.lean](RotationBST/Tango/Preferences/Updates/Results/Abstract.lean).

Nesting edits now have checked realizations: cutting any nonempty proper active
key interval groups exactly its consecutive fringe slots into a new component;
merging expands the selected component's slots. These realizations work from
any auxiliary shape with the same nesting. At a reference-component root, a
first preference setting and either direction of a preference switch are also
realized by actual rotations. A switch costs at most
`14 log₂(L + R + 1) + 4` amortized rotations, including empty-child cases, where
`L` and `R` are the two child auxiliary sizes. See
[State/Nesting/Edits/Results/Abstract.lean](RotationBST/Tango/State/Nesting/Edits/Results/Abstract.lean).

Mark changes and preference switches can now occur anywhere inside a preferred
component, through arbitrarily many unmarked ancestors. A switch costs at most
`14 log₂ H + 4` when both endpoint component sizes are at most `H`; there is no
additional depth factor. The exact before/after nesting and actual rotations are
proved in [State/Nesting/Edits/Path/Results/Abstract.lean](RotationBST/Tango/State/Nesting/Edits/Path/Results/Abstract.lean).

These operations now transfer through arbitrarily many marked boundaries as
well. An indexed replacement theorem changes exactly the intended fringe entry;
a recursive simulation theorem transports it between different auxiliary shapes
without extra rotations or potential cost. Whole-tree preference switches keep
the same `14 log₂ H + 4` bound, and first-time joins keep their local bound; see
[State/Nesting/Edits/Whole/Abstract.lean](RotationBST/Tango/State/Nesting/Edits/Whole/Abstract.lean).

Rank-based reference updates and their ordered application are now executable.
They preserve the fixed reference tree and the condition that every component
is a downward path. This proves the reference-height component bound throughout
an update log. The actual rotation realizations compose with telescoping global
potential, costing at most `updates.length * (14 log₂(height reference) + 4)`;
see [State/Preferences/Results/Abstract.lean](RotationBST/Tango/State/Preferences/Results/Abstract.lean).

The generated log now provably produces exactly the canonical marking for the
extended history. Each update phase is followed by an actual access to the
requested key, and the complete run preserves the full maintenance invariant.
A single online policy is fixed before the request sequence is chosen. Against
any offline execution with `R` rotations and `m` requests on `n` keys, its total
cost is at most

```
(56 log₂ H + 16) (R + m) + (14 log₂ H + 4) n,
```

where `H` is the reference-tree height. For a perfect reference on `2^h - 1`
keys, `H = h`. For arbitrary `n`, the executable `balanced n` constructor
produces exactly `n` keys with `H ≤ Nat.log2 n + 1`; the coefficient is therefore
bounded by `56 log₂(Nat.log2 n + 1) + 16`, with a separate initialization term.
See [Algorithm/Abstract.lean](RotationBST/Tango/Algorithm/Abstract.lean).

Component reconstruction, root-component splaying, all three interval cuts,
and all three component joins now have
executable definitions with checked exact rotation counts and global-potential
bounds. The earlier boundary-exposure, cut, and join proofs use these concrete
operations. The executable interval-cut and fringe-merge dispatchers also
realize exact nesting edits across different auxiliary shapes; see
[State/Nesting/Edits/Algorithm/Results/Abstract.lean](RotationBST/Tango/State/Nesting/Edits/Algorithm/Results/Abstract.lean)
and [State/Executable/Abstract.lean](RotationBST/Tango/State/Executable/Abstract.lean).
Fringe lookup and local editing are also executable: a computed context selects
the indexed occurrence, preserves other attached components, and transfers the
local rotation count and potential difference exactly. The simulation theorem
also covers different actual/reference auxiliary shapes; see
[State/Context/Lookup/Results/Abstract.lean](RotationBST/Tango/State/Context/Lookup/Results/Abstract.lean).
Executable component paths now compose these edits across arbitrarily many
marked boundaries. The resulting nesting follows the reference path, and the
amortized bound remains that of the edited component, with no depth factor; see
[State/ComponentPath/Results/Abstract.lean](RotationBST/Tango/State/ComponentPath/Results/Abstract.lean).
Reference-edge marks, unmarks, and preference switches within a component now
compile to executable cuts and merges using computed active-rank offsets. Their
checked bounds remain `6 log₂ H + 2`, `8 log₂ H + 2`, and `14 log₂ H + 4`,
respectively; see
[State/Nesting/Edits/Path/Algorithm/Results/Abstract.lean](RotationBST/Tango/State/Nesting/Edits/Path/Algorithm/Results/Abstract.lean).
Reference-key lookup now computes the node context and its component address.
The checked address theorem specifies both the reached component and the exact
nesting effect of a replacement. The complete policy compiles each preference
update, executes the log, and splays the requested absolute key; its implementation
no longer selects realizations by classical choice. The existing execution and
competitive bounds apply to this computed policy. See the concise definitions in
[Algorithm/Request/Abstract.lean](RotationBST/Tango/Algorithm/Request/Abstract.lean)
and the checked contract in
[Algorithm/Executable/Abstract.lean](RotationBST/Tango/Algorithm/Executable/Abstract.lean).
The auxiliary primitives use amortized splaying; the paper's red-black
implementation is not formalized. Runtime for planning and reference lookup is
uncharged in the abstract BST cost model. The causal online ASS-to-BST conversion
is proved; this does not establish dynamic optimality for GreedyASS.
The executable boundary cases are in
[RotationBSTTests/Arboral.lean](RotationBSTTests/Arboral.lean).

## Scope audit and upstream submission

The causal geometric-to-BST conversion and its uniform online cost bound are
proved separately from the future-dependent offline treap construction. The
requested core results and their scope limits are recorded in
[the formalization audit](docs/formalization-audit.txt), including the precise
online quantifiers and the implemented algorithm variants.

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
- Demaine, Harmon, Iacono, Kane, and Pătraşcu, [*The Geometry of Binary Search Trees*](https://people.csail.mit.edu/mip/papers/arboral/paper.pdf), SODA 2009, Sections 2–3.
- Demaine, Harmon, Iacono, and Pătraşcu, [*Dynamic Optimality—Almost*](https://erikdemaine.org/papers/Tango_SICOMP/paper.pdf), SIAM Journal on Computing 37(1), 2007.
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
