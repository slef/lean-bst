# Library organization

This document records how `RotationBST` is organized, why, and what remains to
be done. It is the companion of the [README](../README.md) "Library layout"
section and is meant to be updated whenever a part of the library moves.

## Goal

The library is a compendium of checked knowledge about binary search trees,
organized as a textbook rather than as a list of formalized papers:

1. **Models** of BST computation and the equivalences between them.
2. **Bounds** on request sequences, upper and lower, and the implications
   between them, independently of any algorithm.
3. **Algorithms**, each with its definition followed by the bounds it satisfies
   and the lower bounds it is subject to.
4. **Structures**: supporting data structures used by algorithms and proofs.

Following [abstractlean](https://github.com/slef/abstractlean) and the
Complexitylib abstracts it was adapted from, every section separates the
*substance a human reads* (definitions and theorem statements, kept short and
self-contained) from the *proof engineering* that Lean checks.

## Audit before this reorganization (November 2026)

The code had grown along the needs of the proofs. The main findings:

- **Paper-shaped top level.** Directories were `Splay/`, `Arboral/`, `Tango/`,
  one per source paper, next to a handful of small concept directories
  (`Access/`, `Geometry/`, `Normalization/`, `WorkingSet/`).
- **Misfiled content.** Wilber's interleave lower bound lived in
  `Tango/`; the rooted-region BST model and the lazy-simulation skeletons lived
  in `Arboral/View` and `Pointer/Lazy`; 167 files of finger/multiway split trees
  lived in `Arboral/Online/Split` although they are not geometric; the splay
  working-set proof lived in the generic `WorkingSet/` directory; the generic
  unified bound was defined in namespace `Splay`.
- **Diluted reading interface.** 208 of 560 files were named `Abstract.lean`.
  About 35 of them were textbook-level statements with short allowlists; the
  rest were internal lemma contracts (`…/Results/Abstract.lean`, allowlists of
  30–60 modules) or internal definitions. The book and the README treat every
  `Abstract` module as reading interface, so the human surface was blurred.
- **Two bridge conventions.** The older sections used `Abstract.lean` +
  `AbstractBridge.lean` with one-line delegations; the geometric and Tango
  sections imported proof modules directly into their abstracts.
- **Naming collisions.** `Geometry/` meant rotation connectivity, not arboral
  geometry; `Tango/Definitions` was mostly Wilber's interleave quantity.
- **Layering leaks.** Generic bound proofs (`Bounds/Gaps`, `Bounds/LogSum`,
  `Bounds/StaticTree/Comparison`) import splay proof modules for lemmas.

Nothing was mathematically wrong; every module built and passed the audits.

## Target structure

```
RotationBST/
  Audit/            #check_bst_abstract and its LICENSE
  Models/           Part I: models and equivalences
    Rotation/       shapes, rotations, root accesses, executions
      Connectivity/   any shape reaches any shape in 2n rotations
      Existence/      exactly the existing keys can be served
    Labelled/       labelled BSTs, ordering invariant, Mathlib bridge
    Online/         online algorithms, rotation/total cost, dynamic optimality,
                    reset of an algorithm to a fixed initial tree
    Pointer/        single-cursor machine, eager and lazy simulations,
                    causal online transformer (Lazy/Online)
    Region/         rooted-region (touched-subtree) model, skeletons, regions
    Geometric/      points, arborally satisfied sets, online and offline
                    geometric algorithms, rooted rows of a fixed tree
    Equivalence/    offline ASS <-> region <-> rotation <-> pointer
  Bounds/           Part II: bounds and their relations
    WorkingSet/     working-set numbers and property
    Abstract.lean   frequency entropy, static optimality, static finger
    Unified/        the 1985 fixed-finger unified charge
    Implications/   working set => static optimality => static finger
    StaticTree/     fixed-tree benchmark and the entropy lower bound
    Interleave/     Wilber's interleave quantity and lower bound
    LazyFinger/     fixed-tree distances, weighted characterization, separations
    WeightedFinger/ weighted dynamic-finger benchmark
    ConditionalEntropy/ transition entropy and its obstruction
    Normalization/  request charges versus rotation charges
  Algorithms/       Part III: algorithms, definitions then bounds
    MoveToRoot/
    Splay/          algorithm, potential, access lemma, nine ST85 theorems,
                    updates, conditional splay, scanning, pointer version
    GreedyASS/      geometric sweep, potential analysis, lazy/weighted-finger bounds
    OptimalLazyFinger/ exact dynamic program and annotated cubic work
    MultipleTrees/  static linked searches with a space/query tradeoff
    Simulation/     causal geometric-to-BST simulation (last-touch supernodes)
    Tango/          preferred paths, preference changes, auxiliary trees,
                    marked-tree state machine, executable policy, O(log log n)
  Structures/       Appendix: supporting structures
    Treap/          next-touch treaps for the offline construction
    SplitTree/      multiway finger trees and split hierarchies
    FingerHand/     multifinger representation supporting lazy-finger simulation
    PrefixSum/      interval sums for the optimal-tree dynamic program
    WeightedSearch/ search trees used by the multiple-tree structure
```

Cross-part imports are allowed in one direction only: `Models` imports nothing
above it; `Bounds` may import `Models`; `Algorithms` may import both;
`Structures` may import `Models` and `Algorithms/Splay`. A statement about a
model whose proof uses an algorithm (for example, existence of accesses via
move-to-root) keeps its statement in `Models` and its bridge imports the
algorithm; this is a proof dependency, not a reading dependency.

## Module taxonomy

File names carry the abstractlean roles:

| File | Role | Who reads it |
|---|---|---|
| `Abstract.lean` | Textbook surface: definitions a reader must trust, or theorem statements proved by one-line delegation. Ends with `#check_bst_abstract` when it states theorems. | Humans |
| `AbstractBridge.lean` | The single proof import of a statements abstract; a thin re-export of proof modules. Never imports its abstract. | Nobody, by design |
| `Defs.lean` | Internal definitions of a proof cluster (state machines, cost counters). Readable foundations of internal contracts only. | Proof authors |
| `Results.lean` | Internal lemma contract with `#check_bst_abstract`; allowlists may be long. | Proof authors |
| anything else | Proofs. | Lean |

Consequences:

- The book's audit (`book/scripts/build.mjs`) and the README treat exactly the
  `*.Abstract` modules as reading interface. After this reorganization that set
  coincides with the textbook surface.
- A statements `Abstract.lean` lists only readable foundations in its allowlist:
  `Abstract` modules of definitions, never `Defs`, `Results`, or proof modules.
  Long allowlists are a signal that a statement belongs in `Results.lean`.
- Surface theorems live in `<Topic>.Results` namespaces (`Splay.Results`,
  `Wilber.Results`, `Geometric.Equivalence.Results`, …). Namespaces are
  independent of paths in Lean; they were aligned with the parts in the third
  pass, and the historical `Arboral` root was renamed `Geometric` in the fourth.

## What this pass did

The first commit was purely mechanical: 551 of 560 files moved; module names
in imports, allowlists, docstring paths, README, tests, and documentation
scripts were rewritten. No definition, statement, proof, or namespace changed.

| Before | After |
|---|---|
| `AbstractAudit/` | `Audit/` |
| `Model/`, `Geometry/`, `Access/{Abstract,AbstractBridge}` | `Models/Rotation/`, `…/Connectivity/`, `…/Existence/` |
| `Access/MoveToRoot.lean` | `Algorithms/MoveToRoot/Algorithm.lean` |
| `Representation/` | `Models/Labelled/` |
| `Online/` | `Models/Online/` |
| `Pointer/` | `Models/Pointer/` |
| `Arboral/Treap/Regions/`, `Arboral/View/` | `Models/Region/`, `Models/Region/View/` |
| `Arboral/{Definitions,Basic,Rectangle,Online,Offline,Static,Abstract}` | `Models/Geometric/…` |
| `Arboral/Equivalence/` | `Models/Equivalence/` |
| `Arboral/Treap/` (rest) | `Structures/Treap/` |
| `Arboral/Online/Split/` | `Structures/SplitTree/` |
| `Arboral/Online/LastTouch/` | `Algorithms/Simulation/` (headline at `Simulation/Abstract.lean`) |
| `Arboral/{Greedy,Sweep}` | `Algorithms/GreedyASS/` |
| `WorkingSet/Abstract` | `Bounds/WorkingSet/Abstract` |
| `WorkingSet/` (proofs) | `Algorithms/Splay/WorkingSet/` |
| `Normalization/` | `Bounds/Normalization/` |
| `Bounds/*.lean` proofs | `Bounds/Implications/` |
| `Tango/{Definitions,Interleave,Bounds,Wilber,Transition,LowerBound}` | `Bounds/Interleave/…` (headline at `Interleave/Abstract.lean`) |
| `Tango/` (rest) | `Algorithms/Tango/` |
| `Splay/` | `Algorithms/Splay/` |
| every `X/Results/Abstract.lean` | `X/Results.lean` |
| internal `X/Abstract.lean` in SplitTree, Simulation, Tango/State, Tango/Paths/Geometry | `X/Defs.lean` or `X/Results.lean` |

## Second pass: content refinements done

After the mechanical move, a second commit made these content changes, each
checked by a full build:

- `Models/Geometric/Definitions/Abstract.lean` now holds only the geometric
  model (`Point`, `ASS`, `Completion`, `GreedyRow`, `Solution`); the executable
  sweep (`Visible`, `greedySweep`, `greedy`) moved to
  `Algorithms/GreedyASS/Algorithm/Abstract.lean`, and the GreedyASS theorems
  to `Algorithms/GreedyASS/Abstract.lean` with their own bridge.
- `Bounds/Interleave/Definitions/Abstract.lean` now holds only Wilber's
  quantity (`regions`, `alternations`, `interleave`, `switch`); Tango's
  `changes`, `changeCost`, `height`, `perfect`, `DownwardPath` moved to
  `Algorithms/Tango/Definitions/Abstract.lean`, with the accompanying lemmas
  in `Algorithms/Tango/Changes.lean`.
- The online equivalence `online_bst` moved from the geometric results to
  `Models/Equivalence/Abstract.lean`, next to the offline equivalences.
- Move-to-root follows the splay layout: `Algorithm/Abstract.lean`
  (definition), `Correctness.lean`, `Abstract.lean` (audited statement and the
  bundled online algorithm).
- The hubs `Models/Geometric/Abstract`, `Algorithms/Tango/Abstract`,
  `Algorithms/Simulation/Abstract`, and `Structures/SplitTree/Abstract` import
  their internal `Results` modules through an `AbstractBridge.lean`, so every
  statements abstract has exactly one proof import.
- `Algorithms/Simulation/Abstract.lean` allowlists only the seven definition
  modules its statements mention, instead of the 59 internal modules of its
  proof; the audit confirms the statements never reach the split trees.
- `RotationBST.lean` lists the reading interface part by part.

## Third pass: conventions completed

- **Bridges everywhere.** Every statements abstract imports exactly one
  `AbstractBridge.lean`. Bridges that carried proofs became named proof
  modules (`Proofs.lean`, `Labelled/Labelling.lean`, `Splay/PointerBounds.lean`)
  behind thin bridges; the Wilber, Tango, and auxiliary-tree abstracts gained
  bridges.
- **Namespaces follow the parts.** Wilber's definitions and lower bounds are
  `RotationBST.Wilber.*` (Tango modules `open Wilber`); the unified charge is
  `RotationBST.Bounds.unifiedCharge`; geometric results are split into
  `Geometric.Results` (model facts), `Geometric.Equivalence.Results`,
  `Geometric.GreedyASS.Results`, and `Geometric.Simulation.Results`. The
  `Tango` namespace of Tango's own vocabulary is unchanged.
- **Layering.** `Bounds/` no longer imports splay proof modules for lemmas:
  `logb_nat_le` lives in `Bounds/Implications/LogSum.lean` and the `1/k²`
  partial sums in `Bounds/Implications/SquareSum.lean`, both under
  `RotationBST.Bounds`.
- **Split-tree surface.** `Structures/SplitTree/Abstract.lean` states the
  finger contract (construction, minimum, search depth, splay access,
  representation, nearer endpoint) and the accounting lemma; the 2–3–4 tree,
  context, finger, and binary-view definitions it mentions are `Abstract`
  modules again.
- **Pinned audits.** Every `#check_bst_abstract` is wrapped in `#guard_msgs`
  with its root-declaration count, so adding or removing a surface statement
  without updating the pin fails the build.

## Fourth pass: the `Geometric` namespace

The geometric definitions, equivalences, GreedyASS, simulation, treap, and
split-tree modules used the paper-era root namespace `RotationBST.Arboral`.
It was renamed `RotationBST.Geometric` everywhere (317 files, identifier only;
the phrase "arborally satisfied" stays in prose). Surface namespaces are now
`Geometric.Results`, `Geometric.Equivalence.Results`,
`Geometric.GreedyASS.Results`, `Geometric.Simulation.Results`, and
`Geometric.Split.Results`. This was done before any book chapter linked to
these names.

## Fifth pass: reading-interface cleanup (November 2026)

Each change below was checked by a full build with `--wfail`.

- **Tango state on the surface.** The definitions that Tango's statements
  mention (`MarkedTree` and its components, `potential`, `initial`, `canonical`,
  `nesting`, `Maintains`) moved from three `State/*Defs.lean` files to
  `Algorithms/Tango/State/Abstract.lean`. The contract of the executable request,
  whose statement unfolds the whole state machine, moved from a statements
  abstract to the internal `Algorithm/Executable/Results.lean`.
- **Tango as an algorithm.** `Tango.Algorithm.Results.exists_competitive`
  states the `O(log log n)` bound for an ordinary `Algorithm` from every initial
  tree. The proof (`Algorithm/Online.lean`) replays the policy on the past
  requests to recover its marks, and uses the reset wrapper, which moved from the
  simulation proof to `Models/Online/Reset.lean`.
- **Pointer conversion from a prescribed start.**
  `Geometric.Equivalence.Results.ass_to_pointers_from`.
- **Proof-only definitions out of abstracts.** Wilber's transition points
  (`Bounds/Interleave/Transition/Defs.lean`), `absoluteInterleave`
  (`Wilber/Defs.lean`), `Region.project` and `ActiveHeap` (`Models/Region/Defs.lean`),
  `lastTouch` and `HistoryHeap` (`Models/Region/View/Defs.lean`).
- **Layering.** No `Models` abstract imports `Structures`. `Config.under` moved
  into the pointer-machine abstract, so no allowlist names `Pointer.Traces` or
  `Pointer.Model`. `StaticTree.depth` became `Tree.depth` in the rotation model,
  and `locate_depth` moved to splay, so `Structures` no longer imports `Bounds`.
  Remaining proof dependencies on the treap's `Heap`: `Models/Region/Holes`,
  `Models/Region/View/{Ancestor,Defs}`, `Models/Equivalence/Offline`, and
  `Bounds/Interleave/Transition/Top`.
- **Namespaces.** `Geometric.Split` became `SplitTree`; the region model
  (`Region`, `RegionStep`, `RegionExecution`) and the region operations used by
  Tango's auxiliary trees left `Geometric` for the root namespace; `greedyASS`
  left its `Results` namespace (`Geometric.greedyASS`).
- **Duplicates.** `Simulation.Results.uniform_simulation` was removed; its
  statement is `Equivalence.Results.online_bst`.

## Remaining follow-ups

1. `Bounds/StaticTree/Comparison` uses splay's `locate` zipper search and its
   pointer-trace lemma to execute a fixed tree on the pointer machine. Moving
   `locate` into `Models/Pointer` would remove the last `Bounds` → `Algorithms`
   proof dependency; it touches the splay abstract and the book's splay chapter.
2. `Models/Geometric/Offline/Optimal` proves that a minimum offline solution
   exists by running the GreedyASS sweep; a direct argument from `full_row`
   would keep the model independent of the algorithm.
3. The treap's `Heap` order is used by region-model and Wilber proofs; moving it
   to `Models` would remove the last proof dependencies on `Structures`.

## Where new results go

- A new model or equivalence: `Models/<Name>/Abstract.lean` for definitions,
  `Models/Equivalence/` for its correspondence theorems.
- A new sequence bound (dynamic finger, Wilber's second bound, …):
  definitions in `Bounds/<Name>/Abstract.lean`; relations to existing bounds in
  `Bounds/Implications/`; lower-bound theorems against the models in the same
  directory as the quantity.
- A new algorithm: `Algorithms/<Name>/Algorithm/Abstract.lean` for the
  executable definition, `Algorithms/<Name>/<Property>/Abstract.lean` for each
  bound, `Algorithms/<Name>/Abstract.lean` as the overview that the root module
  imports. Lower bounds specific to the algorithm also live there.
- Proof internals follow the `Defs.lean` / `Results.lean` / proof-file taxonomy
  and may be nested as deeply as convenient; only `Abstract.lean` files are
  shown to readers.


## Finger-bound results for the book

The finger-bound integration follows the existing four parts. General benchmarks,
characterizations, separations, and the conditional-entropy obstruction belong in
`Bounds`. The optimal-tree construction, multiple-tree search structure, and
GreedyASS guarantees belong in `Algorithms`. Their linked-search model belongs
in `Models`; prefix sums, weighted search trees, and multifinger representations
belong in `Structures`. Proofs use the current `Tree.depth` and geometric
algorithm interfaces.

A useful chapter progression is: fixed-tree distance → weighted characterization
→ separations and entropy obstruction → optimal static trees → GreedyASS's
weighted bound. The following names are the checked entry points, all under
`RotationBST`. Each linked abstract gives the exact hypotheses and conventions.

| Lazy Finger paper result | Checked entry point |
|---|---|
| Theorem 1: randomized weighted tree | [`LazyFinger.Random.Results.weighted_charge`](../RotationBST/Bounds/LazyFinger/Random/Abstract.lean) |
| Corollary 2: tree from weights | [`LazyFinger.Results.tree_for_weights`](../RotationBST/Bounds/LazyFinger/Abstract.lean) |
| Lemma 3: weights from a tree | [`LazyFinger.Results.tree_weights_two_sided`](../RotationBST/Bounds/LazyFinger/Abstract.lean) |
| Corollary 4: reverse comparison | [`LazyFinger.Results.tree_weights`](../RotationBST/Bounds/LazyFinger/Abstract.lean) |
| Theorem 5: characterization | [`LazyFinger.Results.characterization_from`, `characterization_root`, `characterization_long_sequence`](../RotationBST/Bounds/LazyFinger/Abstract.lean) |
| Theorem 6: comparison and strict separations | [`LazyFinger.Results.optimal_root_finger`](../RotationBST/Bounds/LazyFinger/Abstract.lean), [`LazyFinger.Dynamic.Results.optimal`](../RotationBST/Bounds/LazyFinger/Dynamic/Abstract.lean), [`LazyFinger.Sequential.Results.family`](../RotationBST/Bounds/LazyFinger/Sequential/Abstract.lean), [`LazyFinger.Separation.Results.family`](../RotationBST/Bounds/LazyFinger/Separation/Abstract.lean) |
| Lemma 7: conditional-entropy obstruction | [`ConditionalEntropy.Results.obstruction`](../RotationBST/Bounds/ConditionalEntropy/Abstract.lean) |
| Theorem 8: exact optimizer and cubic work | [`OptimalLazyFinger.Work.Results.root_start`](../RotationBST/Algorithms/OptimalLazyFinger/Work/Abstract.lean) |
| Theorem 9: space/query tradeoff | [`MultipleTrees.Results.sequence`](../RotationBST/Algorithms/MultipleTrees/Abstract.lean) |
| Section 1.4: simultaneous consequences | [`LazyFinger.Consequences.Results.simultaneous`](../RotationBST/Bounds/LazyFinger/Consequences/Abstract.lean) |
| Section 7: polynomial-space consequence | [`MultipleTrees.Results.polynomial_space`](../RotationBST/Algorithms/MultipleTrees/Abstract.lean) |

These are normalized counterparts of the [paper](https://arxiv.org/abs/1304.6897),
with a unit charge per request. Fixed-predecessor and root-start costs have
separate statements. The weight optimum is an infimum; the static-tree optimum
is attained. Conditional information is normalized as `m(1 + H)` so that empty
sequences, deterministic transitions, and capacity one are handled. The
optimizer's time theorem concerns its explicit annotated RAM model, not Lean
runtime. Multiple-tree query bounds exclude construction time and use the
empirical transition matrix only for preprocessing.

| Weighted Dynamic Finger paper result | Checked entry point |
|---|---|
| Theorem 3.1: leaf-oriented lazy-finger bound | [`Geometric.GreedyASS.Potential.Amortized.Results`](../RotationBST/Algorithms/GreedyASS/Potential/Amortized/Abstract.lean) |
| Theorem 4.1: ordinary lazy-finger bound | [`Geometric.GreedyASS.Performance.Results.lazy_tree`, `lazy_optimal`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |
| Theorem 4.2: weighted dynamic finger | [`Geometric.GreedyASS.Performance.Results.weighted`, `weighted_optimal`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |
| Corollary 1: dynamic finger | [`Geometric.GreedyASS.Performance.Results.dynamic`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |
| BST and pointer realizations | [`Geometric.GreedyASS.Performance.Results.bst`, `pointer`, `bst_weighted`, `bst_dynamic`, `pointer_weighted`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |

For this [paper](https://arxiv.org/abs/1810.01785), startup is an explicit linear
term. The realization statements choose one causal policy before the initial
tree, requests, and benchmark. They do not claim global dynamic optimality.

The finger-bound batch excludes ComboBST, deamortization, Weighted Dynamic Finger Theorem
4.3, Lazy Finger's unnumbered periodic-rebuilding analysis, and its concluding
conjecture. Those unfinished developments do not prevent using the results
above in the book. Existing book chapters and interactive figures are preserved;
the theorem map supplies the entry points for expanding them.


## Deamortization results for the book

The second integration adds the abstract transformation and its Splay applications
from [De-amortizing Binary Search Trees](https://arxiv.org/abs/1111.1665).
The chapter can now follow a complete chain: weighted stacks → heavy paths →
bounded-depth simulation → scheduled responses → adaptive Splay bounds.
The transformation and its algorithm interfaces belong in `Algorithms`;
pop-tarts and heavy-path representations belong in `Structures`. The labelled
cursor, replay, and pointer-detour lemmas remain in `Models`. Depth continues
to use the existing `Tree.depth` interface.

Start with `Deamortization.Algorithm.Results.implementation_exists`. For any
certified online rotation algorithm and nonempty saved tree, it constructs one
`Implementation` before any request sequence or comparison bound is selected.
Its `correct` field provides actual key visits, legal single-finger replay,
response costs, and the worst-case guarantee. Its `causal` field certifies that
extending the requests preserves both the emitted instruction and cost prefixes.
The following entry points are all under `RotationBST`.

| Book topic | Checked entry point |
|---|---|
| Weighted stacks and local pointer operations | [`PopTart.Chocolate.Results`](../RotationBST/Structures/PopTart/Chocolate/Abstract.lean) |
| Simulation with bounded intermediate depth | [`Deamortization.Weighted.Results.simulation`, `transform`](../RotationBST/Algorithms/Deamortization/Weighted/Abstract.lean) |
| Serving a request while retaining pending source work | [`Deamortization.Window.Results.serve`](../RotationBST/Algorithms/Deamortization/Window/Abstract.lean) |
| Scheduled response costs and prefix causality | [`Deamortization.Scheduler.Results.run_spec`, `run_served`, `run_prefix`](../RotationBST/Algorithms/Deamortization/Scheduler/Abstract.lean) |
| Abstract transformation, including sequence-dependent offline sources | [`Deamortization.Finger.Results.deamortize`](../RotationBST/Algorithms/Deamortization/Finger/Abstract.lean) |
| Online rotation-algorithm instance of Theorem 6 | [`Deamortization.Algorithm.Results.implementation_exists`](../RotationBST/Algorithms/Deamortization/Algorithm/Abstract.lean) and [`Algorithm.Implementation`](../RotationBST/Algorithms/Deamortization/Algorithm/Definitions/Abstract.lean) |
| Startup-inclusive cost and transfer of source bounds | [`Deamortization.Algorithm.Results.total_bound`, `transfer`](../RotationBST/Algorithms/Deamortization/Algorithm/Abstract.lean) |
| Conditional preservation of dynamic optimality | [`Deamortization.Algorithm.Results.dynamic_optimal`](../RotationBST/Algorithms/Deamortization/Algorithm/Abstract.lean) |
| One deamortized Splay program | [`Splay.Deamortization.Results.implementation_exists`](../RotationBST/Algorithms/Splay/Deamortization/Abstract.lean) |
| Scanning, balance, and working set | [`Splay.Deamortization.Results.scanning`, `balance`, `working_set`](../RotationBST/Algorithms/Splay/Deamortization/Abstract.lean) |
| Static comparisons with coverage | [`Splay.Deamortization.Results.static_optimality`, `static_finger`](../RotationBST/Algorithms/Splay/Deamortization/Abstract.lean) |
| Static comparisons allowing unused keys | [`Splay.Deamortization.Results.static_optimality_general`, `static_finger_general`](../RotationBST/Algorithms/Splay/Deamortization/Abstract.lean) |

For `n` keys, setup costs at most `16n` pointer operations. Responses cost
at most `79360` times the source's normalized cost (`requests + rotations`),
and each response costs less than `251 + 195 log₂(n)`. Setup is separate from
the response list and is included by `total_bound`. These constants are
explicit witnesses, not optimized estimates. The scan theorem bounds the
complete setup-plus-scan cost by `1111056n`.

Every Splay comparison applies to the same implementation and completed run.
The sharper static-tree and static-finger bounds require that the sequence
access every key. The general entropy and static-finger versions remove that
coverage premise and retain an `n(1 + floor(log₂ n))` startup term. The
working-set theorem also states its startup term explicitly. Nonempty initial
trees and in-range requests are hypotheses, not implicit conventions.

This is the abstract BST-operation result of Theorem 6. It does not establish
Theorem 7's bounds on private computation, auxiliary storage, or execution on
a finite-word pointer machine. The source theorems for Cole's Splay dynamic
finger bound, key-independent optimality, and multi-splay applications are
also still outstanding. The conditional dynamic-optimality theorem does not
assert that Splay, or any other supplied algorithm, is dynamically optimal.
The finite-word controllers and unfinished arrival machinery stay on the
formalization worktree; they are not required to use this chapter's results.

The integration includes 23 existing regression modules. They cover weighted
stack operations, heavy-path updates, interruption depths, replay, scheduling,
empty-input accounting, repeated singleton requests, causal prefixes, and a
single Splay scan compared simultaneously with all static trees and fingers.
The whole-library axiom audit remains part of the default build.
