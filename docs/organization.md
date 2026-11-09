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
3. **Classical search trees** that do not adapt to the requests: static,
   rank-balanced, weight-balanced and random trees (planned; see entries 4–9 of
   [ROADMAP.md](../ROADMAP.md)).
4. **Algorithms** that adapt, each with its definition followed by the bounds it
   satisfies and the lower bounds it is subject to.
5. **Structures**: supporting data structures used by algorithms and proofs.

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
    Implications/   working set => static optimality => static finger,
                    dynamic finger => static finger => logarithmic
    DynamicFinger/  dynamic-finger sum and property; DF <= 2 SF + start term
    Logarithmic/    the baseline m(1 + log n) and its property
    StaticTree/     fixed-tree benchmark and the entropy lower bound
    Interleave/     Wilber's interleave quantity and lower bound
    LazyFinger/     fixed-tree distances, weighted characterization, separations
    WeightedFinger/ weighted dynamic-finger benchmark
    ConditionalEntropy/ transition entropy and its obstruction
    Normalization/  request charges versus rotation charges
  Classical/        Part III: classical, non-adaptive trees
    Static/         the balanced tree, its depth and cost; deep keys in every tree
      Optimal/      interval recurrence, Yao's lemma, Knuth's O(n²) algorithm
                    (rank-balanced, weight-balanced, random trees: planned)
  Algorithms/       Part IV: adaptive algorithms, definitions then bounds
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
`Classical` may import `Models`, `Bounds` and `Structures/Treap`;
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
- A classical, non-adaptive search tree (Part III of the book: static,
  rank-balanced, weight-balanced and random trees): `Classical/<Name>/`, laid
  out like an algorithm. The dictionary model with insertions and deletions
  that these trees need goes in `Models/Dictionary/`. Prefer one framework with
  the classical structures as instances (one rank-balanced framework for AVL,
  red-black and WAVL trees) over one development per structure.
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
| Theorem 4.3: combined weighted-finger, competitive, and worst-case bounds | [`Geometric.GreedyASS.Combination.Deamortized.Results.combined`](../RotationBST/Algorithms/GreedyASS/Combination/Deamortized/Abstract.lean) (see the combined-result section below) |
| Corollary 1: dynamic finger | [`Geometric.GreedyASS.Performance.Results.dynamic`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |
| BST and pointer realizations | [`Geometric.GreedyASS.Performance.Results.bst`, `pointer`, `bst_weighted`, `bst_dynamic`, `pointer_weighted`](../RotationBST/Algorithms/GreedyASS/Performance/Abstract.lean) |

For this [paper](https://arxiv.org/abs/1810.01785), startup is an explicit linear
term. The realization statements choose one causal policy before the initial
tree, requests, and benchmark. They do not claim global dynamic optimality.

The first finger-bound batch was followed by the ComboBST, deamortization, and
combined Theorem 4.3 integrations described below. Lazy Finger's unnumbered
periodic-rebuilding analysis and concluding conjecture remain outside these
batches. Existing book chapters and interactive figures are preserved; the
theorem maps supply the entry points for expanding them.

The book covers the first batch in chapters 9–10 (multi-finger and
linked-search models), 13, 14 and 16 (lazy finger, its place among the bounds,
and the conditional-entropy obstruction), sections 19.3–19.6 (GreedyASS's finger
bounds and their proof), chapters 21–22 (the optimizer and multiple trees), 28
(prefix sums and weighted search trees) and 29 (BST deques, tendons and finger
hands). The later batches are in section 20.3 (Tango with linear startup) and
chapters 23 (ComboBST), 24 (deamortization), 25 (Theorem 4.3), 30 (replays,
detours and depth invariants), 31–32 (pop-tarts and heavy paths) and 33 (tree
buffers and snapshots). The numbering is assigned by the book build from
`book/src/book.json`; chapter files are named by slug, not by number.


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


## ComboBST results for the book

The combination integration adds the abstract online and interval guarantees
from [Combining Binary Search Trees](https://arxiv.org/abs/1304.7604), together
with fixed finite-family composition. A chapter can develop the construction
in this order: interruptible source workers → snapshot save and restore →
alternating bounded rounds → charging closed rounds → one online pointer
execution → actual-window bounds → finite families.

`Algorithms/Combination` contains the controller, amortized analysis, source
refinement, online policy, and family construction. `Structures/TreeBuffer`
contains scan accounting, snapshot recording, streaming restoration, and
shared-node storage. These use the existing multifinger-to-pointer simulation
and preserve its per-request visits. All theorem names below are under
`RotationBST`; the exact hypotheses are in the linked public interfaces.

| Book topic | Checked entry point |
|---|---|
| Well-behaved charges and contiguous segments | [`Combo.Analysis.WellBehaved`](../RotationBST/Algorithms/Combination/Analysis/Definitions/Abstract.lean) |
| Interruptible attempts and round switching | [`Combo.Controller.Results`](../RotationBST/Algorithms/Combination/Controller/Abstract.lean) |
| Completed-round certificates | [`Combo.Rounds.Certificates.Results`](../RotationBST/Algorithms/Combination/Rounds/Certificates/Abstract.lean) |
| Minimum charge and window analysis | [`Combo.Analysis.Results.minimum_bound`, `executed_window`](../RotationBST/Algorithms/Combination/Analysis/Abstract.lean) |
| Scan progress and rotation-inclusive cost | [`TreeBuffer.Scan.Results.finish`, `total`](../RotationBST/Structures/TreeBuffer/Scan/Abstract.lean) |
| Shape-preserving snapshot save | [`TreeBuffer.Snapshot.Recording.Results.save`](../RotationBST/Structures/TreeBuffer/Snapshot/Recording/Abstract.lean) |
| Streaming snapshot load | [`TreeBuffer.Snapshot.Streaming.Results.load`](../RotationBST/Structures/TreeBuffer/Snapshot/Streaming/Abstract.lean) |
| Source instructions on shared nodes | [`Combo.Refinement.Results`](../RotationBST/Algorithms/Combination/Refinement/Abstract.lean) |
| One online policy and full-prefix comparison | [`Combo.Online.Results.prefix_policy`, `execute_append`](../RotationBST/Algorithms/Combination/Online/Abstract.lean) |
| Theorem 3's abstract actual-window guarantee | [`Combo.Online.Results.window_policy`, `executed_window`](../RotationBST/Algorithms/Combination/Online/Abstract.lean) |
| Independent source state types | [`Combo.Worker.Pair.Results`](../RotationBST/Algorithms/Combination/Worker/Pair/Abstract.lean) |
| Fixed finite-family worker | [`Combo.Family.Results.minimum_policy`](../RotationBST/Algorithms/Combination/Family/Abstract.lean) |
| Finite-family physical policy and actual windows | [`Combo.Family.Physical.Results.finite_policy`, `window_minimum`](../RotationBST/Algorithms/Combination/Family/Physical/Abstract.lean) |

The two-source theorem assumes a common nonempty initial tree, a valid physical
interpretation and request-service contract, and well-behaved nonnegative
amortized charges. The common overhead `F` must satisfy `n ≤ F`. Well-behavedness
includes the single-request bound at every reachable boundary, a complete-run
upper bound, and stability of the standalone contiguous segment relative to
its charges in the original sequence. These are operational hypotheses on the
input workers; arbitrary BST algorithms do not receive them automatically.

A policy is chosen before the future requests or comparison window. For a
window `[lo, hi)`, `executed_window` splits the actual run into its prefix,
middle, and suffix with exact state and cost composition. The middle is a
legal pointer execution between the trees returned by the prefix and middle.
Its charge comparison uses the indices and history from the original request
sequence. It does not rerun the algorithm from the saved tree at `lo`.

With constants `C₀,C₁` from `WellBehaved`, `window_policy` bounds that cost by

```
8384 * (C₁ + 58) *
  (2 * C₀² * min(original left window charge, original right window charge)
   + (2 * C₀ * C₁ + 73) * F).
```

Preparation is paid once on the first request and is absorbed into the stated
overhead; empty input and empty continuations cost zero. `prefix_policy` gives
a sharper whole-prefix formula. Both statements concern the chosen physical
execution, including its pointer operations and actual request visits.

For a fixed nonempty family of size `k`, the balanced construction uses depth
`d = ceil(log₂ k)`. `Family.Guarantees` retains every original comparator for
one output worker. `chargeScale` and `overheadScale` give explicit recurrences
for its constants. The physical wrapper supplies the corresponding prefix and
actual-window minimum bounds. The input workers can have different state types;
padding unused leaves repeats inputs. At worker depth zero a singleton family
retains its original constants. The physical wrapper has its own cost factor.

This integration supplies abstract BST-operation counterparts. It does not
claim the real-world storage clauses of Theorems 3 and 5, the sharper `O(k)`
family-size overhead, or Corollary 4's complete collection of concrete source
bounds. Classical policy selection and replay logs are allowed by the abstract
model. The finite-word implementation and the remaining source applications
stay on the formalization worktree.

Eleven added regression modules exercise exhausted attempts, exact-budget
completion, switching and restoration, closed-round charges, interleaved
rotations during scans, snapshot inversion, and heterogeneous three-member
families. Family tests check original versus restarted charge indices, windows
after nonempty prefixes, exact cost splitting, and differing best comparators
on different windows. The existing multifinger regressions remain in the build.


## Combined weighted-finger result for the book

The four topics now form a connected chapter sequence: lazy-finger/weight
characterization → GreedyASS's weighted bound → Tango with linear startup →
ComboBST's minimum guarantee → logarithmic worst-case deamortization.
The endpoint is the normalized abstract BST-operation counterpart of
[Weighted Dynamic Finger, Theorem 4.3](https://arxiv.org/abs/1810.01785).
All names below are under `RotationBST`.

| Book topic | Checked entry point |
|---|---|
| Original-sequence lazy-finger and interleave charges, including segment stability | [`Combo.Charges.Results`](../RotationBST/Algorithms/Combination/Charges/Abstract.lean) |
| One GreedyASS worker for all fixed reference trees | [`Geometric.GreedyASS.Combination.Results.greedy_worker`](../RotationBST/Algorithms/GreedyASS/Combination/Abstract.lean) |
| Balanced reference's linear initialization credit | [`Tango.Initialization.Local.Results.balanced_localAllowance`](../RotationBST/Algorithms/Tango/Preferences/Initialization/Local/Abstract.lean) |
| Executable bottom-up updates and a linear-startup competitive policy | [`Tango.BottomUp.Results.balanced_policy`](../RotationBST/Algorithms/Tango/Algorithm/BottomUp/Abstract.lean) |
| Tango worker satisfying the combination hypotheses | [`Tango.Combination.Results.linear_balanced_worker`](../RotationBST/Algorithms/Tango/Combination/Abstract.lean) |
| One combined online policy | [`Geometric.GreedyASS.Combination.Results.policy_exists`](../RotationBST/Algorithms/GreedyASS/Combination/Abstract.lean) |
| Same deamortized run compared with any positive weights | [`Geometric.GreedyASS.Combination.Deamortized.Results.weights_competitive`](../RotationBST/Algorithms/GreedyASS/Combination/Deamortized/Abstract.lean) |
| Complete Theorem 4.3 counterpart | [`Geometric.GreedyASS.Combination.Deamortized.Results.combined`](../RotationBST/Algorithms/GreedyASS/Combination/Deamortized/Abstract.lean) |

For a nonempty saved tree with `n` keys, `combined` chooses one policy and one
causal program before the request sequence, initial finger, weights, or offline
comparator. Every valid sequence has an actual served stream with exactly one
response cost per request. The costs sum to `m + instructions.length`;
setup costs at most `16n`, and every response costs less than
`251 + 195 log₂(n)`. The setup-inclusive total has the form

```
O(n + min(WF, (m + R) * (1 + log₂(1 + floor(log₂ n)))))
```

Here `WF` is the infimum of the normalized weighted-finger cost over positive
weights, from any specified valid predecessor. `R` is the rotation cost of
any offline execution of the same requests on any initial tree of size `n`.
The theorem gives explicit constants for this display and includes the empty
sequence. `Deamortized` records legal setup, replay correctness, actual visits,
and causality of emitted instruction and response-cost prefixes.

The new mathematical ingredient is Tango's linear startup proof. Updating
preferences from the bottom of a search path upward charges first settings
to local subtree credit, with at most one additional ancestor-attachment
charge per request. A balanced reference has at most `42n` local credit.
The replay adapter produces a well-behaved Tango worker with `2816n` startup;
the common GreedyASS/Tango allowance is `46225920n`. These are explicit,
unoptimized witnesses. Both source contracts are proved, not assumed inputs
to the final theorem.

The integration preserves the existing top-down Tango policy and its public
interfaces. A first setting toward an empty child now skips a redundant splay;
its correctness and zero cost are proved. Five added regression modules cover
original versus restarted window charges, empty and singleton universes,
actual bottom-up rotations, exact continuation states, nonperfect balanced
trees, and a single chosen combined program serving multiple sequences.
The ancestor-attachment regression demonstrates why local credit alone is
insufficient.

This chapter concerns abstract BST operations. It does not establish bounds on
finite-word storage or private computation, the full real-world clauses of
ComboBST/deamortization, or dynamic optimality. Those remaining developments
are separate from this complete abstract-model result.

## Dynamic finger, perfect trees and the logarithmic baseline

ROADMAP entries 1 and 4 (branch `formalize-finger-baseline`, 2026-11-09).
The first files of `Classical/`; the book chapters are not updated yet.

| Result | Checked entry point |
|---|---|
| DF ≤ 2·SF + start term | [`Bounds.dynamicFinger_le_fingerCost`, `dynamicFinger_le_fingerCost_self`](../RotationBST/Bounds/DynamicFinger/Abstract.lean) |
| DF property ⇒ SF property | [`Bounds.dynamicFinger_implies_staticFinger`](../RotationBST/Bounds/Implications/Abstract.lean) |
| SF ≤ m(1 + log n), SF property ⇒ logarithmic property | [`Bounds.fingerCost_le_log`, `staticFinger_implies_logarithmic`](../RotationBST/Bounds/Implications/Abstract.lean) |
| Balanced tree: size, depth ≤ ⌊log₂ n⌋, cost | [`Classical.Static.Results.balanced_size`, `balanced_depth`, `balanced_cost`, `balanced_cost_le_logCost`](../RotationBST/Classical/Static/Abstract.lean) |
| Every static tree: a key at depth ≥ ⌊log₂ n⌋, a sequence costing m(⌊log₂ n⌋ + 1) | [`Classical.Static.Results.exists_deep`, `exists_expensive`](../RotationBST/Classical/Static/Abstract.lean) |

New definitions: `HasDynamicFingerBound` in
`Bounds/DynamicFinger/Definitions/Abstract.lean` (which now imports
`Models/Online/Abstract`), `Bounds.logCost` and `HasLogarithmicBound` in
`Bounds/Logarithmic/Abstract.lean`, and `Classical.Static.balanced` in
`Classical/Static/Definitions/Abstract.lean`.

Choices made:

- `HasDynamicFingerBound` quantifies over every start key `p < n`. Changing
  `p` moves the sum by at most `1 + log₂ n`, which the startup term absorbs, so
  "for some `p`" or "`p` = root" would give an equivalent property.
- `Classical.Static.balanced` duplicates `Tango.balanced` because `Classical`
  may not import `Algorithms`. A later cleanup could define Tango's reference
  tree as the classical one (Tango may import `Classical`, which is below it).
- The baseline uses the real logarithm, `m(1 + log₂ n)`, like the other
  sequence costs; the tree statements use `⌊log₂ n⌋` (`Nat.log2`), which is
  what depth counts. `balanced_cost_le_logCost` connects the two.
- `HasStaticFingerBound.logarithmic` keeps the constants: the finger is put at
  rank 0, and the empty tree is handled separately (only the empty sequence is
  valid there).

Regression examples: `RotationBSTTests/FingerBaseline.lean` (the balanced tree
on 6, 7 and 8 keys, depths, a path, concrete costs, and the chain
DF ⇒ SF ⇒ logarithmic).

## Optimal static trees

ROADMAP entry 5 (branch `formalize-optimal-static`, stacked on
`formalize-finger-baseline`, 2026-11-09). Entry points:
[`Classical.Static.Optimal.Results`](../RotationBST/Classical/Static/Optimal/Abstract.lean);
the table in the roadmap entry lists them.

Layout of `Classical/Static/Optimal/`:

| File | Content |
|---|---|
| `Definitions/Abstract.lean` | `treeCost`, `cost` (the recurrence), `candidate`, `root`, `tree`, `Quadrangle`, `Monotone`, Knuth's `scan`, `knuthEntry`, `knuthTables`, `knuth`; key weights `weightedCost`, `rangeWeight`, `optCost`, `optTree`, `counts` |
| `Recurrence.lean` | optimality of the recurrence, the root and the tree |
| `Quadrangle.lean` | Yao's lemma and Knuth's root inequalities |
| `Knuth.lean` | the tables are correct; the root ranges telescope to `2n²` steps |
| `Weights.lean` | key weights, the weighted depth cost, request counts |
| `Sequences.lean` | the best static tree for a sequence, entropy and balanced bounds |

Choices made:

- Half-open intervals `[i, j)` and an abstract interval weight `W`, so Yao's
  lemma is stated once. Its hypotheses are the quadrangle inequality and
  monotonicity under inclusion; key weights satisfy the first with equality.
- `root` is the *largest* optimal root (Knuth's choice); with it both of
  Knuth's inequalities hold, and Knuth's algorithm returns it because the scan
  keeps the last minimizer.
- Knuth's algorithm is defined by interval length with function-valued tables.
  Its step count is the number of candidate roots examined, `R(i+1, j) −
  R(i, j−1) + 1` per interval (one for a single key); lookups are not counted.
  It is a specification of the algorithm, not a fast implementation.
- `Optimal.tree` uses well-founded recursion, so the kernel does not reduce it
  (`decide` cannot compare tree shapes); `#eval` works, and costs and roots
  reduce.
- The same recurrence with a different interval weight is
  `OptimalLazyFinger.solve` (`Algorithms/`). `Classical` cannot import it, and
  it reconstructs an arbitrary rather than the largest optimal root, so the
  classical version is independent. A shared generic recurrence in `Structures/`
  would be a later cleanup.

Regression examples: `RotationBSTTests/OptimalStatic.lean`.
