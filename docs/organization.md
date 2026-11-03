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
    Online/         online algorithms, rotation/total cost, dynamic optimality
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
    Normalization/  request charges versus rotation charges
  Algorithms/       Part III: algorithms, definitions then bounds
    MoveToRoot/
    Splay/          algorithm, potential, access lemma, nine ST85 theorems,
                    updates, conditional splay, scanning, pointer version
    GreedyASS/      the geometric greedy sweep
    Simulation/     causal geometric-to-BST simulation (last-touch supernodes)
    Tango/          preferred paths, preference changes, auxiliary trees,
                    marked-tree state machine, executable policy, O(log log n)
  Structures/       Appendix: supporting structures
    Treap/          next-touch treaps for the offline construction
    SplitTree/      multiway finger trees and split hierarchies
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
  `Wilber.Results`, `Arboral.Equivalence.Results`, …). Namespaces are
  independent of paths in Lean; they were aligned with the parts in the third
  pass, except for the `Arboral` root of the geometric definitions.

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
  `Arboral.Results` (model facts), `Arboral.Equivalence.Results`,
  `Arboral.GreedyASS.Results`, and `Arboral.Simulation.Results`. The `Arboral`
  root namespace of the geometric definitions and the `Tango` namespace of
  Tango's own vocabulary are unchanged.
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

## Remaining follow-ups

1. `Bounds/StaticTree/Comparison` uses splay's `locate` zipper search and its
   pointer-trace lemma to execute a fixed tree on the pointer machine. Moving
   `locate` into `Models/Pointer` would remove the last `Bounds` → `Algorithms`
   proof dependency; it touches the splay abstract and the book's splay chapter.
2. `Models/Geometric/Offline/Optimal` proves that a minimum offline solution
   exists by running the GreedyASS sweep; a direct argument from `full_row`
   would keep the model independent of the algorithm.
3. The geometric definitions keep the historical `Arboral` namespace.
4. Book chapters for the geometric model and equivalences, Wilber's bound,
   GreedyASS, the causal simulation, Tango, and the structures. The book's
   build lists the uncovered surface declarations.

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
