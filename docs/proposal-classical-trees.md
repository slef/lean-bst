# Proposal: classical search trees in the book

Branch `book-classical`, worktree `../lean-bst-classical`.

**Status (2026-11-10).** Implemented as a separate part. Most of it is
formalized and shown in the book; what remains is in ROADMAP.md entries 7–9
(deletions, red-black insertion, BB[α] rebalancing, treap updates, other
samplers) and stretch goals S1–S4. This proposal is kept for its rationale.

## Approach

This is a textbook, not a survey. Past results do not have to be reproduced
as they were published. Where several classical structures are instances of
one digested theory, the book presents the theory once and the structures as
instances. The original papers appear as sources and remarks.

## What the library already has

| Result | Lean | Book today |
|---|---|---|
| Perfectly balanced tree on `n` keys | `Tango.balanced`, `Tango.perfect` | inside the Tango chapter |
| Static tree as a pointer execution, cost = sum of (1 + depth) | `StaticTree.Results.pointer_execution`, `StaticTree.cost` | bounds.md, "Comparison with a fixed tree" |
| Entropy lower bound for every static tree (`staticCost ≤ 3 · cost`) | `StaticTree.Results.entropy_lower_bound` | bounds.md |
| A static tree within the entropy bound | `StaticTree.Results.entropy_upper_bound` | bounds.md |
| Weighted-median trees, `2^depth · w_x ≤ W`, and the regularized version | `WeightedSearch.Results.*` | prefix-sums.md, "Weighted search trees" |
| Treaps, and random treaps with Plackett–Luce priorities | `Treap.*`, `Treap.Random.*` | treaps.md (Part IV) |
| Ancestor and common-ancestor probability in a random treap | `Treap.Random.common_ancestor_probability` | inside the lazy-finger proof |
| Any tree to any other in at most `2n` rotations, through the right spine (vine) | `Geometry.reset` | Chapter 3, "Any shape to any shape" |
| Insert, delete, split, join by rank, with rotation counts (splay only) | `Splay.Updates.*` | beyond.md |

Missing:
- **Balanced dictionaries:** AVL, red-black, weight-balanced and scapegoat
  trees.
- **Optimal static tree:** Knuth's algorithm.
- **Random trees:** the expected depth of a random BST, and the expected
  rotations of treap updates.
- **Updates:** a model for updates that is not specific to splay trees.

## Proposed structure

Add a new part, **Classical search trees**, between Bounds and Algorithms.
Rename Algorithms to **Adaptive algorithms**. Structures becomes Part V.
The new part covers dictionaries, which need updates, and serves as the
baseline the adaptive algorithms are compared with.

### Part III — Classical search trees (new)

The intro page (`classical/part-classical.md`) covers:
- What "non-adaptive" means here: the shape depends on the key set and the
  update history, never on which keys are searched.
- The baseline: every tree on `n` keys has a key at depth `⌊log₂ n⌋`, and the
  perfect tree matches it.
- A comparison table: height bound, rotations per update (worst case and
  amortized), randomized or not, and Lean status.

Four chapters, each built around one theory:

| # | Chapter (slug) | The theory | Instances, as sections or remarks |
|---|---|---|---|
| 17 | **Static search trees** (`static-trees`) | Cost of a fixed tree; entropy bounds; optimal trees by dynamic programming with the quadrangle inequality (Yao 1980) | Perfect trees and the `⌊log₂ n⌋` lower bound · weighted-median trees (Mehlhorn 1975) · Knuth's `O(n²)` optimal trees (Knuth 1971) as the instance of Yao's speedup |
| 18 | **Rank-balanced trees** (`rank-balanced`) | Integer ranks with rank-difference rules, bottom-up rebalancing by promote, demote, single and double rotation (Haeupler–Sen–Tarjan 2015) | AVL (Adelson-Velsky–Landis 1962) · red-black (Bayer 1972, Guibas–Sedgewick 1978) · WAVL |
| 19 | **Weight-balanced trees** (`weight-balanced`) | The α-weight-balance invariant: depth `≤ log_{1/(1−α)} n`, and an unbalanced node of size `s` has seen `Ω(s)` updates below it since it was last rebuilt | Restoring by rotations: BB[α] (Nievergelt–Reingold 1973, Blum–Mehlhorn 1980) · restoring by rebuilding, using the reset of Chapter 3: scapegoat trees (Andersson 1989, Galperin–Rivest 1993) |
| 20 | **Random search trees** (`random-trees`) | One distribution: the treap of uniformly random priorities. Ancestor probabilities give expected depths | Random insertion order (Hibbard 1962) · treaps (Seidel–Aragon 1996), whose shape is independent of the update history · randomized BSTs and zip trees (Martínez–Roura 1998; Tarjan–Levy–Timmel 2021) as other samplers of the same distribution |

**Static search trees.**
- The perfect tree has height `⌊log₂ n⌋`, and every tree has a key at least
  that deep.
- The entropy bounds and weighted-median trees already exist.
- Optimal static trees: Yao's theorem, that a cost satisfying the quadrangle
  inequality has monotone optimal roots, gives Knuth's `O(n²)` algorithm. The
  cubic algorithm is presented first, as the specification.

**Rank-balanced trees.**
- **Heights:**
  - AVL: below `1.44 log₂(n + 2)`.
  - Red-black: at most `2 log₂(n + 1)`.
  - WAVL: AVL's bound if there are no deletions, never worse than red-black.
- **Rotations per update:**
  - AVL insertion: one single or double rotation.
  - Red-black: 2 per insertion, 3 per deletion.
  - WAVL: 2.
- **Amortized:** `O(1)` rank changes per update for red-black and WAVL.
- **Proof structure:** one representation, one set of rebalancing moves, and
  three rank rules. Each height bound comes from a counting lemma on the
  smallest tree of a given rank, so the proofs are shared.

**Weight-balanced trees.**
- One invariant, with two ways of restoring it.
- **Rotations (BB[α]):** `O(1)` amortized rotations per update, for α in
  the classical range.
- **Rebuilding (scapegoat):** a subtree of size `s` is rebuilt with at most
  `2s` rotations by the reset of Chapter 3, applied inside that subtree, for
  `O(log n)` amortized per update. No balance data is stored.
- Mathlib's `Ordnode` (Adams' weight-balanced trees) may be reusable for the
  invariant.

**Random search trees.**
- **Expected depth.** The exact expected depth is `H_{x+1} + H_{n−x} − 2`. It
  is the case `x = y` of `common_ancestor_probability`, with uniform weights.
- **Updates.** Insertions and deletions preserve the distribution, with
  fewer than 2 expected rotations each.
- **Samplers.** The other structures produce the same distribution: one
  theorem each, not one analysis each.
- **Height.** The expected height `≈ 4.311 ln n` (Devroye 1986) is a remark
  only.

### Chapter 3 — no new chapter, one remark

Rebuilding needs no chapter of its own. `Geometry.reset` already goes through
the right spine, which is the vine of the Day–Stout–Warren algorithm. Taking
the perfect tree as the target gives DSW. The scapegoat section uses reset
directly, applied inside a subtree.

Chapter 3 already mentions Sleator–Tarjan–Thurston's `2n − 6` and Pournin's
matching lower bound. They stay remarks there, with a ROADMAP stretch entry
at most. One sentence naming DSW would be added to that section.

### Part I — one new model chapter

**Insertions and deletions** (`dictionary`), after "Online algorithms and
cost". It is a model at the level of tree shapes:

- **Operations.** Insert at a gap, delete a rank, split and join. Positions
  are given as ranks.
- **Cost.** `1 + depth of the search path + rotations`.
- **Node fields.** Ranks, colours or sizes, from `Models/Labelled/Metadata`.

The model generalizes `Splay.Updates.Step` and `Execution`, so splay's
dictionary bound (beyond.md) becomes one instance. It does not model a pointer
machine with node allocation: that would be more faithful, but adds nothing
the classical results need.

### What moves

| From | To |
|---|---|
| prefix-sums.md, "Weighted search trees" | static-trees. Prefix-sums keeps the two-dimensional prefix sums. |
| bounds.md: `entropy_upper_bound` and its construction | static-trees. Bounds keeps the lower bound and `workingSet_competes`. |
| treaps.md, "Random treaps" | random-trees. The Part V treaps chapter keeps the geometric treaps used by the equivalence proofs. |
| Tango chapter: the balanced reference tree | static-trees (shown once, referenced from Tango) |
| beyond.md, "Updates" (the model part) | the new Part I chapter. beyond.md keeps the splay instance and its bound. |

Move-to-root stays the first chapter of Adaptive algorithms.

Also to update:
- the preface map;
- the "What each chapter uses" table of the adaptive part;
- the "Used by" column in the Structures intro;
- the bounds map links.

## Lean work (ROADMAP.md entries to add)

In rough order of cost:

1. Expected depth of a random BST: a corollary of the treap ancestor
   probability. Small.
2. Height of the perfect tree is `⌊log₂ n⌋`, and every tree has a key at
   least that deep. Small.
3. Rebuilding inside a subtree: reset lifted under `inLeft`/`inRight`, to
   `Tango.perfect`. Small.
4. Optimal static trees: the cubic DP is correct; Yao's quadrangle-inequality
   theorem; Knuth's `O(n²)` restriction as a corollary. Medium. The Isabelle
   AFP entry `Optimal_BST` (Nipkow–Somogyi) has the same structure.
5. Generic dictionary model (Part I), with splay's `Updates` as an instance.
   Medium; mostly a design decision.
6. Rank-balanced framework: AVL, red-black and WAVL as three rank rules, with
   heights and rotation counts. Large.
7. Weight-balanced framework: BB[α] and scapegoat trees. Medium to large.
8. Random trees: history independence of treap updates, expected rotations,
   and the other samplers. Medium.

Stretch goals, as remarks in the book with no ROADMAP target:
- the rotation distance `2n − 6`;
- Devroye's height of random trees;
- Hu–Tucker and Garsia–Wachs alphabetic trees;
- Allen and Munro's expected cost of move-to-root.

Out of scope: B-trees and skip lists, which are not binary search trees in
this book's models.

## Phasing

- **Phase 1 (book only, now).**
  - The new part and its intro.
  - Chapter 17 with its existing parts.
  - Chapter 20 with the moved random-treap material.
  - The moves listed above.
  - ROADMAP entries 1–8.
  - Chapters 18 and 19 listed in the part intro as planned.
- **Phase 2 (as the prover delivers).** Write chapters 18 and 19, the dictionary
  model chapter and the missing sections, one ROADMAP entry at a time.

## Remaining questions

1. **Placement.** Is a separate part "Classical search trees" before
   "Adaptive algorithms" right? The alternative is to open the current
   Part III with these four chapters.
2. **Unformalized chapters.** Should they wait for Lean (as above), or be
   drafted now with statements marked "not yet formalized"?
