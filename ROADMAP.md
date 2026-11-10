# Roadmap

Results that the book mentions but the library does not prove yet. Each entry
gives the source, a target statement, where it belongs (see "Where new results
go" in [docs/organization.md](docs/organization.md)), and what to update in the
book once it is proved.

The target statements are suggestions. Change the constants or the shape if the
proof calls for it, but keep the usual conventions: uniform natural constants,
one unit per request, and an explicit startup term.

Entries 7 to 9 are the open parts of the classical search trees of Part III
of the book. The book follows a textbook approach there: one
theory with the classical structures as instances, rather than one analysis
per paper. The Lean development should follow the same plan. The stretch goals
at the end are hard results, to be done last or not at all.

Entries keep their numbers when others are removed, so that links to them stay
valid. A finished entry is deleted once the book shows its results.

## 2. Splay trees are O(log log n · log² log log n)-competitive

**Source.** Petr Chmel, Bernhard Haeupler, Richard Hladík, Michal Koucký,
Antti Roeyskoe, Václav Rozhoň, Ondřej Sladký and Robert E. Tarjan, *Splay trees
are almost dynamically optimal*, arXiv:2607.18498 (July 2026). Abstract: "We
prove that splay trees are O(log log n · log² log log n) = Õ(log log n)-competitive."
Shown as the dashed arrow from splay trees to OPT in the map of the bounds.

**Statement.** The same shape as `Tango.Algorithm.Results.exists_competitive`,
but for the fixed algorithm `RotationBST.Splay.algorithm` rather than an
existential one. Logarithms are shifted so that the factor is defined and
positive for every `n`; the additive term should be read off the paper (the
abstract does not state it).

```lean
theorem RotationBST.Splay.Results.competitive :
    ∃ C D : Nat, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      Execution start xs finish offline →
        let ℓ := Real.logb 2 (Nat.log2 start.size + 1)   -- log log n
        let ℓ' := Real.logb 2 (Nat.log2 (Nat.log2 start.size + 1) + 1)   -- log log log n
        (Splay.algorithm.totalCost start xs : ℝ) ≤
          C * (ℓ * (ℓ' + 1) ^ 2 + 1) * (offline + xs.length : Nat) +
            D * start.size * (1 + (start.size.log2 : ℝ))
```

**Where.** `Algorithms/Splay/Competitive/` (an `Abstract.lean` for the
statement, proof files alongside), imported from `Algorithms/Splay/Abstract.lean`.
This is a large project: read the paper first and plan the lemmas before
starting.

**Book.** In `book/src/assets/viz/boundsmap.js`, drop `todo: true` from the
`splay → OPT` edge and give it `thms`. Update the algorithms table in
`book/src/chapters/bounds/part-bounds.md`, the "What is not formalized" section
of `bounds/bounds.md`, and the overview `algorithms/splay-trees.md`. Add a
headline result to the splay analysis section (`algorithms/analysis.md`) or a
new section after it (an entry under `splay-trees` in `book/src/book.json`).

## 7. Rank-balanced trees

**Status.** Partly formalized (2026-11-10). The book chapter "Rank-balanced
trees" (`classical/rank-balanced.md`) shows what is done, under
`RotationBST.Classical.RankBalanced`: ranked trees and the three rules; the
height bounds (AVL `log_φ(n + 1)` in nodes, red-black and WAVL
`2 log₂(n + 1)`); and WAVL insertion, which is also AVL insertion, as a
dictionary step with at most 2 rotations, `7m` rank changes for `m` insertions
from empty, and height `log_φ(m + 1)` after them. Still open:

- deletion as a dictionary step: WAVL with at most 2 rotations, red-black with
  at most 3, AVL with `O(log n)`;
- red-black insertion, with at most 2 rotations;
- amortized rank changes with deletions, `O(1)` per update for red-black and
  WAVL trees;
- WAVL height at most `log_φ m` after `m` insertions and any deletions;
- optionally, Knuth's sharper AVL bound `height < 1.4405 log₂(n + 2) − 0.3277`,
  with the height in nodes.

**Source.** B. Haeupler, S. Sen and R. E. Tarjan, *Rank-balanced trees*, ACM
TALG 11(4) (2015), for the framework and WAVL trees; G. M. Adelson-Velsky and
E. M. Landis (1962) for AVL trees; R. Bayer (1972) and L. J. Guibas and
R. Sedgewick (1978) for red-black trees; R. E. Tarjan, *Updating a balanced
search tree in O(1) rotations*, IPL 16 (1983).

**Statement.** Follow `insert`, `insert_step` and `insertEdits_empty` in
`Classical/RankBalanced/Insertion/`. For deletion: a function
`delete : RankedTree → Nat → RankedTree × Nat × Nat` (tree, rotations, rank
changes) per rule, or one parametrized by the rule, with

```lean
theorem delete_step (t : RankedTree) (x : Nat) (hx : x < t.erase.size) :
    ∃ c, Dictionary.Step t (.delete x) (delete t x).1 c (delete t x).2.2
theorem delete_valid (r : Rule) (t : RankedTree) (x : Nat) (h : Valid r t) :
    Valid r (delete r t x).1   -- with `delete` parametrized by the rule
theorem wavl_delete_rotations : (delete t x).2.1 ≤ 2      -- WAVL
theorem redBlack_delete_rotations : (delete t x).2.1 ≤ 3  -- red-black
-- amortized: total rank changes over any m updates from empty ≤ C · m
```

**Where.** `Classical/RankBalanced/Deletion/`, next to `Insertion/`.

**Book.** In `classical/rank-balanced.md`, replace the matching items of the
box in "What is not formalized" with `@decl`s and a headline. Update the
status column of `classical/part-classical.md` and the "Deliberate
non-claims" in `appendices/audit.md`.

## 8. Weight-balanced and scapegoat trees

**Status.** Partly formalized (2026-11-10). The book chapter "Weight-balanced
trees" (`classical/weight-balanced.md`) shows what is done: the invariant
`Classical.WeightBalanced.Balanced` and its height bound, rebuilding into the
balanced tree with at most `2n` rotations, and scapegoat trees
(`Classical.Scapegoat`) as dictionary executions with depth
`log_{1/α} n + 1` and an `O(log n)` amortized cost. Still open:

- BB[α] rebalancing: for `2/11 < α ≤ 1 − √2/2`, single and double rotations
  restore the invariant after an insertion or a deletion, as dictionary steps;
- `O(1)` amortized rotations per update for BB[α] trees;
- the common lemma: a balanced subtree of weight `s` needs
  `Ω((β − 1/2) s)` updates inside it before it violates `Balanced β`;
- optionally, scapegoat trees as a `Dictionary.Algorithm` (the count `N` is
  not stored in the tree today), and an executable Day–Stout–Warren rebuild.

**Source.** J. Nievergelt and E. M. Reingold, *Binary search trees of bounded
balance*, SIAM J. Comput. 2(1) (1973); N. Blum and K. Mehlhorn, *On the
average number of rebalancing operations in weight-balanced trees*, TCS 11
(1980). Mathlib's `Ordnode` (Adams' weight-balanced trees) may help.

**Statement.**

```lean
-- BB[α] insertion and deletion with rebalancing, (tree, rotations):
def bbInsert (α : ℚ) : Tree → Nat → Tree × Nat
def bbDelete (α : ℚ) : Tree → Nat → Tree × Nat
theorem bbInsert_balanced (hα : (2 / 11 : ℝ) < α ∧ (α : ℝ) ≤ 1 - Real.sqrt 2 / 2)
    (h : Balanced (1 - (α : ℝ)) t) : Balanced (1 - (α : ℝ)) (bbInsert α t k).1
-- and the same for bbDelete; both are dictionary steps; and the total number
-- of rotations of m updates from the empty tree is at most C · m.
```

**Where.** `Classical/WeightBalanced/`.

**Book.** In `classical/weight-balanced.md`, replace the box in "Restoring by
rotations: BB[α] trees". Update `classical/part-classical.md` and the
"Deliberate non-claims" in `appendices/audit.md`.

## 9. Random search trees

**Status.** Partly formalized (2026-11-10). The book chapter "Random search
trees" (`classical/random-trees.md`) shows what is done, under
`Classical.Random.Results`: the exact expected depth `H(x + 1) + H(n − x) − 2`
in a random treap and in a random BST, the bound `2 ln n`, and the fact that
plain insertion in a given order builds the treap of that order
(`insertKeys_treap`). Still open:

- treap insertion and deletion by rotations, as dictionary steps, producing
  the treap of the new key set (history independence), with fewer than 2
  rotations in expectation;
- randomized BSTs produce the uniform random BST after every operation; zip
  trees produce the treap of their (rank, key) priorities.

**Source.** R. Seidel and C. R. Aragon, *Randomized search trees*,
Algorithmica 16 (1996); C. Martínez and S. Roura, *Randomized binary search
trees*, JACM 45 (1998); R. E. Tarjan, C. Levy and S. Timmel, *Zip trees*, ACM
TALG 17(4) (2021). The Isabelle AFP entry *Treaps* (Haslbeck, Eberl and
Nipkow) and their paper *Verified analysis of random binary tree structures*
(JAR 2020) cover similar ground.

**Statement.**

```lean
-- Priorities as an order, as in Treap.Random; treap insertion of a key
-- with given priority, by leaf insertion and rotations up:
theorem treapInsert_heap ... : Geometric.Heap prio (treapInsert prio t k).1 lo
theorem treapInsert_step ... : Dictionary.Step t.unit (.insert k) (treapInsert prio t k).1.unit c 0
theorem expected_insert_rotations ... : average ... < 2
-- and the same for deletion.
```

**Where.** `Classical/Random/`, using the dictionary model (`Models/Dictionary`).

**Book.** In `classical/random-trees.md`, replace the boxes in "Treaps" and
"Other ways to sample". Update `classical/part-classical.md` and the
"Deliberate non-claims" in `appendices/audit.md`.

## Stretch goals

Hard results that the book mentions. They are listed so that nothing is
forgotten. Do them last, or decide later that the book only cites them.

### S1. Rotation distance

**Source.** K. Culik II and D. Wood (1982), `2n - 2`; D. D. Sleator,
R. E. Tarjan and W. P. Thurston, *Rotation distance, triangulations, and
hyperbolic geometry*, JAMS 1(3) (1988), `2n - 6` for large `n`, tight for
large `n`; L. Pournin, *The diameter of associahedra*, Adv. Math. 259 (2014),
tight for every `n ≥ 11`. Mentioned in the book in `models/accesses.md`
("Any shape to any shape"), next to the formalized bound `2n`.

**Statement.** Upper bound (elementary): for `n ≥ 11`, any two trees with `n`
nodes are at most `2n - 6` rotations apart. Lower bound (hard): for every
`n ≥ 11` there are two trees at distance exactly `2n - 6`.

**Where.** `Models/Rotation/Distance/`.

**Book.** A paragraph and `@decl`s in `models/accesses.md`.

### S2. Height of random search trees

**Source.** L. Devroye, *A note on the height of binary search trees*, JACM
33(3) (1986); B. Reed, *The height of a random binary search tree*, JACM 50(3)
(2003). Book chapter "Random search trees", section "Height".

**Statement.** The expected height of a random BST on `n` keys is
`c ln n - (3c / (2(c - 1))) ln ln n + O(1)` with `c ≈ 4.311` the root of
`c ln(2e/c) = 1` (Reed), or the weaker first-order form `~ c ln n` (Devroye).
A useful intermediate target: expected height `O(log n)`, which follows from
a union bound over the depth tail.

**Where.** `Classical/Random/Height/`.

### S3. Optimal alphabetic trees

**Source.** T. C. Hu and A. C. Tucker, *Optimal computer search trees and
variable-length alphabetical codes*, SIAM J. Appl. Math. 21(4) (1971);
A. M. Garsia and M. L. Wachs, *A new algorithm for minimum cost binary trees*,
SIAM J. Comput. 6(4) (1977). Book chapter "Static search trees", section
"Further results".

**Statement.** With weights only on the gaps (all searches unsuccessful), the
Hu–Tucker or Garsia–Wachs algorithm computes an optimal tree in `O(n log n)`
time. The correctness proofs are notoriously delicate. Decide first whether
the book needs more than a citation.

### S4. Move-to-root under independent requests

**Source.** B. Allen and I. Munro, *Self-organizing binary search trees*, JACM
25(4) (1978). Book chapter "Move-to-root" (`algorithms/move-to-root.md`).

**Statement.** When requests are independent and identically distributed,
the expected cost of move-to-root in the stationary regime is within a
constant factor of the optimal static tree for the same distribution (take
the exact constant from the paper). Needs a probability model for infinite request sequences,
which the library does not have.
