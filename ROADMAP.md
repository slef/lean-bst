# Roadmap

Results that the book mentions but the library does not prove yet. Each entry
gives the source, a target statement, where it belongs (see "Where new results
go" in [docs/organization.md](docs/organization.md)), and what to update in the
book once it is proved.

The target statements are suggestions. Change the constants or the shape if the
proof calls for it, but keep the usual conventions: uniform natural constants,
one unit per request, and an explicit startup term.

Entries 4 to 9 are the classical search trees of Part III of the book, and the
dictionary model they need. The book follows a textbook approach there: one
theory with the classical structures as instances, rather than one analysis
per paper. The Lean development should follow the same plan. The stretch goals
at the end are hard results, to be done last or not at all.

## 1. Dynamic finger implies static finger

**Status.** Formalized (branch `formalize-finger-baseline`, 2026-11-09); the
book update below is pending. Checked names, all under `RotationBST`:

| Statement | Declaration | File |
|---|---|---|
| `DF(p, xs) ≤ 2·SF(f, xs) + log₂(d(p, f) + 1)` | `Bounds.dynamicFinger_le_fingerCost` | `Bounds/DynamicFinger/Abstract.lean` |
| `DF(f, xs) ≤ 2·SF(f, xs)` | `Bounds.dynamicFinger_le_fingerCost_self` | `Bounds/DynamicFinger/Abstract.lean` |
| the property, for every start key `p < n` | `HasDynamicFingerBound` | `Bounds/DynamicFinger/Definitions/Abstract.lean` |
| DF ⇒ SF, constants `(C, D) ↦ (2C, D)` | `Bounds.dynamicFinger_implies_staticFinger` | `Bounds/Implications/Abstract.lean` |

The statements are exactly the targets below. No algorithm in the library has
`HasDynamicFingerBound` yet: GreedyASS's `bst_dynamic` gives one algorithm per
universe size `n`, not one for all sizes, so it does not instantiate the
property; the implication is about the properties only.

**Source.** Classical. Shown as the dashed arrow DF → SF in the map of the
bounds (the introduction to Part II of the book, section "A map of the bounds").

**Statement.** For every finger `f`, start key `p` and sequence `xs`, the dynamic
finger sum is at most twice the static finger sum plus a start term:

```lean
theorem RotationBST.Bounds.dynamicFinger_le_fingerCost (f p : Nat) (xs : List Nat) :
    Bounds.dynamicFingerCostFrom p xs ≤
      2 * Bounds.fingerCost f xs + Real.logb 2 (Nat.dist p f + 1 : Nat)
```

**Proof idea.** For consecutive keys `x`, `y`, `dist x y ≤ dist x f + dist f y`,
so `dist x y + 1 ≤ (dist x f + 1) * (dist y f + 1)`, and the logarithm splits.
Summing, each request's `log (dist x f + 1)` term is counted at most twice
(once as the target of a step, once as its source); the first step's source is
`p`, which gives the extra term. The units match one for one.

**Optional property version.** No `Has…Bound` property exists for dynamic
finger yet. If one is added, the natural shape quantifies over the start key:

```lean
def RotationBST.HasDynamicFingerBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs p, p < t.size → (∀ x ∈ xs, x < t.size) →
    (a.totalCost t xs : ℝ) ≤ (C : ℝ) * Bounds.dynamicFingerCostFrom p xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ))

theorem RotationBST.Bounds.dynamicFinger_implies_staticFinger (a : Algorithm)
    (h : HasDynamicFingerBound a) : HasStaticFingerBound a
```

Taking `p = f` makes the start term vanish.

**Where.** The inequality in `Bounds/DynamicFinger/` (a new `Abstract.lean`
next to `Definitions/`). The property and the implication in
`Bounds/Implications/Abstract.lean`, next to
`staticOptimality_implies_staticFinger`.

**Book.** In `book/src/assets/viz/boundsmap.js`, drop `todo: true` from the two
`DF → SF` edges and give them `thms`. In `book/src/chapters/bounds/bounds.md`, show
the new declarations with `@decl` and update the "Dynamic finger" and "What is
not formalized" sections. In `book/src/chapters/bounds/part-bounds.md`, link
them in the relations table.

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

## 3. Tango as one online algorithm with linear startup

**Source.** Book chapter "Tango with linear startup" (`book/src/chapters/algorithms/tango-linear.md`). Its headline combines two library theorems by hand; no single theorem states the result.

**Statement.** Compose `Tango.BottomUp.Results.balanced_policy` with `Tango.Algorithm.Rotation.Results.rotation_algorithm`. The first gives `run + m ≤ 42n + (70L + 20)(R + m)`. The second gives `totalCost ≤ m + run + 2n`. Together:

```lean
theorem RotationBST.Tango.Algorithm.Results.exists_competitive_linear (n : Nat) :
    ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      start.size = n → Execution start xs finish offline →
        (A.totalCost start xs : ℝ) ≤
          (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) + 44 * n
```

**Proof idea.** The two bounds compose directly. `rotation_algorithm`'s algorithm agrees with the policy on runs from the reference tree. From any other tree it pays at most `2n` extra to reach the reference.

**Where.** `Algorithms/Tango/Algorithm/BottomUp/Abstract.lean`, or `Algorithms/Tango/Algorithm/Abstract.lean` next to `exists_competitive`.

**Book.** In `algorithms/tango-linear.md`, replace the hand composition in the `tango-linear` headline with the new theorem. In `appendices/audit.md` and the overview `algorithms/tango-trees.md`, drop the remarks on Tango's linear startup being composed by hand.

## 4. Perfect trees and the logarithmic baseline

**Status.** Formalized (branch `formalize-finger-baseline`, 2026-11-09); the
book update below is pending. The statements differ from the targets below in
three ways: the tree is `Classical.Static.balanced`, a copy of `Tango.balanced`
(`Classical` may not import `Algorithms`; the two definitions are textually
identical); the finger inequality is named `fingerCost_le_log` and uses the
new baseline `Bounds.logCost n xs = m(1 + log₂ n)`; and there are two extra
results. Checked names, all under `RotationBST`:

| Statement | Declaration | File |
|---|---|---|
| the balanced tree on `n` keys | `Classical.Static.balanced` | `Classical/Static/Definitions/Abstract.lean` |
| it has `n` keys | `Classical.Static.Results.balanced_size` | `Classical/Static/Abstract.lean` |
| depth ≤ `⌊log₂ n⌋` | `Classical.Static.Results.balanced_depth` | same |
| every nonempty tree has a key at depth ≥ `⌊log₂ n⌋` | `Classical.Static.Results.exists_deep` | same |
| static cost ≤ `m(⌊log₂ n⌋ + 1)` | `Classical.Static.Results.balanced_cost` | same |
| static cost ≤ `logCost n xs` (reals) | `Classical.Static.Results.balanced_cost_le_logCost` | same |
| every static tree pays `m(⌊log₂ n⌋ + 1)` on `m` repeats of a deep key | `Classical.Static.Results.exists_expensive` | same |
| the baseline `m(1 + log₂ n)` | `Bounds.logCost` | `Bounds/Logarithmic/Abstract.lean` |
| the property "O(1 + log n) amortized per request" | `HasLogarithmicBound` | same |
| `SF(f, xs) ≤ logCost n xs` for `f < n` | `Bounds.fingerCost_le_log` | `Bounds/Implications/Abstract.lean` |
| SF ⇒ logarithmic, same constants | `Bounds.staticFinger_implies_logarithmic` | same |

For the figure: `SF → BAL` is `Bounds.fingerCost_le_log` (and the property
version `staticFinger_implies_logarithmic`), and `B.BAL` can take the `def`
`Bounds.logCost`. The perfect tree reaches the baseline
(`balanced_cost_le_logCost`), but that is a static tree, not an online
algorithm; the `balanced → BAL` edge still waits on entry 7 or 8 or a
relabelled bubble, as the book instructions below say.

**Source.** Classical. Shown as the box `m(1 + log n)` at the bottom of the
map of the bounds, with a dashed arrow `SF → m(1 + log n)` and the "Balanced
trees" bubble. Book chapter "Static search trees" (`classical/static-trees.md`,
section "Perfect trees").

**Statement.** Three small facts about `Tango.balanced` (or a copy moved to the
new directory) and the static finger sum:

```lean
theorem RotationBST.Classical.Static.Results.balanced_depth (n x : Nat) (hx : x < n) :
    (Tango.balanced n).depth x ≤ Nat.log2 n

theorem RotationBST.Classical.Static.Results.exists_deep (t : Tree) (h : 0 < t.size) :
    ∃ x < t.size, Nat.log2 t.size ≤ t.depth x

theorem RotationBST.Classical.Static.Results.balanced_cost (n : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    StaticTree.cost (Tango.balanced n) xs ≤ xs.length * (Nat.log2 n + 1)

theorem RotationBST.Bounds.fingerCost_le_balanced (n f : Nat) (xs : List Nat)
    (hf : f < n) (valid : ∀ x ∈ xs, x < n) :
    Bounds.fingerCost f xs ≤ xs.length * (1 + Real.logb 2 n)
```

**Proof idea.** `balanced` splits `n` keys into `⌈(n-1)/2⌉` and `⌊(n-1)/2⌋`, so
induction on `n` with `Nat.log2` arithmetic. For `exists_deep`, a tree of
height `h` has at most `2^(h+1) - 1` keys. For the finger sum, `Nat.dist x f + 1 ≤ n`.

**Where.** `Classical/Static/Abstract.lean` (a new top-level `Classical/`
directory for Part III of the book), and the finger inequality in
`Bounds/Implications/`.

**Book.** In `classical/static-trees.md`, replace the "Not yet formalized" box
of "Perfect trees" with the theorems. In `book/src/assets/viz/boundsmap.js`,
drop `todo: true` from `SF → BAL` and `balanced → BAL` (the latter only once
entry 7 or 8 is also done, or relabel the bubble "Perfect tree"), and give
them `thms`. Give `B.BAL` a `def` if a definition of `m(1 + log n)` is added.
Update the tables in `classical/part-classical.md` and `bounds/part-bounds.md`.

## 5. Optimal static trees

**Status.** Formalized (branch `formalize-optimal-static`, stacked on
`formalize-finger-baseline`, 2026-11-09); the book update below is pending.
All statements are in `Classical/Static/Optimal/Abstract.lean`, namespace
`RotationBST.Classical.Static.Optimal.Results`; the definitions are in
`Classical/Static/Optimal/Definitions/Abstract.lean`. Differences from the
targets below:

- The recurrence, its roots and Knuth's algorithm are stated for an abstract
  interval weight `W : Nat → Nat → Nat` over half-open intervals `[i, j)`:
  `Optimal.cost W i j`, `Optimal.root W i j` (the *largest* optimal root),
  `Optimal.tree W i j`, `Optimal.knuth W n : Nat × Nat` (cost, steps). Key
  weights are the instance `rangeWeight w i j = ∑_{i ≤ x < j} w[x]`; gap
  weights are another additive instance, not stated separately.
- `optCost`, `optTree` (in `Classical.Static`, with `w : List Nat`) are the
  targets; `weightedCost w t = ∑ₓ w[x](depth x + 1)` as suggested.
- Yao's lemma is `cost_quadrangle` (the quadrangle inequality passes from a
  monotone `W` to the cost) and Knuth's inequalities `root_le_root_right`
  (`R(i, j) ≤ R(i, j + 1)`) and `root_le_root_left` (`R(i, j) ≤ R(i + 1, j)`).
- Steps count examined candidate roots; the bound is `2n²`, sharper than the
  target `4(n + 1)²`: `knuth_steps`, and `knuth_steps_le` for key weights.

| Statement | Declaration (under `Optimal.Results`) |
|---|---|
| the tree has `j - i` keys and costs `cost W i j`; no tree costs less | `tree_size`, `tree_cost`, `cost_le_treeCost` |
| Yao: quadrangle inequality for the cost | `cost_quadrangle` |
| Knuth's root inequalities | `root_le_root_right`, `root_le_root_left` |
| Knuth's algorithm: cost, steps `≤ 2n²` | `knuth_cost`, `knuth_steps` |
| key weights satisfy the hypotheses | `rangeWeight_quadrangle`, `rangeWeight_monotone` |
| `weightedCost = ∑` of subtree weights | `weightedCost_eq_treeCost` |
| `optTree` has `n` keys, costs `optCost`; `optCost` is minimal | `optTree_size`, `optTree_cost`, `optCost_le` |
| Knuth for key weights | `knuth_optCost`, `knuth_steps_le` |
| `StaticTree.cost t xs = weightedCost (counts n xs) t` | `staticCost_eq_weightedCost` |
| the best static tree for a sequence (`RF*`) | `optTree_static`, `optCost_le_static` |
| `H/3 ≤ RF* ≤ H` for the entropy bound `H = Bounds.staticCost` | `optCost_entropy` |
| `RF* ≤ m(⌊log₂ n⌋ + 1)` | `optCost_le_balanced` |

For the figure, `knuth → RF` is `knuth_optCost` with `optTree_static` and
`optCost_le_static`.

**Source.** E. N. Gilbert and E. F. Moore, *Variable-length binary encodings*
(1959); D. E. Knuth, *Optimum binary search trees*, Acta Informatica 1 (1971);
F. F. Yao, *Efficient dynamic programming using quadrangle inequalities*, STOC
1980. Book chapter "Static search trees", section "Optimal static trees". The
Isabelle AFP entry *Optimal Binary Search Trees* (Nipkow and Somogyi, 2018)
formalizes the same three steps and is a good template.

**Statement.** For key weights `w : List Nat` (gap weights may be added as a
second list), with `weightedCost w t = ∑ x, w[x] * (t.depth x + 1)`:

```lean
/-- The cubic recurrence C(i, j) = W(i, j) + min_r (C(i, r-1) + C(r+1, j)). -/
def RotationBST.Classical.Static.optCost (w : List Nat) : Nat
def RotationBST.Classical.Static.optTree (w : List Nat) : Tree

theorem optTree_size (w : List Nat) : (optTree w).size = w.length
theorem optTree_cost (w : List Nat) : weightedCost w (optTree w) = optCost w
theorem optCost_le (w : List Nat) (t : Tree) (h : t.size = w.length) :
    optCost w ≤ weightedCost w t

/-- Yao: the quadrangle inequality and monotonicity of the weight function
imply monotone optimal roots. Stated for an abstract interval weight. -/
theorem yao_monotone_roots ...

/-- Knuth's O(n²) algorithm computes the same cost, with a step count. -/
def knuth (w : List Nat) : Nat × Nat     -- (cost, steps)
theorem knuth_cost (w : List Nat) : (knuth w).1 = optCost w
theorem knuth_steps (w : List Nat) : (knuth w).2 ≤ 4 * (w.length + 1) ^ 2
```

and the link to the map of the bounds, with request counts as weights:
`StaticTree.cost t xs = weightedCost (counts n xs) t`, so `optCost` is `RF*`.

**Where.** `Classical/Static/Optimal/` (an `Abstract.lean`, with the
quadrangle inequality in its own file).

**Book.** In `classical/static-trees.md`, replace the box in "Optimal static
trees" with `@decl`s and a headline. In `boundsmap.js`, drop `todo: true` from
`knuth → RF` and give it `thms`. Update the tables in
`classical/part-classical.md` and `bounds/part-bounds.md`.

## 6. A dictionary model

**Status.** Formalized (branch `formalize-dictionary`, stacked on
`formalize-optimal-static`, 2026-11-10); the book update below is pending.
Definitions in `Models/Dictionary/Definitions/Abstract.lean`, results in
`Models/Dictionary/Abstract.lean` (`RotationBST.Dictionary.Results`), the splay
instance in `Algorithms/Splay/Updates/Dictionary/Abstract.lean`
(`RotationBST.Splay.Updates.Results`). The design:

- Trees with node data are `LabelledTree α` (the datum is balance data; keys
  stay inorder ranks). `Tree.unit` is a shape with no data.
- `Op`: `access x`, `insert k` (gap), `delete x`; `Op.Valid`, `Op.resize`,
  `Op.ValidSeq`. Split and join are not included.
- Primitive `Moves s t a e`: `a` rotations (data travel with nodes) and `e`
  data edits (`Edit`: change one node's datum), in any order.
- One structural change per update, `Splice t x u`: the node of rank `x` has at
  most one child and is removed (read backwards: a node is inserted at rank
  `x`, as a leaf or above a subtree).
- `Step s op t c e`. Access: moves; `c = 1 + depth x` in `s` plus rotations.
  Insert: moves, splice in, moves; `c = 1 + depth` of the new node plus all
  rotations. Delete: moves, splice out the node of rank `x`, or its predecessor
  or successor when `x` has two children (`Tree.TwoChildren`; the node at `x`
  keeps its datum), moves; `c = 1 + depth` of the spliced node plus rotations.
  `e` is the number of data edits.
- `Execution` over a list of operations; `Algorithm α` (online: past
  operations, tree, operation ↦ tree, `c`, `e`, certified by `Step`) with
  `runFrom`.

Differences from the requirements above: the search charge is taken in the
tree where the structural change happens, not necessarily the tree before the
operation. Without moves before the change (the classical trees) this is the
search path in the tree before the operation, and one rotation changes a
depth by at most one (`depth_rotations`), so moves before the change pay for
any shortcut. An insertion above a subtree pays the path to that subtree, not
to the gap below it. The generic parts of `Algorithms/Splay/Updates/` were not
moved: the splay model is a forest model with split and join, and it stays as
it is; the instance theorems relate the two. Checked names:

| Statement | Declaration |
|---|---|
| sizes; validity; data do not affect `c` | `Dictionary.Results.step_size`, `step_valid`, `step_unit`, `execution_unit` |
| an online algorithm executes every valid sequence | `Dictionary.Results.algorithm_execution` |
| a rotation changes a depth by at most one | `Dictionary.Results.depth_rotations` |
| the rotation model embeds, `c ≤ m + 2R` (target: `≤ 2(m + R)`) | `Dictionary.Results.of_execution` |
| searching without moving costs `∑ (1 + depth)` = `StaticTree.cost` | `Dictionary.Results.static_execution` |
| splay access, insert, delete are steps, `c ≤ 2, 3, 2 ×` splay's charge | `Splay.Updates.Results.dictionary_access`, `dictionary_insert`, `dictionary_delete` |

**Source.** Book chapter "Insertions and deletions" (`models/dictionary.md`).
It generalizes `Splay.Updates.Step` and `Splay.Updates.Execution` (book
section "Beyond single accesses", `algorithms/beyond.md`).

**Statement.** This is a design task more than a proof. Requirements:

- operations by rank, as in `Splay.Updates`: access rank `x`, insert at gap
  `k ≤ n`, delete rank `x` (split and join optional);
- cost: one unit per node of the search path in the tree before the
  operation, plus one per rotation (so a search that changes nothing costs
  `1 + depth`, the static cost `StaticTree.cost`); rank, colour or size changes counted
  separately (a second counter);
- node data of an arbitrary type, through `Models/Labelled/Metadata` or a
  tree type with a field per node;
- a `DictionaryAlgorithm` structure (state = tree with data; one step per
  operation) and an `Execution` over a list of operations;
- the splay update model as an instance, with a theorem relating the two cost
  accountings (splay's search path is part of its rotations);
- the bridge in the models map: a rotation execution is a dictionary
  execution with accesses only, whose search paths cost at most `m + R`:

```lean
theorem RotationBST.Dictionary.Results.of_execution {s t : Tree} {xs : List Nat} {k : Nat}
    (h : Execution s xs t k) :
    ∃ c, Dictionary.Execution s (xs.map .access) t c ∧ c ≤ 2 * (xs.length + k)
```

**Where.** `Models/Dictionary/` (an `Abstract.lean` for definitions and the
bridge). Move the generic parts of `Algorithms/Splay/Updates/` there.

**Book.** Rewrite `models/dictionary.md` around the definitions, and shorten
the "Updates" section of `algorithms/beyond.md` to the splay instance. In
`book/src/assets/viz/modelsmap.js`, drop `todo: true` from the `DIC` node and
the `ROT → DIC` edge, and give the edge `thms`. Update the models table in
`models/part-models.md`.

## 7. Rank-balanced trees

**Status.** Partly formalized (branch `formalize-rank-balanced`, stacked on
`formalize-weight-balanced`, 2026-11-10): the static half. Statements in
`Classical/RankBalanced/Abstract.lean`
(`RotationBST.Classical.RankBalanced.Results`), definitions in
`Classical/RankBalanced/Definitions/Abstract.lean`. Still open: insertion and
deletion with bottom-up rebalancing as dictionary steps (entry 6 is done),
their rotation counts, and the amortized rank-change bounds.

The definitions are as below: `RankedTree := LabelledTree Int`, `rank`
(`-1` for the empty tree), `Rule` (`avl`, `redBlack`, `wavl`), `Rule.Local`,
`Valid`, plus `NoZeroChild` for the red-black rule. Every rank is required to
be nonnegative; red-black uses "rank differences 0 or 1, no 0-child has a
0-child", WAVL "rank differences 1 or 2, leaves have rank 0".

Differences from the targets below: heights count nodes
(`Classical.Static.height` of the shape), one more than edges. So the AVL
bound is `height ≤ log_φ(n + 1)` with `φ = Real.goldenRatio`, rather than a
decimal constant (in edges it is `log_φ(n + 1) − 1 < 1.4405 log₂(n + 2)`; the
decimal form is not proved). The red-black bound is `2 log₂(n + 1)` in nodes,
stronger than the target in edges. The WAVL bound is `rank + 1 ≤ 2 log₂(n + 1)`.
`wavl_height_insertions` is not done (it needs the insertion procedure).

| Statement | Declaration (under `RankBalanced.Results`) |
|---|---|
| AVL: rank = height in edges; `height ≤ log_φ(n + 1)` | `avl_height_rank`, `avl_height` |
| red-black: `height ≤ 2 log₂(n + 1)` | `redBlack_height` |
| WAVL: `rank + 1 ≤ 2 log₂(n + 1)`, same for height | `wavl_rank`, `wavl_height` |
| every AVL tree is a WAVL tree | `avl_wavl` |

**Source.** B. Haeupler, S. Sen and R. E. Tarjan, *Rank-balanced trees*, ACM
TALG 11(4) (2015), for the framework and WAVL trees; G. M. Adelson-Velsky and
E. M. Landis (1962) for AVL trees; R. Bayer (1972) and L. J. Guibas and
R. Sedgewick (1978) for red-black trees; R. E. Tarjan, *Updating a balanced
search tree in O(1) rotations*, IPL 16 (1983). Book chapter "Rank-balanced
trees" (`classical/rank-balanced.md`). Needs entry 6.

**Statement.** One representation, one rebalancing procedure per rule, three
rules:

```lean
/-- A tree with an integer rank in each node; a missing child has rank -1.
`height` below is defined on this type, counting edges. -/
def RotationBST.Classical.RankBalanced.RankedTree := ...
inductive Rule | avl | redBlack | wavl
def Valid (r : Rule) : RankedTree → Prop

theorem avl_height (t) (h : Valid .avl t) :
    (t.height : ℝ) < 1.4405 * Real.logb 2 (t.size + 2)
theorem redBlack_height (t) (h : Valid .redBlack t) :
    (t.height : ℝ) ≤ 2 * Real.logb 2 (t.size + 1)
theorem wavl_rank (t) (h : Valid .wavl t) : (t.rank : ℝ) ≤ 2 * Real.logb 2 (t.size + 1)
theorem wavl_height_insertions ... -- height ≤ log_φ m after m insertions

-- insert and delete preserve Valid r and the inorder; rotation counts:
theorem avl_insert_rotations  : rotations ≤ 2
theorem redBlack_insert_rotations : rotations ≤ 2
theorem redBlack_delete_rotations : rotations ≤ 3
theorem wavl_update_rotations : rotations ≤ 2
-- amortized: total rank changes over any sequence of updates from empty ≤ C · #updates
theorem redBlack_amortized_rank_changes ...
theorem wavl_amortized_rank_changes ...
```

**Proof idea.** Heights: the smallest valid tree of each rank, by induction
(Fibonacci for AVL). Rotation counts: case analysis of bottom-up rebalancing,
shared across rules. Amortization: the potential functions of Haeupler, Sen
and Tarjan (count 0,1 / 2,2 nodes).

**Where.** `Classical/RankBalanced/` (definitions and the rebalancing steps in
`Abstract.lean`, one file per rule).

**Book.** Replace the boxes in `classical/rank-balanced.md` with `@decl`s and
headlines. Update `classical/part-classical.md` and `bounds/part-bounds.md`
(the "Balanced trees" row), and the `balanced → BAL` edge of `boundsmap.js`.

## 8. Weight-balanced and scapegoat trees

**Status.** Partly formalized (branch `formalize-weight-balanced`, stacked on
`formalize-dictionary`, 2026-11-10): the static half. Statements in
`Classical/WeightBalanced/Abstract.lean`
(`RotationBST.Classical.WeightBalanced.Results`), definitions in
`Classical/WeightBalanced/Definitions/Abstract.lean`. Still open: BB[α]
rebalancing by single and double rotations with `O(m)` rotations, scapegoat
trees as a `Dictionary.Algorithm` with their height invariant and `O(m log n)`
total cost, and the common "a perfectly balanced subtree needs
`Ω((β - 1/2)s)` updates" lemma.

**Scapegoat trees: formalized** (branch `formalize-scapegoat`, stacked on
`formalize-random-depth`, 2026-11-10). Statements in
`Classical/Scapegoat/Abstract.lean` (`RotationBST.Classical.Scapegoat.Results`),
definitions in `Classical/Scapegoat/Definitions/Abstract.lean`. The parameter
`α` is a rational with `1/2 < α < 1` (so `step` and `run` are executable); the
state is the shape and `N`, the largest key count since the last full
rebuild. Insertion adds a leaf; if its depth `d` has `α^d N < 1` it rebuilds
(`rebuild`, entry 8) the deepest subtree on the path whose height exceeds
`log_{1/α}` of its size. Deletion is plain (successor for two children) and
rebuilds the whole tree when fewer than `αN` keys remain. Costs are the
dictionary model's (entry 6).

| Statement | Declaration (under `Scapegoat.Results`) |
|---|---|
| every operation is a dictionary step; runs are dictionary executions | `step_dictionary`, `run_execution` |
| from empty, every depth `≤ log_{1/α} n + 1` | `reachable_depth` |
| from empty, total cost `≤ ∑ bound α nᵢ`, `bound α n = (2/(2α−1) + 1)(log_{1/α} n + 2) + 1 + 2α/(1−α)` | `total_cost` |
| hence `≤ m · bound α m` | `total_cost_le` |

The analysis (`Classical/Scapegoat/Analysis.lean`) uses the potential
`(2/(2α−1)) Σ (|size l − size r| − 1)⁺ + (2α/(1−α))(N − n)` and the invariant
`n ≤ N`, `αN ≤ n`, `α^depth N ≥ 1`. Not done: BB[α], and a
`Dictionary.Algorithm` packaging (the count `N` is not stored in the tree).

Differences from the targets below: heights use `Classical.Static.height`
(nodes on a longest path, the same as `Tango.height`, which `Classical` cannot
import); the height bound needs only `0 < β < 1`; `rebuild` reaches
`Classical.Static.balanced` exactly (not just its height), by rotating to the
right spine and then running the spine procedure of the balanced tree
backwards, so the Day–Stout–Warren compression is not used; the height
statement needs `0 < n`. Checked names:

| Statement | Declaration |
|---|---|
| `height ≤ log_{1/β}(n + 1)` for `β`-balanced trees | `WeightBalanced.Results.height_le` |
| the balanced tree is `β`-balanced for `β ≥ 2/3` | `WeightBalanced.Results.balanced_balanced` |
| `rebuild t` is the balanced tree, height `⌊log₂ n⌋ + 1` | `WeightBalanced.Results.rebuild_tree`, `rebuild_height` |
| it is reached by exactly `(rebuild t).2 ≤ 2n` rotations | `WeightBalanced.Results.rebuild_rotations`, `rebuild_cost` |
| minimum height: `height t ≥ ⌊log₂ n⌋ + 1`; the balanced tree attains it | `Static.Results.log2_lt_height`, `balanced_height` |

**Source.** J. Nievergelt and E. M. Reingold, *Binary search trees of bounded
balance*, SIAM J. Comput. 2(1) (1973); N. Blum and K. Mehlhorn, *On the
average number of rebalancing operations in weight-balanced trees*, TCS 11
(1980); A. Andersson, *Improving partial rebuilding by using simple balance
criteria*, WADS 1989; I. Galperin and R. L. Rivest, *Scapegoat trees*, SODA
1993; A. C. Day (1976) and Q. F. Stout and B. L. Warren (1986) for rebuilding.
Book chapter "Weight-balanced trees" (`classical/weight-balanced.md`). Needs
entry 6. Mathlib's `Ordnode` (Adams' weight-balanced trees) may help with the
invariant.

**Statement.**

```lean
/-- Every child's weight (size + 1) is at most β times its parent's. -/
def RotationBST.Classical.WeightBalanced.Balanced (β : ℝ) : Tree → Prop

-- `Tango.height` counts nodes on the longest root-to-leaf path.
theorem height_le (β) (hβ : 1/2 < β ∧ β < 1) (t) (h : Balanced β t) :
    (Tango.height t : ℝ) ≤ Real.logb (1/β) (t.size + 1)

/-- Rebuilding inside a subtree: an explicit linear procedure (to the right
spine, then compress), returning a tree of minimum height and at most 2s
rotations. Day–Stout–Warren's compression does not build `Tango.balanced`
exactly; either target it with a different second phase, or state the
height only, as here. -/
def rebuild (t : Tree) : Tree × Nat
theorem rebuild_spec (t : Tree) :
    (rebuild t).1.size = t.size ∧ Tango.height (rebuild t).1 = Nat.log2 t.size + 1 ∧
      (rebuild t).2 ≤ 2 * t.size ∧ Rotations t (rebuild t).1 (rebuild t).2

-- BB[α], for 2/11 < α ≤ 1 - √2/2: single/double rotations restore balance,
-- and the total number of rotations over m updates from empty is O(m).
-- Scapegoat trees: height ≤ log_{1/α} n + 1, and the total cost of m updates
-- from empty, rebuilding included, is O(m log n).
```

**Proof idea.** The common lemma: a subtree that is perfectly balanced needs
`Ω((β - 1/2) s)` updates inside it before it violates `Balanced β`. For
`rebuild`, `Geometry.reset` already goes through the right spine; make the
two halves executable and lift them under `inLeft`/`inRight`.

**Where.** `Classical/WeightBalanced/`, with `rebuild` in its own file (it may
also serve `Models/Rotation/`).

**Book.** Replace the boxes in `classical/weight-balanced.md`. Update
`classical/part-classical.md`, `bounds/part-bounds.md` and the `balanced → BAL`
edge of `boundsmap.js`.

## 9. Random search trees

**Status.** Step (a) formalized (branch `formalize-random-depth`, stacked on
`formalize-rank-balanced`, 2026-11-10). Step (b), first part, formalized
(branch `formalize-random-insertion`, stacked on `formalize-scapegoat`):
`Classical.Random.Results.insertAll_treap` (for a permutation `order` of the
`n` keys, `insertAll order`, plain insertion by comparison into a key-labelled
tree, erases to the treap of `order.idxOf`), and its consequence for random
BSTs, `random_bst_depth` (`H(x + 1) + H(n - x) - 2` when the insertion order is
uniformly random) and `random_bst_depth_le` (`2 ln n`). Still open in (b):
treap insertion and deletion by rotations with history independence, and the
expected number of rotations per update. Step (c) is open. The
statement is the target (a) below with explicit casts:
`RotationBST.Classical.Random.Results.expected_depth` in
`Classical/Random/Abstract.lean`, with `average` meaning
`Treap.Random.average` and `harmonic` Mathlib's (cast from `ℚ`). The proof is
in `Classical/Random/Depth.lean`, not next to `Structures/Treap/Random/Common.lean`:
it needs `LazyFinger.searchPath_length` from `Bounds/`, which `Structures/`
may not import. A corollary `expected_depth_le` bounds every expected depth by
`2 ln n`, using `H(k) ≤ 1 + ln k` proved there (Mathlib's
`harmonic_le_one_add_log` needs the integration library, which is not built
locally).

**Source.** T. N. Hibbard, *Some combinatorial properties of certain trees
with applications to searching and sorting*, JACM 9 (1962); R. Seidel and
C. R. Aragon, *Randomized search trees*, Algorithmica 16 (1996); J. Vuillemin,
*A unifying look at data structures*, CACM 23 (1980); C. Martínez and S. Roura,
*Randomized binary search trees*, JACM 45 (1998); R. E. Tarjan, C. Levy and
S. Timmel, *Zip trees*, ACM TALG 17(4) (2021). Book chapter "Random search
trees" (`classical/random-trees.md`). The Isabelle AFP entry *Treaps*
(Haslbeck, Eberl and Nipkow) and their paper *Verified analysis of random
binary tree structures* (JAR 2020) cover similar ground.

**Statement.** In three steps, from small to medium:

```lean
-- (a) Expected depth, a corollary of Treap.Random.common_ancestor_probability
-- with x = y and uniform weights. Proved next to it, stated in
-- Classical/Random/Abstract.lean.
theorem RotationBST.Classical.Random.Results.expected_depth (n x : Nat) (hx : x < n)
    (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) 0) :
    average (fun _ => 1) (Finset.range n) (fun xs => ((T xs).depth x : ℝ)) =
      (harmonic (x + 1) : ℝ) + harmonic (n - x) - 2

-- (b) Insertion in a given order without rebalancing builds the treap of the
-- positions; treap insertion and deletion produce the treap of the new key
-- set (history independence); expected rotations per update < 2.
theorem bstInsertAll_treap (order : List Nat) ... :
    Geometric.Heap order.idxOf (bstInsertAll order) 0
theorem expected_insert_rotations ... : average ... < 2

-- (c) Randomized BSTs produce the uniform treap distribution after every
-- operation; zip trees produce the treap of their (rank, key) priorities.
```

**Where.** (a) in `Structures/Treap/Random/` next to `Common.lean`, stated in a
new `Classical/Random/Abstract.lean`. (b) and (c) in `Classical/Random/`,
using the dictionary model of entry 6 for updates.

**Book.** Replace the boxes in `classical/random-trees.md` with `@decl`s and
headlines. Update `classical/part-classical.md` ("partly formalized"),
`bounds/part-bounds.md` and the `random → BAL` edge of `boundsmap.js`.

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
