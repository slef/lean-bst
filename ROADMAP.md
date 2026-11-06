# Roadmap

Results that the book mentions but the library does not prove yet. Each entry
gives the source, a target statement, where it belongs (see "Where new results
go" in [docs/organization.md](docs/organization.md)), and what to update in the
book once it is proved.

The target statements are suggestions. Change the constants or the shape if the
proof calls for it, but keep the usual conventions: uniform natural constants,
one unit per request, and an explicit startup term.

## 1. Dynamic finger implies static finger

**Source.** Classical. Shown as the dashed arrow DF → SF in the map of the
bounds (book chapter "Adaptive bounds", section "A map of the bounds").

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
`DF → SF` edges and give them `thms`. In `book/src/chapters/12-bounds.md`, show
the new declarations with `@decl`, link them in the relations table, and update
the "Dynamic finger" and "What is not formalized" sections.

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
`splay → OPT` edge and give it `thms`. In `book/src/chapters/12-bounds.md`,
update the algorithms table and the "What is not formalized" section, and add a
headline result to the splay analysis chapter (`19-analysis.md`) or a new
chapter after it.
