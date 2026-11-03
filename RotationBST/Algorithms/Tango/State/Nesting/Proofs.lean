module

public import RotationBST.Algorithms.Tango.State.Nesting.Defs
public import RotationBST.Algorithms.Tango.State.Canonical.Proofs
public import RotationBST.Algorithms.Tango.State.Bounds

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem branch_fringe (children : List ComponentNesting) :
    (ComponentNesting.branch children).fringe = children := rfl

/-- Flattening the root component leaves exactly its marked fringe signatures. -/
theorem nesting_fringe (s : MarkedTree) : s.nesting.fringe = s.fringe.map nesting := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp only [nesting, branch_fringe, fringe, Bool.false_eq_true, ite_false, ite_true,
        List.map_append, List.map_singleton, il, ir]

/-- Reshaping one auxiliary component preserves the nesting of every component. -/
theorem nesting_of_fringe {s t : MarkedTree} (same : s.fringe = t.fringe) : s.nesting = t.nesting := by
  have sizes := region_size_eq same
  have nested := congrArg (List.map nesting) same
  rw [← nesting_fringe, ← nesting_fringe] at nested
  cases s <;> cases t
  · rfl
  · simp only [region, Pointer.Lazy.Skeleton.size] at sizes; omega
  · simp only [region, Pointer.Lazy.Skeleton.size] at sizes; omega
  · exact congrArg ComponentNesting.branch nested

theorem canonical_represents (reference : Tree) (past : List Nat) :
    Represents (canonical reference 0 past) reference past := by
  have spec := canonical_decomposition reference 0 past
  exact ⟨by rw [canonical_tree], spec.2.2 ▸ List.Perm.refl _, spec.1⟩

theorem canonical_maintains (reference : Tree) (past : List Nat) :
    Maintains (canonical reference 0 past) reference past := ⟨canonical_represents reference past, rfl⟩

theorem initial_maintains (reference : Tree) : Maintains (initial reference) reference [] := by
  simpa only [canonical_initial] using canonical_maintains reference []

theorem maintains_of_fringe {s t : MarkedTree} {reference : Tree} {past : List Nat}
    (maintained : Maintains s reference past) (same : s.fringe = t.fringe) :
    Maintains t reference past :=
  ⟨represents_of_fringe maintained.1 same, (nesting_of_fringe same).symm.trans maintained.2⟩

/-- The computed final splay preserves the full component-nesting invariant. -/
theorem maintained_splayRoot (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) (x : Nat) (valid : x ∈ s.region.keys 0) :
    Access s.tree (s.splayRoot (Geometric.Region.index s.region 0 x)).1.tree x
        (s.splayRoot (Geometric.Region.index s.region 0 x)).2 ∧
      Maintains (s.splayRoot (Geometric.Region.index s.region 0 x)).1 reference past ∧
      ((s.splayRoot (Geometric.Region.index s.region 0 x)).2 : ℝ) +
        (s.splayRoot (Geometric.Region.index s.region 0 x)).1.potential - s.potential ≤
          3 * Real.logb 2 (height reference) + 1 := by
  have member : (0, s.region) ∈ s.components 0 := by
    cases s with
    | nil => simp [region, Geometric.Region.keys] at valid
    | node l r cl cr => simp [components, rootComponent]
  have hs := component_size maintained.1 member
  obtain ⟨hf, _, _, bound⟩ := splayRoot_spec s _ (Geometric.Region.index_valid valid)
  refine ⟨splayRoot_key s x valid, maintains_of_fringe maintained hf, ?_⟩
  linarith [Splay.Updates.log_nat_mono hs]

/-- The final auxiliary access preserves the full component-nesting invariant. -/
theorem maintained_access (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) (x : Nat) (valid : x ∈ s.region.keys 0) :
    ∃ u : MarkedTree, ∃ cost : Nat, Access s.tree u.tree x cost ∧ Maintains u reference past ∧
      (cost : ℝ) + u.potential - s.potential ≤ 3 * Real.logb 2 (height reference) + 1 := by
  exact ⟨_, _, maintained_splayRoot s reference past maintained x valid⟩

end RotationBST.Tango.MarkedTree
