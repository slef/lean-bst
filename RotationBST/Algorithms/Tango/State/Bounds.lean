module

public import RotationBST.Algorithms.Tango.State.Access
public import RotationBST.Algorithms.Tango.Paths.Bounds

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Region

/-- The preferred-path invariant bounds every actual auxiliary component. -/
theorem component_size {s : MarkedTree} {reference : Tree} {past : List Nat}
    (represented : Represents s reference past) {p : Nat × Region}
    (member : p ∈ s.components 0) : p.2.size ≤ height reference := by
  have hm : p.2.keys p.1 ∈ (s.components 0).map (fun p => p.2.keys p.1) :=
    List.mem_map.mpr ⟨p, member, rfl⟩
  have target := represented.2.1.mem_iff.mp hm
  obtain ⟨path, hp, he⟩ := List.mem_map.mp target
  rw [← keys_card p.2 p.1, ← he]
  exact Nat.le_trans (List.toFinset_card_le path) (preferredPaths_size reference past path hp)

theorem root_access_bound (s : MarkedTree) (reference : Tree) (past : List Nat)
    (represented : Represents s reference past) (x : Nat) (valid : x ∈ s.region.keys 0) :
    ∃ u : MarkedTree, ∃ cost : Nat, Access s.tree u.tree x cost ∧ Represents u reference past ∧
      (cost : ℝ) + u.potential - s.potential ≤ 3 * Real.logb 2 (height reference) + 1 := by
  have member : (0, s.region) ∈ s.components 0 := by
    cases s with
    | nil => simp [region, keys] at valid
    | node l r cl cr => simp [components, rootComponent]
  have hs := component_size represented member
  obtain ⟨u, cost, hf, served, bound⟩ := access s x valid
  refine ⟨u, cost, served, represents_of_fringe represented hf, ?_⟩
  linarith [Splay.Updates.log_nat_mono hs]

end RotationBST.Tango.MarkedTree
