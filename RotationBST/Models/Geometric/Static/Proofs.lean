module

public import RotationBST.Models.Geometric.Static.Abstract
public import RotationBST.Models.Geometric.Basic

@[expose] public section
namespace RotationBST.Geometric

/-- Any execution that touches connected root regions of one fixed BST has
an arborally satisfied geometric view. Rotating executions require more. -/
theorem rootedRows_ass (t : Tree) (lo : Nat) (P : Finset Point)
    (h : RootedRows t lo P) : ASS P := by
  induction t generalizing lo P with
  | nil => simpa only [RootedRows] using h ▸ ass_empty
  | node l r il ir =>
    obtain ⟨root, hl, hr⟩ := h
    have sl := il lo _ hl
    have sr := ir (lo + l.size + 1) _ hr
    intro a ha b hb hx hy
    by_cases bothLeft : a.1 < lo + l.size ∧ b.1 < lo + l.size
    · obtain ⟨p, hp, hpa, hpb, hrect⟩ := sl a (Finset.mem_filter.mpr ⟨ha, bothLeft.1⟩)
        b (Finset.mem_filter.mpr ⟨hb, bothLeft.2⟩) hx hy
      exact ⟨p, (Finset.mem_filter.mp hp).1, hpa, hpb, hrect⟩
    by_cases bothRight : lo + l.size < a.1 ∧ lo + l.size < b.1
    · obtain ⟨p, hp, hpa, hpb, hrect⟩ := sr a (Finset.mem_filter.mpr ⟨ha, bothRight.1⟩)
        b (Finset.mem_filter.mpr ⟨hb, bothRight.2⟩) hx hy
      exact ⟨p, (Finset.mem_filter.mp hp).1, hpa, hpb, hrect⟩
    have between : min a.1 b.1 ≤ lo + l.size ∧ lo + l.size ≤ max a.1 b.1 := by omega
    by_cases haRoot : a.1 = lo + l.size
    · refine ⟨(lo + l.size, b.2), root b hb, ?_, ?_, ?_⟩
      · intro he; have := congrArg (fun p : Point => p.2) he; exact hy this.symm
      · intro he; have := congrArg (fun p : Point => p.1) he; exact hx (haRoot.trans this)
      · exact ⟨between.1, between.2, min_le_right _ _, le_max_right _ _⟩
    · refine ⟨(lo + l.size, a.2), root a ha, ?_, ?_, ?_⟩
      · intro he; have := congrArg (fun p : Point => p.1) he; exact haRoot this.symm
      · intro he; have := congrArg (fun p : Point => p.2) he; exact hy this
      · exact ⟨between.1, between.2, min_le_left _ _, le_max_left _ _⟩

end RotationBST.Geometric
