module

public import RotationBST.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

theorem offset_append (xs ys : List Frame) (lo : Nat) :
    offset (xs ++ ys) lo = offset xs (offset ys lo) := by
  induction xs with
  | nil => rfl
  | cons f fs ih => simp only [List.cons_append, offset, ih]

/-- Locate the specified occurrence of a fringe component. Keeping its absolute
key offset distinguishes identical unlabelled subtrees at different positions. -/
theorem locate_fringeAt (s : MarkedTree) (lo : Nat) (child : MarkedTree) (atKey : Nat)
    (member : (atKey, child) ∈ s.fringeAt lo) (nonempty : child ≠ .nil) :
    ∃ fs : List Frame, fs ≠ [] ∧ Boundary fs ∧ plug fs child = s ∧ offset fs lo = atKey := by
  induction s generalizing lo with
  | nil =>
    have h : child = .nil := (Prod.mk.inj (List.mem_singleton.mp member)).2
    exact False.elim (nonempty h)
  | node l r cl cr il ir =>
    change (atKey, child) ∈
      (if cl then [(lo, l)] else l.fringeAt lo) ++
      (if cr then [(lo + l.tree.size + 1, r)] else r.fringeAt (lo + l.tree.size + 1)) at member
    rcases List.mem_append.mp member with hm | hm
    · cases cl
      · obtain ⟨fs, hn, hb, hp, ho⟩ := il lo hm
        refine ⟨fs ++ [.left r false cr], by simp, ?_, ?_, ?_⟩
        · cases fs with
          | nil => contradiction
          | cons f fs => exact hb
        · rw [plug_append, hp]; rfl
        · simpa only [offset_append, offset, Frame.offset] using ho
      · obtain ⟨hk, hc⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
        subst child
        exact ⟨[.left r true cr], by simp, rfl, rfl, hk.symm⟩
    · cases cr
      · obtain ⟨fs, hn, hb, hp, ho⟩ := ir (lo + l.tree.size + 1) hm
        refine ⟨fs ++ [.right l false cl], by simp, ?_, ?_, ?_⟩
        · cases fs with
          | nil => contradiction
          | cons f fs => exact hb
        · rw [plug_append, hp]; rfl
        · simpa only [offset_append, offset, Frame.offset] using ho
      · obtain ⟨hk, hc⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
        subst child
        exact ⟨[.right l true cl], by simp, rfl, rfl, hk.symm⟩

end RotationBST.Tango.Context
