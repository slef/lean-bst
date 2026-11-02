module

public import RotationBST.Representation.ArbitraryKeys
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace RotationBST.Representation.Bridge

/-- A root access to implicit rank `x` is exactly an access to the corresponding
arbitrary key. Distinctness is necessary for the converse: equal labels cannot
identify a unique inorder position. -/
theorem arbitrary_access_iff {α : Type} (s t : LabelledTree α)
    (keys : s.inorder = t.inorder) (distinct : s.inorder.Nodup)
    (x k : Nat) (valid : x < s.inorder.length) :
    Access s.erase t.erase x k ↔ LabelledTree.Access s t s.inorder[x] k := by
  cases t with
  | nil => simp [LabelledTree.inorder] at keys; simp [keys] at valid
  | node l y r =>
      have hlen : l.inorder.length < s.inorder.length := by
        rw [keys]; simp [LabelledTree.inorder]
      have hroot : s.inorder[l.inorder.length] = y := by
        simp [keys, LabelledTree.inorder]
      unfold Access LabelledTree.Access
      rw [arbitrary_rotations_iff s (.node l y r) keys]
      change (_ ∧ l.erase.size = x) ↔ (_ ∧ y = s.inorder[x])
      constructor
      · rintro ⟨hr, hx⟩
        refine ⟨hr, ?_⟩
        have hi : l.inorder.length = x := (inorder_length l).trans hx
        simpa only [hi] using hroot.symm
      · rintro ⟨hr, hy⟩
        refine ⟨hr, ?_⟩
        have hi : l.inorder.length = x := distinct.getElem_inj_iff.mp (hroot.trans hy)
        exact (inorder_length l).symm.trans hi

end RotationBST.Representation.Bridge
