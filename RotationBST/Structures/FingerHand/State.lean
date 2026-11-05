module

public import RotationBST.Structures.FingerHand.Keys
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.FingerHand

theorem stateMarks_card {k : Nat} (s : Multifinger.State k) : (stateMarks s).card ≤ k + 1 := by
  have h := Finset.card_insert_le (rootRank s.tree) (Finset.univ.image s.position)
  have hi := Finset.card_image_le (f := s.position) (s := Finset.univ)
  have he : (Finset.univ : Finset (Fin k)).card = k := by simp
  unfold stateMarks
  omega

/-- The compressed skeleton has size depending only on the number of fingers,
including the root anchor, not on the total number of keys. -/
theorem ofState_size {k : Nat} (s : Multifinger.State k) : (ofState s).erase.size ≤ 2 * (k + 1) := by
  have h := compress_size (stateMarks s) s.tree 0
  have hc := stateMarks_card s
  unfold ofState
  omega

/-- If the permanent root finger is already included among the `k` fingers,
no extra anchor is needed and the usual `2k` bound applies. -/
theorem ofState_size_root_marked {k : Nat} (s : Multifinger.State k)
    (rootMarked : rootRank s.tree ∈ Finset.univ.image s.position) :
    (ofState s).erase.size ≤ 2 * k := by
  have h := compress_size (stateMarks s) s.tree 0
  have hc := Finset.card_image_le (f := s.position) (s := Finset.univ)
  have hm : (stateMarks s).card ≤ k := by
    simpa only [stateMarks, Finset.insert_eq_of_mem rootMarked, Finset.card_univ, Fintype.card_fin] using hc
  unfold ofState
  omega

theorem ofState_finger {k : Nat} (s : Multifinger.State k) (valid : s.Valid) (i : Fin k) :
    s.position i ∈ (ofState s).inorder := by
  apply marked_mem (stateMarks s) s.tree 0 (s.position i)
  · rw [Representation.Bridge.inorder_label]
    simpa using valid i
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem ofState_root {k : Nat} (s : Multifinger.State k) (nonempty : 0 < s.tree.size) :
    rootRank s.tree ∈ (ofState s).inorder := by
  apply marked_mem (stateMarks s) s.tree 0 (rootRank s.tree)
  · rw [Representation.Bridge.inorder_label]
    cases ht : s.tree with
    | nil => simp [ht, Tree.size] at nonempty
    | node l r => simp [rootRank, Tree.size]; omega
  · exact Finset.mem_insert_self _ _

end RotationBST.FingerHand
