module

public import RotationBST.Structures.FingerHand.Packed.Initialization

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem forState_represents {k : Nat} (s : Multifinger.State k) : (forState s).Represents s :=
  ⟨forState_valid s, forState_reference s, build_labels (stateMarks s) s.tree 0⟩

theorem Represents.size {k : Nat} {h : Hand} {s : Multifinger.State k} (rep : h.Represents s) :
    h.tree.size = s.tree.size := (tree_size rep.1).trans (congrArg Tree.size rep.2.1)

theorem Represents.count {k : Nat} {h : Hand} {s : Multifinger.State k} (rep : h.Represents s) :
    h.count ≤ 2 * (k + 1) := by
  rw [← labels_size h 0, rep.2.2]
  exact ofState_size s

theorem Represents.finger {k : Nat} {h : Hand} {s : Multifinger.State k} (rep : h.Represents s)
    (valid : s.Valid) (i : Fin k) : s.position i ∈ (h.labels 0).inorder := by
  rw [rep.2.2]
  exact ofState_finger s valid i

/-- Navigation holds for every maintained hand satisfying the invariant, not
only for the canonical constructor. No rebalancing or repacking is performed. -/
theorem Represents.visit {k : Nat} {h : Hand} {s : Multifinger.State k} (rep : h.Represents s)
    (valid : s.Valid) (i : Fin k) :
    ∃ (v : Pointer.Config) (m : Nat), Pointer.Trace ⟨h.tree, []⟩ v m ∧
      v.key? = some (s.position i) ∧ Pointer.Trace v ⟨h.tree, []⟩ m ∧ m < 10 * (k + 1) := by
  obtain ⟨v, m, down, key, up, bound⟩ := Hand.visit rep.1 _ (rep.finger valid i)
  have count := rep.count
  exact ⟨v, m, down, key, up, by omega⟩

theorem Represents.serves {k : Nat} {h : Hand} {s : Multifinger.State k} (rep : h.Represents s)
    (valid : s.Valid) (i : Fin k) :
    ∃ m, Pointer.Serves h.tree h.tree (s.position i) m ∧ m ≤ 20 * (k + 1) := by
  obtain ⟨v, m, down, key, up, bound⟩ := rep.visit valid i
  exact ⟨1 + m + m, ⟨v, ⟨h.tree, []⟩, m, m, down, key, up, rfl, rfl⟩, by omega⟩

end RotationBST.FingerHand.Hand
