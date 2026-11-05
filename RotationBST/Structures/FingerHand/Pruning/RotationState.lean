module

public import RotationBST.Structures.FingerHand.Pruning.State
public import RotationBST.Models.Pointer.Navigation

@[expose] public section
namespace RotationBST.FingerHand

/-- A non-root rotation preserves the global root rank. -/
theorem rootRank_plug_congr (cs : List Pointer.Frame) {s t : Tree} (size : s.size = t.size)
    (nonempty : cs ≠ []) : rootRank (Pointer.plug cs s) = rootRank (Pointer.plug cs t) := by
  cases cs using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton cs f =>
    cases f <;> simp only [Pointer.plug_append, Pointer.plug, rootRank]
    exact Pointer.plug_size_congr cs size

/-- Adding the old parent as a temporary mark gives the same marks before and
after a right rotation. At the root, the new anchor is the rotating finger. -/
theorem rotation_marks_right {fingers : Nat} (position : Fin fingers → Nat) (i : Fin fingers)
    (a b c : Tree) (anc : List Pointer.Frame)
    (finger : position i = Pointer.offset anc + a.size) :
    insert (Pointer.offset anc + (Tree.node a b).size)
        (stateMarks (⟨Pointer.plug anc (.node (.node a b) c), position⟩ : Multifinger.State fingers)) =
      insert (Pointer.offset anc + (Tree.node a b).size)
        (stateMarks (⟨Pointer.plug anc (.node a (.node b c)), position⟩ : Multifinger.State fingers)) := by
  by_cases empty : anc = []
  · subst anc
    simp only [Pointer.offset, Nat.zero_add] at finger
    have child : a.size ∈ Finset.univ.image position := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, finger⟩
    simp only [stateMarks, Pointer.offset, Nat.zero_add, Pointer.plug, rootRank,
      Finset.insert_idem, Finset.insert_eq_of_mem child]
  · have same := rootRank_plug_congr anc (s := .node (.node a b) c) (t := .node a (.node b c))
      (by simp only [Tree.size]; omega) empty
    simp only [stateMarks, same]

theorem rotation_marks_left {fingers : Nat} (position : Fin fingers → Nat) (i : Fin fingers)
    (a b c : Tree) (anc : List Pointer.Frame)
    (finger : position i = Pointer.offset anc + a.size + 1 + b.size) :
    insert (Pointer.offset anc + a.size)
        (stateMarks (⟨Pointer.plug anc (.node a (.node b c)), position⟩ : Multifinger.State fingers)) =
      insert (Pointer.offset anc + a.size)
        (stateMarks (⟨Pointer.plug anc (.node (.node a b) c), position⟩ : Multifinger.State fingers)) := by
  by_cases empty : anc = []
  · subst anc
    simp only [Pointer.offset, Nat.zero_add] at finger
    have child : (Tree.node a b).size ∈ Finset.univ.image position :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp only [Tree.size]; omega⟩
    simp only [stateMarks, Pointer.offset, Nat.zero_add, Pointer.plug, rootRank,
      Finset.insert_idem, Finset.insert_eq_of_mem child]
  · have same := rootRank_plug_congr anc (s := .node a (.node b c)) (t := .node (.node a b) c)
      (by simp only [Tree.size]; omega) empty
    simp only [stateMarks, same]

end RotationBST.FingerHand
