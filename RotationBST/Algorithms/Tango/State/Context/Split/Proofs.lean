module

public import RotationBST.Algorithms.Tango.State.Context.Split.Defs
public import RotationBST.Algorithms.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.Context

theorem splitComponent_spec (fs : List Frame) :
    fs = (splitComponent fs).1 ++ (splitComponent fs).2 ∧
      (∀ f ∈ (splitComponent fs).1, f.marked = false) ∧ Boundary (splitComponent fs).2 := by
  induction fs with
  | nil => exact ⟨rfl, by simp [splitComponent], trivial⟩
  | cons f fs ih =>
    cases marked : f.marked
    · simp only [splitComponent, marked, Bool.false_eq_true, ite_false]
      refine ⟨?_, ?_, ih.2.2⟩
      · rw [List.cons_append, ← ih.1]
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact marked
        · exact ih.2.1 g hg
    · simp only [splitComponent, marked, ite_true]
      exact ⟨rfl, by simp, marked⟩

end RotationBST.Tango.Context
