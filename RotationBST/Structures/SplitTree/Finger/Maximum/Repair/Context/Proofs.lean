module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Balance
public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem maximumRepairContext_balance (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (right : ∀ f ∈ fs, IsRightFrame f) (shorter : actual ≤ expected) :
    Balanced (maximumRepairContext expected actual focus fs).height (maximumRepairContext expected actual focus fs).tree ∧
      (maximumRepairContext expected actual focus fs).height ≤ expected + fs.length := by
  induction fs generalizing expected actual focus with
  | nil => exact ⟨balanced, shorter⟩
  | cons f fs ih =>
    by_cases same : actual = expected
    · subst actual
      simp only [maximumRepairContext, ite_true]
      exact ⟨plug_balanced _ ancestors balanced, Nat.le_refl _⟩
    · have step := maximumRepairFrame_balance balanced ancestors.1 (right f (List.mem_cons_self ..)) shorter
      have result := ih step.1 ancestors.2 (fun g hg => right g (List.mem_cons_of_mem _ hg)) step.2.2
      simp only [maximumRepairContext, same, ite_false]
      exact ⟨result.1, by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using result.2⟩

/-- Context repair acts directly on the enclosing finger view, with exactly the
computed rotations and no hidden reconstruction of the unaffected ancestors. -/
theorem maximumRepairContext_rotations (fs : List Frame) (expected actual : Nat) (focus : Multiway)
    (right : ∀ f ∈ fs, IsRightFrame f) :
    Rotations (maximumEnclosingView focus fs) (maximumView (maximumRepairContext expected actual focus fs).tree).tree
      (maximumRepairContext expected actual focus fs).cost := by
  induction fs generalizing expected actual focus with
  | nil => exact .refl
  | cons f fs ih =>
    by_cases same : actual = expected
    · simp only [maximumRepairContext, same, ite_true]
      rw [← maximumEnclosingView_eq (f :: fs) focus right]
      exact .refl
    · have head := right f (List.mem_cons_self ..)
      have tail := ih (expected + 1) (maximumRepairFrame expected actual focus f).height
        (maximumRepairFrame expected actual focus f).tree (fun g hg => right g (List.mem_cons_of_mem _ hg))
      cases fs with
      | nil =>
        simpa only [maximumRepairContext, same, ite_false, maximumEnclosingView, maximumContextRemainder, Nat.add_zero] using
          maximumRepairFrame_rotations expected actual focus f head
      | cons g gs =>
        have first := maximumRepairFrame_open expected actual focus f head (maximumFrameRemainder g (maximumContextRemainder gs))
        have result := first.append tail
        simpa only [maximumRepairContext, same, ite_false, maximumEnclosingView, maximumContextRemainder] using result

end RotationBST.Arboral.Split.Multiway.Finger
