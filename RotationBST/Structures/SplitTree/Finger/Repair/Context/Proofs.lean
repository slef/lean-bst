module

public import RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs
public import RotationBST.Structures.SplitTree.Finger.Repair.Frame.Balance
public import RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem repairContext_balance (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected) :
    Balanced (repairContext expected actual focus fs).height (repairContext expected actual focus fs).tree ∧
      (repairContext expected actual focus fs).height ≤ expected + fs.length := by
  induction fs generalizing expected actual focus with
  | nil => exact ⟨balanced, shorter⟩
  | cons f fs ih =>
    by_cases same : actual = expected
    · subst actual
      simp only [repairContext, ite_true]
      exact ⟨plug_balanced _ ancestors balanced, Nat.le_refl _⟩
    · have step := repairFrame_balance balanced ancestors.1 (left f (List.mem_cons_self ..)) shorter
      have result := ih step.1 ancestors.2 (fun g hg => left g (List.mem_cons_of_mem _ hg)) step.2.2
      simp only [repairContext, same, ite_false]
      exact ⟨result.1, by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using result.2⟩

/-- Context repair acts directly on the enclosing finger view, with exactly the
computed rotations and no hidden reconstruction of the unaffected ancestors. -/
theorem repairContext_rotations (fs : List Frame) (expected actual : Nat) (focus : Multiway)
    (left : ∀ f ∈ fs, IsLeftFrame f) :
    Rotations (enclosingView focus fs) (binaryView (repairContext expected actual focus fs).tree).tree
      (repairContext expected actual focus fs).cost := by
  induction fs generalizing expected actual focus with
  | nil => exact .refl
  | cons f fs ih =>
    by_cases same : actual = expected
    · simp only [repairContext, same, ite_true]
      rw [← enclosingView_eq (f :: fs) focus left]
      exact .refl
    · have head := left f (List.mem_cons_self ..)
      have tail := ih (expected + 1) (repairFrame expected actual focus f).height
        (repairFrame expected actual focus f).tree (fun g hg => left g (List.mem_cons_of_mem _ hg))
      cases fs with
      | nil =>
        simpa only [repairContext, same, ite_false, enclosingView, contextRemainder, Nat.add_zero] using
          repairFrame_rotations expected actual focus f head
      | cons g gs =>
        have first := repairFrame_open expected actual focus f head (frameRemainder g (contextRemainder gs))
        have result := first.append tail
        simpa only [repairContext, same, ite_false, enclosingView, contextRemainder] using result

end RotationBST.Arboral.Split.Multiway.Finger
