module

public import RotationBST.Structures.SplitTree.Finger.Repair.Context.Accounting

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- Repair cannot lower the global height by more than the initial local gap. -/
theorem repairContext_height_lower (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected) :
    actual + fs.length ≤ (repairContext expected actual focus fs).height := by
  induction fs generalizing expected actual focus with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    by_cases same : actual = expected
    · simp only [repairContext, same, ite_true]
      omega
    · have step := repairFrame_balance balanced ancestors.1 (left f (List.mem_cons_self ..)) shorter
      have child := ih step.1 ancestors.2 (fun g hg => left g (List.mem_cons_of_mem _ hg)) step.2.2
      simp only [repairContext, same, ite_false, List.length_cons]
      omega

/-- A one-level deficit reaching the root consumes exactly one node per
ancestor. Early restoration would preserve the original total height. -/
theorem repairContext_one_level_loss (fs : List Frame) {h : Nat} {focus : Multiway}
    (balanced : Balanced h focus) (ancestors : Valid (h + 1) fs)
    (left : ∀ f ∈ fs, IsLeftFrame f)
    (lost : (repairContext (h + 1) h focus fs).height < h + 1 + fs.length) :
    (repairContext (h + 1) h focus fs).tree.nodes + fs.length = (plug fs focus).nodes := by
  induction fs generalizing h focus with
  | nil => simp [repairContext, plug]
  | cons f fs ih =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := repairFrame_balance balanced ancestors.1 head (by omega)
    have continues : (repairFrame (h + 1) h focus f).height = h + 1 := by
      by_contra different
      have restored : (repairFrame (h + 1) h focus f).height = h + 1 + 1 := by omega
      simp only [repairContext, show h ≠ h + 1 by omega, ite_false, restored, repairContext_same,
        List.length_cons] at lost
      omega
    have merge := (repairFrame_merge focus ancestors.1 head continues).1
    have childBalance : Balanced (h + 1) (repairFrame (h + 1) h focus f).tree := by
      have result := step.1
      rw [continues] at result
      exact result
    have childLoss : (repairContext (h + 1 + 1) (h + 1) (repairFrame (h + 1) h focus f).tree fs).height <
        h + 1 + 1 + fs.length := by
      simp only [repairContext, show h ≠ h + 1 by omega, ite_false, continues, List.length_cons] at lost
      omega
    have result := ih childBalance ancestors.2 tail childLoss
    have outer := plug_nodes_drop fs merge
    simp only [repairContext, show h ≠ h + 1 by omega, ite_false, continues, plug, List.length_cons]
    omega

/-- With an arbitrary initial gap, all but the first frame of a height-lowering
cascade still remove one node each. Local joining accounts for the exception. -/
theorem repairContext_height_loss (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected)
    (lost : (repairContext expected actual focus fs).height < expected + fs.length) :
    (repairContext expected actual focus fs).tree.nodes + fs.length ≤
      (plug fs focus).nodes + (expected - actual) + 3 := by
  have different : actual ≠ expected := by
    intro same
    subst actual
    rw [repairContext_same] at lost
    simp only at lost
    omega
  cases fs with
  | nil => simp [repairContext, plug]; omega
  | cons f fs =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := repairFrame_balance balanced ancestors.1 head shorter
    have continues : (repairFrame expected actual focus f).height = expected := by
      by_contra differentHeight
      have restored : (repairFrame expected actual focus f).height = expected + 1 := by omega
      simp only [repairContext, different, ite_false, restored, repairContext_same, List.length_cons] at lost
      omega
    have childBalance : Balanced expected (repairFrame expected actual focus f).tree := by
      have result := step.1
      rw [continues] at result
      exact result
    have childLoss : (repairContext (expected + 1) expected (repairFrame expected actual focus f).tree fs).height <
        expected + 1 + fs.length := by
      simp only [repairContext, different, ite_false, continues, List.length_cons] at lost
      omega
    have result := repairContext_one_level_loss fs childBalance ancestors.2 tail childLoss
    have allocation := repairFrame_nodes expected actual focus f head
    have before := plug_nodes fs (f.fill focus)
    have after := plug_nodes fs (repairFrame expected actual focus f).tree
    simp only [repairContext, different, ite_false, continues, plug, List.length_cons]
    omega

end RotationBST.SplitTree.Multiway.Finger
