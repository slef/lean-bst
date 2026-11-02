module

public import RotationBST.Arboral.Online.Split.Finger.Repair.Context.Proofs
public import RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Accounting

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem repairContext_same (fs : List Frame) (h : Nat) (focus : Multiway) :
    repairContext h h focus fs = ⟨plug fs focus, h + fs.length, 0⟩ := by
  cases fs <;> simp [repairContext, plug]

/-- Each continuing step pays for itself by deleting one enclosing node. Only
the final step needs the fixed allowance, independently of cascade length. -/
theorem repairContext_one_level (fs : List Frame) {h : Nat} {focus : Multiway}
    (balanced : Balanced h focus) (ancestors : Valid (h + 1) fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) :
    (repairContext (h + 1) h focus fs).cost + 2 * (repairContext (h + 1) h focus fs).tree.nodes ≤
      2 * (plug fs focus).nodes + 16 := by
  induction fs generalizing h focus with
  | nil => simp [repairContext, plug]
  | cons f fs ih =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := repairFrame_balance balanced ancestors.1 head (by omega)
    have charge := repairFrame_cost (h + 1) h focus f head
    have charged : (match fs with
        | [] => (repairFrame (h + 1) h focus f).cost
        | _ :: _ => repairFrameOpenCost (h + 1) h focus f) ≤ 10 := by
      cases fs <;> simp only <;> omega
    have inputNodes := plug_nodes fs (f.fill focus)
    have afterNodes := plug_nodes fs (repairFrame (h + 1) h focus f).tree
    by_cases continues : (repairFrame (h + 1) h focus f).height = h + 1
    · have merge := repairFrame_merge focus ancestors.1 head continues
      have childBalance : Balanced (h + 1) (repairFrame (h + 1) h focus f).tree := by
        have result := step.1
        rw [continues] at result
        exact result
      have result := ih childBalance ancestors.2 tail
      have cheap : (match fs with
          | [] => (repairFrame (h + 1) h focus f).cost
          | _ :: _ => repairFrameOpenCost (h + 1) h focus f) ≤ 2 := by
        cases fs <;> simp only <;> omega
      simp only [repairContext, show h ≠ h + 1 by omega, ite_false, continues, plug]
      cases fs <;> simp_all +arith <;> omega
    · have restored : (repairFrame (h + 1) h focus f).height = h + 1 + 1 := by omega
      have nodes := repairFrame_nodes (h + 1) h focus f head
      simp only [repairContext, show h ≠ h + 1 by omega, ite_false, restored, repairContext_same, plug]
      cases fs <;> simp_all +arith <;> omega

/-- An arbitrary initial height gap costs linearly in that gap. Any subsequent
one-level cascade is paid from the multiway node reserve. -/
theorem repairContext_credit (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected) :
    (repairContext expected actual focus fs).cost + 2 * (repairContext expected actual focus fs).tree.nodes ≤
      2 * (plug fs focus).nodes + 6 * (expected - actual) + 26 := by
  by_cases same : actual = expected
  · subst actual
    rw [repairContext_same]
    simp
  cases fs with
  | nil => simp [repairContext, plug]; omega
  | cons f fs =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := repairFrame_balance balanced ancestors.1 head shorter
    have charge := repairFrame_cost expected actual focus f head
    have nodes := repairFrame_nodes expected actual focus f head
    have charged : (match fs with
        | [] => (repairFrame expected actual focus f).cost
        | _ :: _ => repairFrameOpenCost expected actual focus f) ≤ 4 * (expected + 1 - actual) + 2 := by
      cases fs <;> simp only <;> omega
    have paid : (repairContext (expected + 1) (repairFrame expected actual focus f).height
        (repairFrame expected actual focus f).tree fs).cost +
        2 * (repairContext (expected + 1) (repairFrame expected actual focus f).height
          (repairFrame expected actual focus f).tree fs).tree.nodes ≤
        2 * (plug fs (repairFrame expected actual focus f).tree).nodes + 16 := by
      by_cases restored : (repairFrame expected actual focus f).height = expected + 1
      · rw [restored, repairContext_same]
        simp
      · have continues : (repairFrame expected actual focus f).height = expected := by omega
        have childBalance : Balanced expected (repairFrame expected actual focus f).tree := by
          have result := step.1
          rw [continues] at result
          exact result
        rw [continues]
        exact repairContext_one_level fs childBalance ancestors.2 tail
    have inputNodes := plug_nodes fs (f.fill focus)
    have afterNodes := plug_nodes fs (repairFrame expected actual focus f).tree
    simp only [repairContext, same, ite_false, plug]
    cases fs <;> simp_all +arith <;> omega

end RotationBST.Arboral.Split.Multiway.Finger
