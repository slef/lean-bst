module

public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem maximumRepairFrame_balance {expected actual : Nat} {focus : Multiway} {frame : Frame}
    (balanced : Balanced actual focus) (siblings : frame.Valid expected)
    (right : IsRightFrame frame) (shorter : actual ≤ expected) :
    Balanced (maximumRepairFrame expected actual focus frame).height (maximumRepairFrame expected actual focus frame).tree ∧
      expected ≤ (maximumRepairFrame expected actual focus frame).height ∧
      (maximumRepairFrame expected actual focus frame).height ≤ expected + 1 := by
  cases frame <;> simp only [IsRightFrame] at right
  case twoRight b => exact attachLeft_balance balanced siblings shorter
  case threeLast b c =>
    have result := attachLeft_balance balanced (Balanced.two siblings.1 siblings.2) (by omega)
    have height := attachLeft_taller_two (show actual < expected + 1 by omega) focus b c
    exact ⟨result.1, by change expected ≤ (attachLeft actual (expected + 1) focus (.two b c)).height; omega,
      by change (attachLeft actual (expected + 1) focus (.two b c)).height ≤ expected + 1; omega⟩
  case fourLast b c d =>
    have result := attachLeft_balance balanced (Balanced.three siblings.1 siblings.2.1 siblings.2.2) (by omega)
    have height := attachLeft_taller_three (show actual < expected + 1 by omega) focus b c d
    exact ⟨result.1, by change expected ≤ (attachLeft actual (expected + 1) focus (.three b c d)).height; omega,
      by change (attachLeft actual (expected + 1) focus (.three b c d)).height ≤ expected + 1; omega⟩

theorem maximumRepairFrame_cost (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (right : IsRightFrame frame) :
    (maximumRepairFrame expected actual focus frame).cost ≤ 4 * (expected + 1 - actual) + 1 ∧
      maximumRepairFrameOpenCost expected actual focus frame ≤ 4 * (expected + 1 - actual) + 2 := by
  have closed := attachLeft_cost actual (maximumFrameSibling expected frame).height focus (maximumFrameSibling expected frame).tree
  have opened := maximumJoinOpen_cost ((maximumFrameSibling expected frame).height - actual) (maximumFrameSibling expected frame).tree focus
  cases frame <;> simp only [IsRightFrame] at right
  all_goals
    simp only [maximumRepairFrame, maximumRepairFrameOpenCost, maximumFrameSibling, maximumFrameGroupingCost, maximumFrameClosedCost] at *
    omega

end RotationBST.Arboral.Split.Multiway.Finger
