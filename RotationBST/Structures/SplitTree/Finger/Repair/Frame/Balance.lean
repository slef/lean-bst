module

public import RotationBST.Structures.SplitTree.Finger.Repair.Frame.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem repairFrame_balance {expected actual : Nat} {focus : Multiway} {frame : Frame}
    (balanced : Balanced actual focus) (siblings : frame.Valid expected)
    (left : IsLeftFrame frame) (shorter : actual ≤ expected) :
    Balanced (repairFrame expected actual focus frame).height (repairFrame expected actual focus frame).tree ∧
      expected ≤ (repairFrame expected actual focus frame).height ∧
      (repairFrame expected actual focus frame).height ≤ expected + 1 := by
  cases frame <;> simp only [IsLeftFrame] at left
  case twoLeft b => exact attachRight_balance balanced siblings shorter
  case threeFirst b c =>
    have result := attachRight_balance balanced (Balanced.two siblings.1 siblings.2) (by omega)
    have height := attachRight_taller_two (show actual < expected + 1 by omega) focus b c
    exact ⟨result.1, by change expected ≤ (attachRight actual (expected + 1) focus (.two b c)).height; omega,
      by change (attachRight actual (expected + 1) focus (.two b c)).height ≤ expected + 1; omega⟩
  case fourFirst b c d =>
    have result := attachRight_balance balanced (Balanced.three siblings.1 siblings.2.1 siblings.2.2) (by omega)
    have height := attachRight_taller_three (show actual < expected + 1 by omega) focus b c d
    exact ⟨result.1, by change expected ≤ (attachRight actual (expected + 1) focus (.three b c d)).height; omega,
      by change (attachRight actual (expected + 1) focus (.three b c d)).height ≤ expected + 1; omega⟩

theorem repairFrame_cost (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (left : IsLeftFrame frame) :
    (repairFrame expected actual focus frame).cost ≤ 4 * (expected + 1 - actual) ∧
      repairFrameOpenCost expected actual focus frame ≤ 4 * (expected + 1 - actual) + 2 := by
  have closed := attachRight_cost actual (frameSibling expected frame).height focus (frameSibling expected frame).tree
  have opened := joinOpen_cost ((frameSibling expected frame).height - actual) focus (frameSibling expected frame).tree
  cases frame <;> simp only [IsLeftFrame] at left
  all_goals
    simp only [repairFrame, repairFrameOpenCost, frameSibling, frameGroupingCost] at *
    omega

end RotationBST.Arboral.Split.Multiway.Finger
