module

public import RotationBST.Structures.SplitTree.Multiway.Edges.Defs
public import RotationBST.Structures.SplitTree.Multiway.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway

theorem repairFirst_rotations (t : Multiway) :
    Rotations t.binary (t.repairFirst).1.binary (t.repairFirst).2 := by
  cases t with
  | nil => exact .refl
  | two a b => exact prepareLeft_rotations _
  | three first second rest =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d => exact .step .left .refl
      | three c d e =>
        exact .step .left ((prepareLeft_rotations (.two (.two a b) (.three c d e))).inLeft.append
          (.step .right .refl))
      | four c d e f =>
        exact .step .left ((prepareLeft_rotations (.two (.two a b) (.four c d e f))).inLeft.append
          (.step .right .refl))
  | four first second third fourth =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d => exact .refl
      | three c d e => exact (prepareLeft_rotations (.two (.two a b) (.three c d e))).inLeft
      | four c d e f => exact (prepareLeft_rotations (.two (.two a b) (.four c d e f))).inLeft

theorem repairLast_rotations (t : Multiway) :
    Rotations t.binary (t.repairLast).1.binary (t.repairLast).2 := by
  cases t with
  | nil => exact .refl
  | two a b => exact prepareRight_rotations _
  | three first second last =>
    cases second with
    | nil => exact .refl
    | two a b =>
      cases last with
      | nil => exact .refl
      | two c d => exact .refl
      | three c d e => exact .refl
      | four c d e f => exact .refl
    | three a b c =>
      cases last with
      | nil => exact .refl
      | two d e => exact (prepareRight_rotations (.two (.three a b c) (.two d e))).inRight
      | three d e f => exact .refl
      | four d e f g => exact .refl
    | four a b c d =>
      cases last with
      | nil => exact .refl
      | two e f => exact (prepareRight_rotations (.two (.four a b c d) (.two e f))).inRight
      | three e f g => exact .refl
      | four e f g h => exact .refl
  | four first second third last =>
    cases third with
    | nil => exact .refl
    | two a b =>
      cases last with
      | nil => exact .refl
      | two c d => exact .step .right .refl
      | three c d e => exact .refl
      | four c d e f => exact .refl
    | three a b c =>
      cases last with
      | nil => exact .refl
      | two d e => exact (prepareRight_rotations (.two (.three a b c) (.two d e))).inRight
      | three d e f => exact .refl
      | four d e f g => exact .refl
    | four a b c d =>
      cases last with
      | nil => exact .refl
      | two e f => exact (prepareRight_rotations (.two (.four a b c d) (.two e f))).inRight
      | three e f g => exact .refl
      | four e f g h => exact .refl

end RotationBST.SplitTree.Multiway
