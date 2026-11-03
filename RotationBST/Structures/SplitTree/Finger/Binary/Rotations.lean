module

public import RotationBST.Structures.SplitTree.Finger.Binary.Abstract
public import RotationBST.Models.Rotation.Rotations

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

theorem comb_append (xs ys : List Tree) (tail : Tree) :
    comb (xs ++ ys) tail = comb xs (comb ys tail) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, comb, ih]

theorem comb_rotations (xs : List Tree) {s t : Tree} {cost : Nat}
    (steps : Rotations s t cost) : Rotations (comb xs s) (comb xs t) cost := by
  induction xs with
  | nil => exact steps
  | cons a xs ih => exact ih.inRight

/-- Move one enclosing separator to the far end of the represented finger. -/
theorem comb_rotate (xs : List Tree) (tail right : Tree) :
    Rotations (.node (comb xs tail) right) (comb xs (.node tail right)) xs.length := by
  induction xs with
  | nil => exact .refl
  | cons a xs ih => exact .step .right ih.inRight

/-- Construction changes only the spine and is realized by the stated rotations. -/
theorem binaryView_rotations (t : Multiway) :
    Rotations t.binary (binaryView t).tree (viewCost t) := by
  induction t with
  | nil => exact .refl
  | two a b ia ib =>
    have steps := ia.inLeft.append (comb_rotate (binaryView a).spine (binaryView a).tail b.binary)
    simpa only [binaryView, BinaryView.tree, binary, comb_append, comb, viewCost] using steps
  | three a b c ia ib ic =>
    have steps := ia.inLeft.append (comb_rotate (binaryView a).spine (binaryView a).tail (.node b.binary c.binary))
    simpa only [binaryView, BinaryView.tree, binary, comb_append, comb, viewCost] using steps
  | four a b c d ia ib ic id =>
    have first := (comb_rotate (binaryView a).spine (binaryView a).tail b.binary).inLeft
      (r := Tree.node c.binary d.binary)
    have second := comb_rotate (binaryView a).spine (.node (binaryView a).tail b.binary) (.node c.binary d.binary)
    have last := comb_rotations (binaryView a).spine
      (show Rotations (.node (.node (binaryView a).tail b.binary) (.node c.binary d.binary))
        (.node (binaryView a).tail (.node b.binary (.node c.binary d.binary))) 1 from .step .right .refl)
    have steps := ((ia.inLeft.inLeft.append first).append second).append last
    have cost : ((viewCost a + (binaryView a).spine.length) + (binaryView a).spine.length) + 1 =
        viewCost a + 2 * (binaryView a).spine.length + 1 := by omega
    rw [cost] at steps
    simpa only [binaryView, BinaryView.tree, binary, comb_append, comb, viewCost] using steps

end RotationBST.SplitTree.Multiway.Finger
