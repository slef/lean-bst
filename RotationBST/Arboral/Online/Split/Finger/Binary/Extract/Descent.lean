module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Bounds
public import RotationBST.Arboral.Online.Split.Multiway.Extract.Ready

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Contracting a minimal root only changes grouping in the closed finger view. -/
theorem rootMerge_view {t u : Multiway} (merged : t.rootMerge = some u) :
    (binaryView t).tree = (binaryView u).tree ∧
      ∀ rest, Rotations (openView t rest) (openView u rest) 1 := by
  cases t with
  | nil => simp [rootMerge] at merged
  | three a b c => simp [rootMerge] at merged
  | four a b c d => simp [rootMerge] at merged
  | two first second =>
    cases first <;> cases second <;> simp [rootMerge] at merged
    subst u
    constructor
    · simp [binaryView, BinaryView.tree, comb_append, comb, binary]
    · intro rest
      exact repairOpen_rotations _ rest

/-- In the finger encoding, descending and exposing the minimum of a child
requires no additional rotations beyond the recursive child's repairs. -/
theorem descendFirst_open (recur : Multiway → Multiway × Nat) (cost : Multiway → Nat)
    {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil)
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → child ≠ .nil → ∀ rest,
      Rotations (openView child rest) (.node .nil (openView (recur child).1 rest)) (cost child))
    (rest : Tree) :
    Rotations (openView t rest) (.node .nil (openView (descendFirst recur t).1 rest))
      (if firstChild t = .nil then 0 else cost (firstChild t)) := by
  cases valid with
  | nil => contradiction
  | @two k l r ha hb =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb; exact .refl
    · have step := recursive l k (by simp only [nodes]; omega) ha empty (.node r.binary rest)
      simpa only [openView, binaryView, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step
  | @three k l m r ha hb hc =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb; cases hc; exact .refl
    · have step := recursive l k (by simp only [nodes]; omega) ha empty (.node m.binary (.node r.binary rest))
      simpa only [openView, binaryView, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step
  | @four k a b c d ha hb hc hd =>
    by_cases empty : a = .nil
    · subst a; cases ha; cases hb; cases hc; cases hd; exact .refl
    · have step := recursive a k (by simp only [nodes]; omega) ha empty (.node b.binary (.node c.binary (.node d.binary rest)))
      simpa only [openView, binaryView, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step

theorem descendFirst_view (recur : Multiway → Multiway × Nat) (cost : Multiway → Nat)
    {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil)
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → child ≠ .nil → ∀ rest,
      Rotations (openView child rest) (.node .nil (openView (recur child).1 rest)) (cost child)) :
    Rotations (binaryView t).tree (.node .nil (binaryView (descendFirst recur t).1).tree)
      (if firstChild t = .nil then 0 else cost (firstChild t)) := by
  cases valid with
  | nil => contradiction
  | @two k l r ha hb =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb; exact .refl
    · have step := recursive l k (by simp only [nodes]; omega) ha empty r.binary
      simpa only [openView, binaryView, BinaryView.tree, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step
  | @three k l m r ha hb hc =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb; cases hc; exact .refl
    · have step := recursive l k (by simp only [nodes]; omega) ha empty (.node m.binary r.binary)
      simpa only [openView, binaryView, BinaryView.tree, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step
  | @four k a b c d ha hb hc hd =>
    by_cases empty : a = .nil
    · subst a; cases ha; cases hb; cases hc; cases hd; exact .refl
    · have step := recursive a k (by simp only [nodes]; omega) ha empty (.node b.binary (.node c.binary d.binary))
      simpa only [openView, binaryView, BinaryView.tree, comb_append, comb, descendFirst, firstChild, empty, ite_false] using step

end RotationBST.Arboral.Split.Multiway.Finger
