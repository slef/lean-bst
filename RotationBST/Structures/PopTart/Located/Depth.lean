module

public import RotationBST.Structures.PopTart.Located.Fringe
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

/-- Search inside an opaque payload adds its local search depth to the outer
slot depth, at the exact rank determined by the occurrence. -/
theorem LocatedSlot.key_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth t.tree (offset + x) = depth + Tree.depth subtree x := by
  induction slot with
  | leaf s w => change Tree.depth s (0 + x) = 0 + _; simp only [Nat.zero_add]
  | @left l r subtree weight offset depth slot ih =>
    have fits := slot.fits
    have left : offset + x < l.tree.size := by omega
    change Tree.depth (.node l.tree r.tree) (offset + x) = depth + 1 + _
    rw [Tree.depth, ite_eq_left left, ih inside]
    omega
  | @right l r subtree weight offset depth slot ih =>
    have left : ¬ offset + l.tree.size + 1 + x < l.tree.size := by omega
    have root : ¬ offset + l.tree.size + 1 + x = l.tree.size := by omega
    have index : offset + l.tree.size + 1 + x - l.tree.size - 1 = offset + x := by omega
    change Tree.depth (.node l.tree r.tree) (offset + l.tree.size + 1 + x) = depth + 1 + _
    rw [Tree.depth, ite_eq_right left, ite_eq_right root, index, ih inside]
    omega

/-- If there is a separator immediately after a payload, it is an ancestor
of that slot. The bound also holds for an empty external payload. -/
theorem LocatedSlot.successor_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (existsKey : offset + subtree.size < t.tree.size) :
    Tree.depth t.tree (offset + subtree.size) < depth := by
  induction slot with
  | leaf s w => change 0 + s.size < s.size at existsKey; omega
  | @left l r subtree weight offset depth slot ih =>
    have fits := slot.fits
    change Tree.depth (.node l.tree r.tree) (offset + subtree.size) < depth + 1
    by_cases left : offset + subtree.size < l.tree.size
    · rw [Tree.depth, ite_eq_left left]
      have bound := ih left
      omega
    · have root : offset + subtree.size = l.tree.size := by omega
      rw [root]
      simp only [Tree.depth, Nat.lt_irrefl, ite_false, ite_true]
      omega
  | @right l r subtree weight offset depth slot ih =>
    change offset + l.tree.size + 1 + subtree.size < l.tree.size + 1 + r.tree.size at existsKey
    have child : offset + subtree.size < r.tree.size := by omega
    have bound := ih child
    have left : ¬ offset + l.tree.size + 1 + subtree.size < l.tree.size := by omega
    have root : ¬ offset + l.tree.size + 1 + subtree.size = l.tree.size := by omega
    have index : offset + l.tree.size + 1 + subtree.size - l.tree.size - 1 = offset + subtree.size := by omega
    change Tree.depth (.node l.tree r.tree) (offset + l.tree.size + 1 + subtree.size) < depth + 1
    rw [Tree.depth, ite_eq_right left, ite_eq_right root, index]
    omega

/-- The separator immediately before a noninitial slot is likewise an
ancestor. This is the orientation used by the reflected upper stack. -/
theorem LocatedSlot.predecessor_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (existsKey : 0 < offset) :
    Tree.depth t.tree (offset - 1) < depth := by
  induction slot with
  | leaf => omega
  | @left l r subtree weight offset depth slot ih =>
    have fits := slot.fits
    have left : offset - 1 < l.tree.size := by omega
    have bound := ih existsKey
    change Tree.depth (.node l.tree r.tree) (offset - 1) < depth + 1
    rw [Tree.depth, ite_eq_left left]
    omega
  | @right l r subtree weight offset depth slot ih =>
    change Tree.depth (.node l.tree r.tree) (offset + l.tree.size + 1 - 1) < depth + 1
    by_cases zero : offset = 0
    · subst offset
      simp only [Nat.zero_add, Nat.add_sub_cancel, Tree.depth, Nat.lt_irrefl, ite_false, ite_true]
      omega
    · have bound := ih (by omega)
      have left : ¬ offset + l.tree.size + 1 - 1 < l.tree.size := by omega
      have root : ¬ offset + l.tree.size + 1 - 1 = l.tree.size := by omega
      have index : offset + l.tree.size + 1 - 1 - l.tree.size - 1 = offset - 1 := by omega
      rw [Tree.depth, ite_eq_right left, ite_eq_right root, index]
      omega

/-- The located slot has a physical cursor with exactly that offset and depth. -/
theorem LocatedSlot.context {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.offset cs = offset ∧ Pointer.plug cs subtree = t.tree := by
  induction slot with
  | leaf => exact ⟨[], rfl, rfl, rfl⟩
  | @left l r subtree weight offset depth slot ih =>
    obtain ⟨cs, length, position, tree⟩ := ih
    refine ⟨cs ++ [.left r.tree], by simp [length], ?_, ?_⟩
    · simp [Pointer.offset_append, Pointer.offset, position]
    · rw [Pointer.plug_append, tree]; rfl
  | @right l r subtree weight offset depth slot ih =>
    obtain ⟨cs, length, position, tree⟩ := ih
    refine ⟨cs ++ [.right l.tree], by simp [length], ?_, ?_⟩
    · simp [Pointer.offset_append, Pointer.offset, position, Nat.add_assoc]
    · rw [Pointer.plug_append, tree]; rfl

end RotationBST.PopTart.WeightedTree
