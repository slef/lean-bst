module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Parent
public import RotationBST.Models.Pointer.Location

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Retaining both pivots of an actual right rotation exposes precisely the
local hand shape for that rotation, even if the original finger was in a tendon. -/
theorem rotation_right_shape (h : Hand) (a b c : Tree) (anc : List Pointer.Frame)
    (reference : h.reference = Pointer.plug anc (.node (.node a b) c))
    (child : Pointer.offset anc + a.size ∈ (h.labels 0).inorder)
    (parent : Pointer.offset anc + (Tree.node a b).size ∈ (h.labels 0).inorder) :
    ∃ (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State) (l r sibling : Hand),
      h = Context.plug fs (.node cs d (.node [] e l r) sibling) ∧
      l.reference = a ∧ r.reference = b ∧ sibling.reference = c ∧
      anc = cs ++ Context.referencePath fs ∧ fs.length < h.count := by
  obtain ⟨fs, cs, e, l, r, shape, tree, key, depth⟩ := locate_reference h _ child
  have cursor : (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)) =
      ⟨.node a b, .left c :: anc⟩ :=
    Pointer.Config.ext_key (tree.trans reference) key rfl
  have focus := congrArg Pointer.Config.focus cursor
  have path := congrArg Pointer.Config.context cursor
  simp only [Tree.node.injEq] at focus
  obtain ⟨rfl, rfl⟩ := focus
  have empty := retained_parent_path fs cs e l r 0 (.left c) anc path
    (by simpa only [Nat.zero_add, Pointer.plug, rootRank, ← shape] using parent)
  subst cs
  simp only [List.nil_append] at path
  cases fs with
  | nil => simp [Context.referencePath] at path
  | cons frame fs =>
    cases frame with
    | left cs d sibling =>
      simp only [Context.referencePath, List.cons_append, List.cons.injEq, Pointer.Frame.left.injEq] at path
      obtain ⟨rfl, rfl⟩ := path
      exact ⟨fs, cs, d, e, l, r, sibling, shape, rfl, rfl, rfl, rfl, by simp only [List.length_cons] at depth; omega⟩
    | right cs d sibling => simp [Context.referencePath] at path

/-- Symmetric exposed shape for an actual left rotation. -/
theorem rotation_left_shape (h : Hand) (a b c : Tree) (anc : List Pointer.Frame)
    (reference : h.reference = Pointer.plug anc (.node a (.node b c)))
    (child : Pointer.offset anc + a.size + 1 + b.size ∈ (h.labels 0).inorder)
    (parent : Pointer.offset anc + a.size ∈ (h.labels 0).inorder) :
    ∃ (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State) (sibling l r : Hand),
      h = Context.plug fs (.node cs d sibling (.node [] e l r)) ∧
      sibling.reference = a ∧ l.reference = b ∧ r.reference = c ∧
      anc = cs ++ Context.referencePath fs ∧ fs.length < h.count := by
  obtain ⟨fs, cs, e, l, r, shape, tree, key, depth⟩ := locate_reference h _ child
  have cursor : (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)) =
      ⟨.node b c, .right a :: anc⟩ :=
    Pointer.Config.ext_key (tree.trans reference) key rfl
  have focus := congrArg Pointer.Config.focus cursor
  have path := congrArg Pointer.Config.context cursor
  simp only [Tree.node.injEq] at focus
  obtain ⟨rfl, rfl⟩ := focus
  have empty := retained_parent_path fs cs e l r 0 (.right a) anc path
    (by simpa only [Nat.zero_add, Pointer.plug, rootRank, ← shape] using parent)
  subst cs
  simp only [List.nil_append] at path
  cases fs with
  | nil => simp [Context.referencePath] at path
  | cons frame fs =>
    cases frame with
    | left cs d sibling => simp [Context.referencePath] at path
    | right cs d sibling =>
      simp only [Context.referencePath, List.cons_append, List.cons.injEq, Pointer.Frame.right.injEq] at path
      obtain ⟨rfl, rfl⟩ := path
      exact ⟨fs, cs, d, e, sibling, l, r, shape, rfl, rfl, rfl, rfl, by simp only [List.length_cons] at depth; omega⟩

end RotationBST.FingerHand.Hand
