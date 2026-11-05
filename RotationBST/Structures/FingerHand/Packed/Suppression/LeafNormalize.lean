module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Leaves
public import RotationBST.Structures.FingerHand.Packed.Suppression.Normalize

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem demote_left_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (l r : Tree) (sibling : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d (.node [] e (.knuckle l) (.knuckle r)) sibling)).Valid)
    (parent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + (Tree.node l r).size ∈ marks) :
    let before := Context.plug fs (.node cs d (.node [] e (.knuckle l) (.knuckle r)) sibling)
    let after := Context.plug fs (.node cs d (.knuckle (.node l r)) sibling)
    let key := Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.size
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ 0 ∧ after.potential = before.potential := by
  dsimp only
  obtain ⟨normalized, ref, labels, tree, potential⟩ :=
    normalize_empty_under (.left cs d sibling :: fs) e (.knuckle l) (.knuckle r) valid
  obtain ⟨afterValid, reference, suppression, trace, phi⟩ :=
    demote_left fs cs d l r sibling marks normalized parent
  refine ⟨afterValid, reference.trans ref, ?_, ?_, phi.trans potential⟩
  · simpa only [Context.plug] using (labels 0) ▸ suppression
  · simpa only [Context.plug] using tree ▸ trace

theorem demote_right_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (sibling : Hand) (l r : Tree) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d sibling (.node [] e (.knuckle l) (.knuckle r)))).Valid)
    (parent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size ∈ marks) :
    let before := Context.plug fs (.node cs d sibling (.node [] e (.knuckle l) (.knuckle r)))
    let after := Context.plug fs (.node cs d sibling (.knuckle (.node l r)))
    let key := Pointer.offset (Context.referencePath fs) + Pointer.offset cs + sibling.reference.size + 1 + l.size
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ 0 ∧ after.potential = before.potential := by
  dsimp only
  obtain ⟨normalized, ref, labels, tree, potential⟩ :=
    normalize_empty_under (.right cs d sibling :: fs) e (.knuckle l) (.knuckle r) valid
  obtain ⟨afterValid, reference, suppression, trace, phi⟩ :=
    demote_right fs cs d sibling l r marks normalized parent
  refine ⟨afterValid, reference.trans ref, ?_, ?_, phi.trans potential⟩
  · simpa only [Context.plug] using (labels 0) ▸ suppression
  · simpa only [Context.plug] using tree ▸ trace

end RotationBST.FingerHand.Hand
