module

public import RotationBST.Structures.FingerHand.Packed.Definitions.Abstract
public import RotationBST.Structures.Tendon.Potential

@[expose] public section
namespace RotationBST.FingerHand.Hand

private theorem path_size (cs : List Pointer.Frame) (t : Tree) :
    cs.length + t.size ≤ (Pointer.plug cs t).size := by
  induction cs generalizing t with
  | nil => simp [Pointer.plug]
  | cons frame cs ih =>
    cases frame with
    | left r =>
      have bound := ih (.node t r)
      simp only [List.length_cons, Pointer.plug, Tree.size] at bound ⊢
      omega
    | right l =>
      have bound := ih (.node l t)
      simp only [List.length_cons, Pointer.plug, Tree.size] at bound ⊢
      omega

/-- Every maintained hand has a size-linear potential. Tendon paths occupy
disjoint regions of the reference tree, so no node is counted twice. -/
theorem potential_le_reference {h : Hand} (valid : h.Valid) : h.potential ≤ 32 * h.reference.size := by
  induction h with
  | knuckle t => simp [potential]
  | node cs d l r il ir =>
    have tendon := d.potential_le_length valid.1
    have left := il valid.2.1
    have right := ir valid.2.2
    have size := path_size cs (.node l.reference r.reference)
    simp only [potential, reference, Tree.size] at size ⊢
    omega

theorem Represents.potential {fingers : Nat} {h : Hand} {s : Multifinger.State fingers} (rep : h.Represents s) :
    h.potential ≤ 32 * s.tree.size := by
  simpa only [rep.2.1] using potential_le_reference rep.1

end RotationBST.FingerHand.Hand
