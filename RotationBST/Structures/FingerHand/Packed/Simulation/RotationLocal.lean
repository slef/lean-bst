module

public import RotationBST.Structures.FingerHand.Packed.Updates.RotationContext
public import RotationBST.Structures.FingerHand.Packed.Suppression.Normalize

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem rotate_right_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (a b c : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d (.node [] e a b) c)).Valid)
    (canonical : (Context.plug fs (.node cs d (.node [] e a b) c)).labels 0 =
      compress marks (Context.plug fs (.node cs d (.node [] e a b) c)).reference 0)
    (lower : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + a.reference.size ∈ marks)
    (upper : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + a.reference.size + 1 + b.reference.size ∈ marks) :
    let before := Context.plug fs (.node cs d (.node [] e a b) c)
    let after := Context.plug fs (.node cs d a (fork b c))
    after.Valid ∧ after.labels 0 = compress marks after.reference 0 ∧
      after.count = before.count ∧ after.potential = before.potential ∧
      ∃ k, Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ k ∧
        k + after.potential ≤ 10 + 10 * fs.length + before.potential := by
  dsimp only
  obtain ⟨normalValid, normalRef, normalLabels, normalTree, normalPhi⟩ :=
    normalize_empty_under (.left cs d c :: fs) e a b valid
  have normalCanonical : (Context.plug fs (.node cs d (fork a b) c)).labels 0 =
      compress marks (Context.plug fs (.node cs d (fork a b) c)).reference 0 := by
    change (Context.plug (.left cs d c :: fs) (fork a b)).labels 0 =
      compress marks (Context.plug (.left cs d c :: fs) (fork a b)).reference 0
    rw [normalLabels, normalRef]
    exact canonical
  have normalCount := congrArg (fun t : LabelledTree Nat => t.erase.size) (normalLabels 0)
  simp only [labels_size] at normalCount
  have rot := LocalRotation.right cs d a b c
  have marked := marked_reference_right cs d a b c marks
    (0 + Pointer.offset (Context.referencePath fs))
    (by simpa only [Nat.zero_add] using lower) (by simpa only [Nat.zero_add] using upper)
  have afterCanonical := rot.canonical_under fs marks 0 marked normalCanonical
  obtain ⟨afterValid, count, phi, k, trace, cost⟩ := rot.trace_under fs normalValid
  refine ⟨afterValid, afterCanonical, count.trans normalCount, phi.trans normalPhi, k, ?_, ?_⟩
  · simpa only [Context.plug] using normalTree ▸ trace
  · simpa only [Context.plug] using normalPhi ▸ cost

theorem rotate_left_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (a b c : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d a (.node [] e b c))).Valid)
    (canonical : (Context.plug fs (.node cs d a (.node [] e b c))).labels 0 =
      compress marks (Context.plug fs (.node cs d a (.node [] e b c))).reference 0)
    (lower : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + a.reference.size ∈ marks)
    (upper : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + a.reference.size + 1 + b.reference.size ∈ marks) :
    let before := Context.plug fs (.node cs d a (.node [] e b c))
    let after := Context.plug fs (.node cs d (fork a b) c)
    after.Valid ∧ after.labels 0 = compress marks after.reference 0 ∧
      after.count = before.count ∧ after.potential = before.potential ∧
      ∃ k, Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ k ∧
        k + after.potential ≤ 10 + 10 * fs.length + before.potential := by
  dsimp only
  obtain ⟨normalValid, normalRef, normalLabels, normalTree, normalPhi⟩ :=
    normalize_empty_under (.right cs d a :: fs) e b c valid
  have normalCanonical : (Context.plug fs (.node cs d a (fork b c))).labels 0 =
      compress marks (Context.plug fs (.node cs d a (fork b c))).reference 0 := by
    change (Context.plug (.right cs d a :: fs) (fork b c)).labels 0 =
      compress marks (Context.plug (.right cs d a :: fs) (fork b c)).reference 0
    rw [normalLabels, normalRef]
    exact canonical
  have normalCount := congrArg (fun t : LabelledTree Nat => t.erase.size) (normalLabels 0)
  simp only [labels_size] at normalCount
  have rot := LocalRotation.left cs d a b c
  have marked := (marked_reference_right cs d a b c marks
    (0 + Pointer.offset (Context.referencePath fs))
    (by simpa only [Nat.zero_add] using lower) (by simpa only [Nat.zero_add] using upper)).symm
  have afterCanonical := rot.canonical_under fs marks 0 marked normalCanonical
  obtain ⟨afterValid, count, phi, k, trace, cost⟩ := rot.trace_under fs normalValid
  refine ⟨afterValid, afterCanonical, count.trans normalCount, phi.trans normalPhi, k, ?_, ?_⟩
  · simpa only [Context.plug] using normalTree ▸ trace
  · simpa only [Context.plug] using normalPhi ▸ cost

end RotationBST.FingerHand.Hand
