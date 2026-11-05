module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Parent
public import RotationBST.Structures.FingerHand.Packed.Geometry.Obsolete
public import RotationBST.Structures.FingerHand.Packed.Suppression.LeafNormalize

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Moving to a marked actual parent permits complete cleanup of the obsolete
source vertex. Canonicality selects the unary or leaf case; no local shape or
canonical empty-tendon representation is assumed. -/
theorem suppress_up (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (.node cs d l r)).Valid)
    (canonical : (Context.plug fs (.node cs d l r)).labels 0 =
      compress (insert (Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size) marks) (Context.plug fs (.node cs d l r)).reference 0)
    (absent : Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∉
      (compress marks (Context.plug fs (.node cs d l r)).reference 0).inorder)
    (f : Pointer.Frame) (anc : List Pointer.Frame)
    (path : cs ++ Context.referencePath fs = f :: anc)
    (parent : Pointer.offset anc + rootRank (Pointer.plug [f] (.node l.reference r.reference)) ∈ marks) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = (Context.plug fs (.node cs d l r)).reference ∧
      after.labels 0 = compress marks after.reference 0 ∧
      Suppress marks (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size)
        ((Context.plug fs (.node cs d l r)).labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 86 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  have parentTree : (Pointer.Config.mk (Pointer.plug [f] (.node l.reference r.reference)) anc).tree =
      (Context.plug fs (.node cs d l r)).reference := by
    rw [Context.plug_reference, reference, ← Pointer.plug_append, path]
    cases f <;> rfl
  have parentRange := Pointer.Config.key_lt_size
    ⟨Pointer.plug [f] (.node l.reference r.reference), anc⟩
    (Pointer.offset anc + rootRank (Pointer.plug [f] (.node l.reference r.reference)))
    (by cases f <;> rfl)
  rw [parentTree] at parentRange
  have parentMember : Pointer.offset anc + rootRank (Pointer.plug [f] (.node l.reference r.reference)) ∈
      ((Context.plug fs (.node cs d l r)).labels 0).inorder := by
    rw [canonical]
    apply marked_mem
    · rw [Representation.Bridge.inorder_label]
      simpa using parentRange
    · exact Finset.mem_insert_of_mem parent
  have empty := retained_parent_path fs cs d l r 0 f anc path (by simpa only [Nat.zero_add] using parentMember)
  subst cs
  have shape := obsolete_shape fs [] d l r marks 0 (by simpa only [Nat.zero_add] using canonical)
    (by simpa only [Nat.zero_add] using absent)
  have unmarked := obsolete_unmarked _ marks 0 _ (Context.node_member fs [] d l r 0)
    (by simpa only [Nat.zero_add] using absent)
  simp only [Nat.zero_add] at unmarked
  suffices result : ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = (Context.plug fs (.node [] d l r)).reference ∧
      Suppress marks (Pointer.offset (Context.referencePath fs) + Pointer.offset [] + l.reference.size)
        ((Context.plug fs (.node [] d l r)).labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨(Context.plug fs (.node [] d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 86 + 10 * fs.length + (Context.plug fs (.node [] d l r)).potential by
    obtain ⟨after, k, afterValid, ref, suppression, trace, cost⟩ := result
    exact ⟨after, k, afterValid, ref,
      suppression_canonical marks 0 _ ref suppression unmarked canonical, suppression, trace, cost⟩
  simp only [Pointer.offset, Nat.add_zero, List.nil_append] at path ⊢
  cases l with
  | knuckle a =>
    cases r with
    | node rs rd rl rr =>
      obtain ⟨afterValid, ref, suppression, k, trace, cost⟩ :=
        suppress_top_empty fs rs rd d (.right a) rl rr marks valid
      exact ⟨_, k, afterValid, ref, suppression, trace, cost⟩
    | knuckle b =>
      cases fs with
      | nil => simp [Context.referencePath] at path
      | cons frame fs =>
        cases frame with
        | left ps pd sibling =>
          simp only [Context.referencePath, List.cons_append, List.cons.injEq] at path
          obtain ⟨rfl, rfl⟩ := path
          have marked : Pointer.offset (Context.referencePath fs) + Pointer.offset ps + (Tree.node a b).size ∈ marks := by
            simpa only [Pointer.offset_append, Pointer.plug, rootRank, reference,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using parent
          obtain ⟨afterValid, ref, suppression, trace, phi⟩ :=
            demote_left_empty fs ps pd d a b sibling marks valid marked
          refine ⟨_, 0, afterValid, ref, ?_, trace, ?_⟩
          · simpa only [Context.plug, reference, Context.referencePath, Pointer.offset_append, Pointer.offset,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using suppression
          · rw [phi]
            simp only [Context.plug]
            omega
        | right ps pd sibling =>
          simp only [Context.referencePath, List.cons_append, List.cons.injEq] at path
          obtain ⟨rfl, rfl⟩ := path
          have marked : Pointer.offset (Context.referencePath fs) + Pointer.offset ps + sibling.reference.size ∈ marks := by
            simpa only [Pointer.offset_append, Pointer.plug, rootRank,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using parent
          obtain ⟨afterValid, ref, suppression, trace, phi⟩ :=
            demote_right_empty fs ps pd d sibling a b marks valid marked
          refine ⟨_, 0, afterValid, ref, ?_, trace, ?_⟩
          · simpa only [Context.plug, reference, Context.referencePath, Pointer.offset_append, Pointer.offset,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using suppression
          · rw [phi]
            simp only [Context.plug]
            omega
  | node ls ld ll lr =>
    rcases shape with ⟨g, impossible⟩ | ⟨g, rfl⟩
    · cases impossible
    · obtain ⟨afterValid, ref, suppression, k, trace, cost⟩ :=
        suppress_top_empty fs ls ld d (.left g) ll lr marks valid
      exact ⟨_, k, afterValid, ref, suppression, trace, cost⟩

end RotationBST.FingerHand.Hand
