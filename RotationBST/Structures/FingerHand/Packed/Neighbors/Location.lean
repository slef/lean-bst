module

public import RotationBST.Structures.FingerHand.Packed.Updates.Context

@[expose] public section
namespace RotationBST.FingerHand.Hand

namespace Context

theorem plug_reference (fs : List ContextFrame) (h : Hand) :
    (plug fs h).reference = Pointer.plug (referencePath fs) h.reference := by
  induction fs generalizing h with
  | nil => rfl
  | cons f fs ih => cases f <;>
      simp only [plug, referencePath, ih, Hand.reference, Pointer.plug_append, Pointer.plug]

theorem reference_offset (fs : List ContextFrame) (valid : Valid fs) :
    Pointer.offset (pointer fs) = Pointer.offset (referencePath fs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      simp only [pointer, referencePath, Pointer.offset_append, Pointer.offset,
        Tendon.State.represents_offset valid.1, ih valid.2.2]
    | right cs d l =>
      simp only [pointer, referencePath, Pointer.offset_append, Pointer.offset,
        Tendon.State.represents_offset valid.1, tree_size valid.2.1, ih valid.2.2]

theorem member (fs : List ContextFrame) (h : Hand) (lo x : Nat)
    (inside : x ∈ (h.labels (lo + Pointer.offset (referencePath fs))).inorder) :
    x ∈ ((plug fs h).labels lo).inorder := by
  induction fs generalizing h with
  | nil => simpa only [plug, referencePath, Pointer.offset, Nat.add_zero] using inside
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      apply ih
      apply List.mem_append_left
      simpa only [referencePath, Pointer.offset_append, Pointer.offset, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using inside
    | right cs d l =>
      apply ih
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      simpa only [referencePath, Pointer.offset_append, Pointer.offset, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using inside

theorem plug_append (fs gs : List ContextFrame) (h : Hand) :
    plug (fs ++ gs) h = plug gs (plug fs h) := by
  induction fs generalizing h with
  | nil => rfl
  | cons f fs ih => cases f <;> simp only [List.cons_append, plug, ih]

theorem referencePath_append (fs gs : List ContextFrame) :
    referencePath (fs ++ gs) = referencePath fs ++ referencePath gs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp only [List.cons_append, referencePath, ih, List.append_assoc]

end Context

/-- Locate a pseudofinger as an actual editable hand region. Its global rank
uses the reference zipper; the surrounding number of hand frames is bounded
independently of the lengths of reference tendons. -/
theorem locate (h : Hand) (lo x : Nat) (member : x ∈ (h.labels lo).inorder) :
    ∃ (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand),
      h = Context.plug fs (.node cs d l r) ∧
      x = lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∧
      fs.length < h.count := by
  induction h generalizing lo with
  | knuckle t => simp [labels, LabelledTree.inorder] at member
  | node cs d l r il ir =>
    simp only [labels, LabelledTree.inorder, List.mem_append, List.mem_cons] at member
    rcases member with left | root | right
    · obtain ⟨fs, path, e, a, b, eq, key, depth⟩ := il _ left
      refine ⟨fs ++ [.left cs d r], path, e, a, b, ?_, ?_, ?_⟩
      · simp only [Context.plug_append, Context.plug, ← eq]
      · simp only [Context.referencePath_append, Context.referencePath, Pointer.offset_append,
          Pointer.offset, Nat.add_zero]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil, count]
        omega
    · exact ⟨[], cs, d, l, r, rfl, by simpa only [Context.referencePath, Pointer.offset, Nat.add_zero] using root,
        by simp only [List.length_nil, count]; omega⟩
    · obtain ⟨fs, path, e, a, b, eq, key, depth⟩ := ir _ right
      refine ⟨fs ++ [.right cs d l], path, e, a, b, ?_, ?_, ?_⟩
      · simp only [Context.plug_append, Context.plug, ← eq]
      · simp only [Context.referencePath_append, Context.referencePath, Pointer.offset_append,
          Pointer.offset, Nat.add_zero]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil, count]
        omega

/-- The located region supplies the full reference-machine cursor, not just a
rank equation. This is the cursor whose neighboring nodes are exposed below. -/
theorem locate_reference (h : Hand) (x : Nat) (member : x ∈ (h.labels 0).inorder) :
    ∃ (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand),
      h = Context.plug fs (.node cs d l r) ∧
      (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)).tree = h.reference ∧
      (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)).key? = some x ∧
      fs.length < h.count := by
  obtain ⟨fs, cs, d, l, r, eq, key, depth⟩ := locate h 0 x member
  refine ⟨fs, cs, d, l, r, eq, ?_, ?_, depth⟩
  · rw [eq, Context.plug_reference]
    simp only [Pointer.Config.tree, Pointer.plug_append, reference]
  · simp only [Pointer.Config.key?, Pointer.offset_append]
    congr 1
    omega

end RotationBST.FingerHand.Hand
