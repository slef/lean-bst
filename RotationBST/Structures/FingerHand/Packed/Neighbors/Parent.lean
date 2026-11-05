module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Root

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Expose the parent of a located pseudofinger. A nonempty incoming tendon
uses its bottom removal operation. With an empty tendon, the parent is already
an enclosing pseudofinger and no physical instruction is needed. -/
theorem expose_parent (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand)
    (valid : (Context.plug fs (.node cs d l r)).Valid)
    (parent : Pointer.Frame) (ancestors : List Pointer.Frame)
    (path : cs ++ Context.referencePath fs = parent :: ancestors) :
    ∃ (after : Hand) (k : Nat), Exposure (Context.plug fs (.node cs d l r)) after
        (Pointer.offset ancestors + rootRank (Pointer.plug [parent] (.node l.reference r.reference))) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 180 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential := by
  cases cs with
  | cons f cs =>
    simp only [List.cons_append] at path
    obtain ⟨rfl, rfl⟩ := List.cons.inj path
    obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
    obtain ⟨e, j, ex, trace, cost⟩ := exposeBottom cs d f l r inside
    have full := ex.under fs outside
    obtain ⟨k, run, bound⟩ := Context.lift_trace fs trace ex.nonempty.1 ex.nonempty.2 cost
    refine ⟨_, k, ⟨full.after_valid, full.reference, full.keys, le_of_eq full.count, ?_⟩, run, bound⟩
    apply Context.member
    cases f <;>
      simp only [graft, labels, Hand.reference, Pointer.plug, rootRank, Pointer.offset,
        Pointer.offset_append, Nat.add_zero, Nat.zero_add, LabelledTree.inorder, List.mem_append,
        List.mem_cons, Tree.size]
    all_goals right; left; omega
  | nil =>
    cases fs with
    | nil => simp [Context.referencePath] at path
    | cons f fs =>
      refine ⟨Context.plug (f :: fs) (.node [] d l r), 0,
        ⟨valid, rfl, fun _ => .refl _, by omega, ?_⟩, .refl, by omega⟩
      cases f with
      | left pcs pd sibling =>
        simp only [List.nil_append, Context.referencePath, List.cons_append] at path
        obtain ⟨rfl, rfl⟩ := List.cons.inj path
        apply Context.member fs
        simp only [labels, Hand.reference, Pointer.plug, rootRank, Pointer.offset_append,
          Nat.zero_add, LabelledTree.inorder, List.mem_append, List.mem_cons, Tree.size]
        right; left; omega
      | right pcs pd sibling =>
        simp only [List.nil_append, Context.referencePath, List.cons_append] at path
        obtain ⟨rfl, rfl⟩ := List.cons.inj path
        apply Context.member fs
        simp only [labels, Pointer.plug, rootRank, Pointer.offset_append,
          Nat.zero_add, LabelledTree.inorder, List.mem_append, List.mem_cons]
        right; left; omega

end RotationBST.FingerHand.Hand
