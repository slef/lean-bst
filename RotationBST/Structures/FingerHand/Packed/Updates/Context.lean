module

public import RotationBST.Structures.FingerHand.Packed.Updates.Shapes

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem Expansion.nonempty {a b : Hand} (ex : Expansion a b) : a.tree ≠ .nil ∧ b.tree ≠ .nil := by
  have hb : b.tree ≠ .nil := by
    cases b with
    | knuckle t => have := ex.count; simp [Hand.count] at this
    | node cs d l r => exact Pointer.plug_ne_nil d.context (by simp)
  refine ⟨?_, hb⟩
  have size : a.tree.size = b.tree.size := (tree_size ex.before_valid).trans
    ((congrArg Tree.size ex.reference).symm.trans (tree_size ex.after_valid).symm)
  intro ha
  rw [ha] at size
  cases h : b.tree with
  | nil => exact hb h
  | node l r => simp only [h, Tree.size] at size; omega

theorem Expansion.left {a b r : Hand} (ex : Expansion a b) (cs : List Pointer.Frame)
    (d : Tendon.State) (hd : d.Represents cs) (hr : r.Valid) :
    Expansion (.node cs d a r) (.node cs d b r) := by
  refine ⟨⟨hd, ex.before_valid, hr⟩, ⟨hd, ex.after_valid, hr⟩, ?_, ?_, ?_⟩
  · simp only [Hand.reference, ex.reference]
  · simp only [Hand.count, ex.count]
    omega
  · intro lo
    have sub := (ex.keys (lo + Pointer.offset cs)).append (List.Sublist.refl
      ((lo + Pointer.offset cs + a.reference.size) ::
        (r.labels (lo + Pointer.offset cs + a.reference.size + 1)).inorder))
    simpa only [labels, LabelledTree.inorder, ex.reference] using sub

theorem Expansion.right {a b l : Hand} (ex : Expansion a b) (cs : List Pointer.Frame)
    (d : Tendon.State) (hd : d.Represents cs) (hl : l.Valid) :
    Expansion (.node cs d l a) (.node cs d l b) := by
  refine ⟨⟨hd, hl, ex.before_valid⟩, ⟨hd, hl, ex.after_valid⟩, ?_, ?_, ?_⟩
  · simp only [Hand.reference, ex.reference]
  · simp only [Hand.count, ex.count]
    omega
  · intro lo
    have sub := (List.Sublist.refl (l.labels (lo + Pointer.offset cs)).inorder).append
      (List.Sublist.cons_cons (lo + Pointer.offset cs + l.reference.size)
        (ex.keys (lo + Pointer.offset cs + l.reference.size + 1)))
    simpa only [labels, LabelledTree.inorder] using sub

theorem Expansion.under {a b : Hand} (ex : Expansion a b) (fs : List ContextFrame)
    (valid : Context.Valid fs) : Expansion (Context.plug fs a) (Context.plug fs b) := by
  induction fs generalizing a b with
  | nil => exact ex
  | cons f fs ih =>
    cases f with
    | left cs d r => exact ih (ex.left cs d valid.1 valid.2.1) valid.2.2
    | right cs d l => exact ih (ex.right cs d valid.1 valid.2.1) valid.2.2

namespace Context

theorem plug_valid_iff (fs : List ContextFrame) (h : Hand) :
    (plug fs h).Valid ↔ h.Valid ∧ Valid fs := by
  induction fs generalizing h with
  | nil => simp [plug, Valid]
  | cons f fs ih =>
    cases f <;> simp [plug, ih, Hand.Valid, Valid, and_assoc, and_left_comm]

theorem plug_valid {fs : List ContextFrame} (valid : Valid fs) {h : Hand} (hh : h.Valid) :
    (plug fs h).Valid := by
  induction fs generalizing h with
  | nil => exact hh
  | cons f fs ih =>
    cases f with
    | left cs d r => exact ih valid.2.2 ⟨valid.1, hh, valid.2.1⟩
    | right cs d l => exact ih valid.2.2 ⟨valid.1, valid.2.1, hh⟩

theorem plug_tree (fs : List ContextFrame) (h : Hand) :
    (plug fs h).tree = Pointer.plug (pointer fs) h.tree := by
  induction fs generalizing h with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [plug, pointer, ih, tree, Tendon.State.tree, Pointer.plug_append, Pointer.plug]

theorem plug_potential (fs : List ContextFrame) (h : Hand) :
    (plug fs h).potential = h.potential + potential fs := by
  induction fs generalizing h with
  | nil => simp [plug, potential]
  | cons f fs ih => cases f <;> simp only [plug, potential, ih, Hand.potential] <;> omega

theorem plug_count (fs : List ContextFrame) (h : Hand) :
    (plug fs h).count = h.count + count fs := by
  induction fs generalizing h with
  | nil => simp [plug, count]
  | cons f fs ih => cases f <;> simp only [plug, count, ih, Hand.count] <;> omega

theorem length_le_count (fs : List ContextFrame) : fs.length ≤ count fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp only [List.length_cons, count] <;> omega

theorem pointer_length (fs : List ContextFrame) : (pointer fs).length ≤ 5 * fs.length := by
  induction fs with
  | nil => simp [pointer]
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      have := d.context_length
      simp only [pointer, List.length_append, List.length_cons]
      omega
    | right cs d l =>
      have := d.context_length
      simp only [pointer, List.length_append, List.length_cons]
      omega

/-- Lift any local pointer/potential bound into a whole hand. Both navigation
directions are charged; enclosing tendons and siblings retain their potential. -/
theorem lift_trace (fs : List ContextFrame) {a b : Hand} {k C : Nat}
    (trace : Pointer.Trace ⟨a.tree, []⟩ ⟨b.tree, []⟩ k)
    (before : a.tree ≠ .nil) (after : b.tree ≠ .nil)
    (bound : k + b.potential ≤ C + a.potential) :
    ∃ m, Pointer.Trace ⟨(plug fs a).tree, []⟩ ⟨(plug fs b).tree, []⟩ m ∧
      m + (plug fs b).potential ≤ C + 10 * fs.length + (plug fs a).potential := by
  have run := trace.inContext before after (pointer fs)
  refine ⟨(pointer fs).length + k + (pointer fs).length, ?_, ?_⟩
  · simpa only [plug_tree] using run
  · have := pointer_length fs
    simp only [plug_potential]
    omega

/-- In a maintained `k`-finger hand, navigation adds only `20(k+1)` to any local
amortized bound. This does not assume that the updated hand already has its
final marked skeleton. -/
theorem lift_in_state {fingers : Nat} (fs : List ContextFrame) {a b : Hand}
    {s : Multifinger.State fingers} (rep : (plug fs a).Represents s) {k C : Nat}
    (trace : Pointer.Trace ⟨a.tree, []⟩ ⟨b.tree, []⟩ k)
    (before : a.tree ≠ .nil) (after : b.tree ≠ .nil)
    (bound : k + b.potential ≤ C + a.potential) :
    ∃ m, Pointer.Trace ⟨(plug fs a).tree, []⟩ ⟨(plug fs b).tree, []⟩ m ∧
      m + (plug fs b).potential ≤ C + 20 * (fingers + 1) + (plug fs a).potential := by
  obtain ⟨m, run, cost⟩ := lift_trace fs trace before after bound
  have len := length_le_count fs
  have count := rep.count
  rw [plug_count] at count
  exact ⟨m, run, by omega⟩

end Context
end RotationBST.FingerHand.Hand
