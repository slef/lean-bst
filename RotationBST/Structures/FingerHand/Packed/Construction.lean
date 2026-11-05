module

public import RotationBST.Structures.FingerHand.Packed.Definitions.Abstract
public import RotationBST.Structures.FingerHand.State
public import RotationBST.Structures.Tendon.Representation

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem labels_size (h : Hand) (lo : Nat) : (h.labels lo).erase.size = h.count := by
  induction h generalizing lo with
  | knuckle => rfl
  | node cs d l r ihl ihr => simp [labels, count, LabelledTree.erase, Tree.size, ihl, ihr]

theorem extend_reference (h : Hand) (f : Pointer.Frame) :
    (h.extend f).reference = Pointer.plug [f] h.reference := by
  cases h <;> simp [extend, reference, Pointer.plug_append]

theorem extend_valid {h : Hand} (valid : h.Valid) (f : Pointer.Frame) : (h.extend f).Valid := by
  cases h with
  | knuckle => trivial
  | node cs d l r => exact ⟨Tendon.State.ofPath_represents _, valid.2⟩

theorem extend_count (h : Hand) (f : Pointer.Frame) : (h.extend f).count = h.count := by
  cases h <;> rfl

theorem extend_labels_left (h : Hand) (g : Tree) (lo : Nat) :
    (h.extend (.left g)).labels lo = h.labels lo := by
  cases h <;> simp [extend, labels, Pointer.offset_append, Pointer.offset]

theorem extend_labels_right (h : Hand) (g : Tree) (lo : Nat) :
    (h.extend (.right g)).labels lo = h.labels (lo + g.size + 1) := by
  cases h <;> simp [extend, labels, Pointer.offset_append, Pointer.offset,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem build_reference (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (build marks t lo).reference = t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    have hl := ihl lo
    have hr := ihr (lo + l.size + 1)
    by_cases hm : lo + l.size ∈ marks
    · simp [build, hm, reference, Pointer.plug, hl, hr]
    · cases hL : build marks l lo <;> cases hR : build marks r (lo + l.size + 1) <;>
        simp only [hL, hR] at hl hr <;>
        simp [build, hm, hL, hR, extend_reference, reference, Pointer.plug] at hl hr ⊢ <;>
        simp_all

theorem build_valid (marks : Finset Nat) (t : Tree) (lo : Nat) : (build marks t lo).Valid := by
  induction t generalizing lo with
  | nil => trivial
  | node l r ihl ihr =>
    have hl := ihl lo
    have hr := ihr (lo + l.size + 1)
    by_cases hm : lo + l.size ∈ marks
    · simp only [build, hm, ↓reduceIte]
      exact ⟨Tendon.State.ofPath_represents [], hl, hr⟩
    · cases hL : build marks l lo <;> cases hR : build marks r (lo + l.size + 1) <;>
        simp only [hL, hR] at hl hr
      · simp [build, hm, hL, hR, Valid]
      · simpa only [build, hm, ↓reduceIte, hL, hR] using extend_valid hr (.right l)
      · simpa only [build, hm, ↓reduceIte, hL, hR] using extend_valid hl (.left r)
      · simpa only [build, hm, ↓reduceIte, hL, hR, Valid] using
          And.intro (Tendon.State.ofPath_represents []) (And.intro hl hr)

theorem build_labels (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (build marks t lo).labels lo = compress marks t lo := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    have hl := ihl lo
    have hr := ihr (lo + l.size + 1)
    have rl := build_reference marks l lo
    by_cases hm : lo + l.size ∈ marks
    · simp [build, compress, hm, labels, Pointer.offset, rl, hl, hr]
    · cases hL : build marks l lo <;> cases hR : build marks r (lo + l.size + 1) <;>
        simp only [hL, hR] at hl hr rl
      all_goals
        simp only [build, compress, hm, ↓reduceIte, hL, hR, ← hl, ← hr]
      · rfl
      · rw [extend_labels_right]
        rfl
      · rw [extend_labels_left]
        rfl
      · simp only [labels, Pointer.offset, Nat.add_zero, rl]

theorem build_count (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (build marks t lo).count ≤ 2 * marks.card := by
  rw [← labels_size _ lo, build_labels]
  exact compress_size marks t lo

theorem build_marked (marks : Finset Nat) (t : Tree) (lo x : Nat)
    (member : x ∈ (t.labelFrom lo).inorder) (marked : x ∈ marks) :
    x ∈ ((build marks t lo).labels lo).inorder := by
  rw [build_labels]
  exact marked_mem marks t lo x member marked

end RotationBST.FingerHand.Hand
