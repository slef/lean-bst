module

public import RotationBST.Structures.FingerHand.Packed.Pruning
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Location
public import RotationBST.Models.Pointer.Keys

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- An actual cursor at a marked key identifies a retained pseudofinger in a
canonical hand. -/
theorem canonical_cursor_member (h : Hand) (marks : Finset Nat)
    (canonical : h.labels 0 = compress marks h.reference 0)
    (c : Pointer.Config) (x : Nat) (tree : c.tree = h.reference)
    (key : c.key? = some x) (marked : x ∈ marks) : x ∈ (h.labels 0).inorder := by
  rw [canonical]
  apply marked_mem marks h.reference 0 x _ marked
  have bound := c.key_lt_size x key
  rw [tree] at bound
  rw [Representation.Bridge.inorder_label]
  simpa using bound

theorem labels_bounds (h : Hand) (lo x : Nat) (member : x ∈ (h.labels lo).inorder) :
    lo ≤ x ∧ x < lo + h.reference.size := by
  have inside := (labels_sublist h lo).subset member
  rw [Representation.Bridge.inorder_label] at inside
  obtain ⟨i, bound, eq⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at eq
  omega

/-- Retained nodes lie in the endpoint subtree's interval, excluding every
suppressed vertex on its incoming tendon. -/
theorem node_labels_bounds (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand) (lo x : Nat)
    (member : x ∈ ((Hand.node cs d l r).labels lo).inorder) :
    lo + Pointer.offset cs ≤ x ∧
      x < lo + Pointer.offset cs + (Tree.node l.reference r.reference).size := by
  simp only [labels, LabelledTree.inorder, List.mem_append, List.mem_cons] at member
  rcases member with left | root | right
  · have := labels_bounds l _ x left
    simp only [Tree.size]
    omega
  · simp only [Tree.size]
    omega
  · have := labels_bounds r _ x right
    simp only [Tree.size]
    omega

theorem left_member (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand) (lo x : Nat)
    (member : x ∈ ((Hand.node cs d l r).labels lo).inorder)
    (beforeRoot : x < lo + Pointer.offset cs + l.reference.size) :
    x ∈ (l.labels (lo + Pointer.offset cs)).inorder := by
  simp only [labels, LabelledTree.inorder, List.mem_append, List.mem_cons] at member
  rcases member with left | root | right
  · exact left
  · omega
  · have := labels_bounds r _ x right
    omega

theorem right_member (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand) (lo x : Nat)
    (member : x ∈ ((Hand.node cs d l r).labels lo).inorder)
    (afterRoot : lo + Pointer.offset cs + l.reference.size < x) :
    x ∈ (r.labels (lo + Pointer.offset cs + l.reference.size + 1)).inorder := by
  simp only [labels, LabelledTree.inorder, List.mem_append, List.mem_cons] at member
  rcases member with left | root | right
  · have := labels_bounds l _ x left
    omega
  · omega
  · exact right

theorem Context.node_member (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (l r : Hand) (lo : Nat) :
    lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size ∈
      ((Context.plug fs (.node cs d l r)).labels lo).inorder := by
  apply Context.member
  simp [labels, LabelledTree.inorder]

/-- A globally retained key lying inside a hand region is retained locally in
that region. Siblings and enclosing pseudofingers cannot witness its presence. -/
theorem Context.local_member (fs : List ContextFrame) (h : Hand) (lo x : Nat)
    (member : x ∈ ((Context.plug fs h).labels lo).inorder)
    (lower : lo + Pointer.offset (Context.referencePath fs) ≤ x)
    (upper : x < lo + Pointer.offset (Context.referencePath fs) + h.reference.size) :
    x ∈ (h.labels (lo + Pointer.offset (Context.referencePath fs))).inorder := by
  induction fs generalizing h with
  | nil => simpa only [Context.plug, Context.referencePath, Pointer.offset, Nat.add_zero] using member
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      have size := Pointer.offset_add_size_le_plug cs (.node h.reference r.reference)
      simp only [Tree.size] at size
      simp only [Context.referencePath, Pointer.offset_append, Pointer.offset] at lower upper ⊢
      have parent := ih (.node cs d h r) member (by omega) (by change x < _ + (Pointer.plug cs _).size; omega)
      have child := left_member cs d h r _ x parent (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child
    | right cs d l =>
      have size := Pointer.offset_add_size_le_plug cs (.node l.reference h.reference)
      simp only [Tree.size] at size
      simp only [Context.referencePath, Pointer.offset_append, Pointer.offset] at lower upper ⊢
      have parent := ih (.node cs d l h) member (by omega) (by change x < _ + (Pointer.plug cs _).size; omega)
      have child := right_member cs d l h _ x parent (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child

end RotationBST.FingerHand.Hand
