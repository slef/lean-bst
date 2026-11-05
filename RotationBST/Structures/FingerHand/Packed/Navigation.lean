module

public import RotationBST.Structures.FingerHand.Packed.Construction
public import RotationBST.Models.Pointer.Basic

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Replacing a reference tendon by its representation preserves the size of
the whole subtree, including all recursively represented children. -/
theorem tree_size {h : Hand} (valid : h.Valid) : h.tree.size = h.reference.size := by
  induction h with
  | knuckle => rfl
  | node cs d l r ihl ihr =>
    obtain ⟨k, _, trace⟩ := Tendon.State.compress_trace valid.1 (.node l.tree r.tree)
    obtain ⟨j, _, rotations⟩ := trace.rotations
    have eq := rotations.size_eq
    have children : (Tree.node l.tree r.tree).size = (Tree.node l.reference r.reference).size := by
      simp only [Tree.size, ihl valid.2.1, ihr valid.2.2]
    exact eq.symm.trans (Pointer.plug_size_congr cs children)

/-- Each pseudofinger has an actual location in the represented BST, preserving
its global inorder rank. The location's depth counts only hand vertices and the
bounded tendon boundary paths, never the sizes of the knuckle subtrees. -/
theorem location {h : Hand} (valid : h.Valid) (lo x : Nat) (member : x ∈ (h.labels lo).inorder) :
    ∃ (a b : Tree) (cs : List Pointer.Frame), Pointer.plug cs (.node a b) = h.tree ∧
      x = lo + Pointer.offset cs + a.size ∧ cs.length < 5 * h.count := by
  induction h generalizing lo with
  | knuckle => simp [labels, LabelledTree.inorder] at member
  | node path d l r ihl ihr =>
    have offset := Tendon.State.represents_offset valid.1
    have len := d.context_length
    have leftSize := tree_size valid.2.1
    simp only [labels, LabelledTree.inorder, List.mem_append, List.mem_cons] at member
    rcases member with left | root | right
    · obtain ⟨a, b, cs, eq, key, depth⟩ := ihl valid.2.1 _ left
      refine ⟨a, b, cs ++ (.left r.tree :: d.context), ?_, ?_, ?_⟩
      · simp only [Pointer.plug_append, eq, Pointer.plug, tree, Tendon.State.tree]
      · simp only [Pointer.offset_append, Pointer.offset, offset]
        omega
      · simp only [List.length_append, List.length_cons, count]
        omega
    · refine ⟨l.tree, r.tree, d.context, rfl, ?_, ?_⟩
      · simpa only [offset, leftSize] using root
      · simp only [count]
        omega
    · obtain ⟨a, b, cs, eq, key, depth⟩ := ihr valid.2.2 _ right
      refine ⟨a, b, cs ++ (.right l.tree :: d.context), ?_, ?_, ?_⟩
      · simp only [Pointer.plug_append, eq, Pointer.plug, tree, Tendon.State.tree]
      · simp only [Pointer.offset_append, Pointer.offset, offset, leftSize]
        omega
      · simp only [List.length_append, List.length_cons, count]
        omega

/-- Visit a pseudofinger and return, with exact matching outward/return costs.
These are movement-only traces and leave the represented tree unchanged. -/
theorem visit {h : Hand} (valid : h.Valid) (x : Nat) (member : x ∈ (h.labels 0).inorder) :
    ∃ (v : Pointer.Config) (k : Nat), Pointer.Trace ⟨h.tree, []⟩ v k ∧
      v.key? = some x ∧ Pointer.Trace v ⟨h.tree, []⟩ k ∧ k < 5 * h.count := by
  obtain ⟨a, b, cs, eq, key, depth⟩ := location valid 0 x member
  refine ⟨⟨.node a b, cs⟩, cs.length, ?_, ?_, ?_, depth⟩
  · simpa only [eq] using Pointer.descend cs a b
  · simp only [Pointer.Config.key?]
    congr 1
    omega
  · simpa only [eq] using Pointer.ascend cs a b

theorem serves {h : Hand} (valid : h.Valid) (x : Nat) (member : x ∈ (h.labels 0).inorder) :
    ∃ k, Pointer.Serves h.tree h.tree x k ∧ k ≤ 10 * h.count := by
  obtain ⟨v, k, down, key, up, bound⟩ := visit valid x member
  exact ⟨1 + k + k, ⟨v, ⟨h.tree, []⟩, k, k, down, key, up, rfl, rfl⟩, by omega⟩

theorem build_visit (marks : Finset Nat) (t : Tree) (x : Nat)
    (range : x < t.size) (marked : x ∈ marks) :
    ∃ (v : Pointer.Config) (k : Nat), Pointer.Trace ⟨(build marks t 0).tree, []⟩ v k ∧
      v.key? = some x ∧ Pointer.Trace v ⟨(build marks t 0).tree, []⟩ k ∧ k < 10 * marks.card := by
  have member : x ∈ ((build marks t 0).labels 0).inorder := by
    apply build_marked marks t 0 x _ marked
    rw [RotationBST.Representation.Bridge.inorder_label]
    simpa using range
  obtain ⟨v, k, down, key, up, bound⟩ := visit (build_valid marks t 0) x member
  have count := build_count marks t 0
  exact ⟨v, k, down, key, up, by omega⟩

/-- A marked-key request, including the request charge, costs a constant times
the number of marks in the concrete represented BST. -/
theorem build_serves (marks : Finset Nat) (t : Tree) (x : Nat)
    (range : x < t.size) (marked : x ∈ marks) :
    ∃ k, Pointer.Serves (build marks t 0).tree (build marks t 0).tree x k ∧ k ≤ 20 * marks.card := by
  obtain ⟨v, k, down, key, up, bound⟩ := build_visit marks t x range marked
  exact ⟨1 + k + k, ⟨v, ⟨(build marks t 0).tree, []⟩, k, k, down, key, up, rfl, rfl⟩, by omega⟩

end RotationBST.FingerHand.Hand
