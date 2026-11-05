module

public import RotationBST.Structures.FingerHand.Packed.Updates.Context
public import RotationBST.Structures.FingerHand.Packed.Pruning

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem Expansion.new_key {a b : Hand} (ex : Expansion a b) (lo : Nat) :
    ∃ x, x ∈ (b.labels lo).inorder ∧ x ∉ (a.labels lo).inorder := by
  by_contra none
  push Not at none
  have bound := (labels_distinct b lo).length_le_of_subset none
  simp only [Representation.Bridge.inorder_length, labels_size] at bound
  have := ex.count
  omega

/-- Exactly one key is added, not merely one unit of tree size. -/
theorem Expansion.key_set {a b : Hand} (ex : Expansion a b) (lo x : Nat)
    (fresh : x ∉ (a.labels lo).inorder) (added : x ∈ (b.labels lo).inorder) :
    (b.labels lo).inorder.toFinset = insert x (a.labels lo).inorder.toFinset := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rcases Finset.mem_insert.mp hy with eq | hy
    · exact List.mem_toFinset.mpr (eq ▸ added)
    · exact List.mem_toFinset.mpr ((ex.keys lo).subset (List.mem_toFinset.mp hy))
  · have notin : x ∉ (a.labels lo).inorder.toFinset := by simpa using fresh
    simp only [Finset.card_insert_of_notMem notin, List.toFinset_card_of_nodup (labels_distinct a lo),
      List.toFinset_card_of_nodup (labels_distinct b lo), Representation.Bridge.inorder_length, labels_size]
    exact le_of_eq ex.count

/-- Marking the newly exposed key makes an expansion exactly canonical for the
enlarged mark set. No extra, unaccounted-for pseudofingers remain. -/
theorem Expansion.mark_added {a b : Hand} (ex : Expansion a b) (marks : Finset Nat) (lo x : Nat)
    (canonical : a.labels lo = compress marks a.reference lo)
    (fresh : x ∉ (a.labels lo).inorder) (added : x ∈ (b.labels lo).inorder) :
    b.labels lo = compress (insert x marks) b.reference lo := by
  have covers : ∀ y ∈ (b.reference.labelFrom lo).inorder, y ∈ insert x marks →
      y ∈ (b.labels lo).inorder := by
    intro y hy hm
    rcases Finset.mem_insert.mp hm with eq | hm
    · simpa only [eq] using added
    · rw [ex.reference] at hy
      have old := marked_mem marks a.reference lo y hy hm
      rw [← canonical] at old
      exact (ex.keys lo).subset old
  have projected := b.prune_labels (insert x marks) lo covers
  have retained : (a.labels lo).inorder.Sublist (compress (insert x marks) b.reference lo).inorder := by
    rw [canonical, ex.reference]
    exact compress_submarks (Finset.subset_insert _ _) _ _
  have newKey : x ∈ (compress (insert x marks) b.reference lo).inorder :=
    marked_mem _ _ _ x ((labels_sublist b lo).subset added) (Finset.mem_insert_self _ _)
  have strict : (a.labels lo).inorder.length < (compress (insert x marks) b.reference lo).inorder.length := by
    have weak := retained.length_le
    by_contra h
    have eq := retained.eq_of_length (by omega)
    exact fresh (eq ▸ newKey)
  have contraction := prune_contracts (insert x marks) (b.labels lo)
  have size := contraction.size_le
  have count := ex.count
  rw [projected] at size
  simp only [Representation.Bridge.inorder_length, labels_size] at strict size
  have equal : (b.labels lo).erase.size = (prune (insert x marks) (b.labels lo)).erase.size := by
    rw [projected, labels_size]
    omega
  exact (contraction.eq_of_size equal).trans projected

/-- A temporary expansion of a maintained state has precisely the old marks
plus its new key. Pruning to any smaller mark set restores that set's exact
skeleton. This separates mark maintenance from the physical suppression steps. -/
theorem Expansion.prune_to {a b : Hand} (ex : Expansion a b) (marks target : Finset Nat) (lo x : Nat)
    (canonical : a.labels lo = compress marks a.reference lo)
    (fresh : x ∉ (a.labels lo).inorder) (added : x ∈ (b.labels lo).inorder)
    (sub : target ⊆ insert x marks) :
    prune target (b.labels lo) = compress target b.reference lo := by
  rw [ex.mark_added marks lo x canonical fresh added]
  exact prune_compress sub _ _

end RotationBST.FingerHand.Hand
