module

public import RotationBST.Structures.FingerHand.Packed.Navigation

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem build_singleton_outside (t : Tree) (lo x : Nat) (outside : x < lo ∨ lo + t.size ≤ x) :
    build {x} t lo = .knuckle t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    simp only [Tree.size] at outside
    have hm : lo + l.size ∉ ({x} : Finset Nat) := by simp only [Finset.mem_singleton]; omega
    have hl := ihl lo (by omega)
    have hr := ihr (lo + l.size + 1) (by omega)
    simp only [build, hm, ↓reduceIte, hl, hr]

theorem build_singleton_root (l r : Tree) (lo : Nat) :
    build {lo + l.size} (.node l r) lo =
      .node [] (Tendon.State.ofPath []) (.knuckle l) (.knuckle r) := by
  have hl := build_singleton_outside l lo (lo + l.size) (Or.inr (Nat.le_refl _))
  have hr := build_singleton_outside r (lo + l.size + 1) (lo + l.size) (Or.inl (by omega))
  simp [build, hl, hr]

theorem initial_marks (k : Nat) (t : Tree) : stateMarks (Multifinger.initial k t) = {rootRank t} := by
  have pos : ∀ i : Fin k, (Multifinger.initial k t).position i = rootRank t := by
    intro i
    cases t <;> rfl
  apply Finset.ext
  intro a
  simp only [stateMarks, Finset.mem_insert, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (eq | ⟨i, _, eq⟩)
    · exact eq
    · rw [pos] at eq
      exact eq.symm
  · exact Or.inl

/-- When all fingers start at the root, packing performs no tree change and
creates no potential debt. In particular, no linear startup cost is required. -/
theorem initial_tree (k : Nat) (t : Tree) :
    (forState (Multifinger.initial k t)).tree = t ∧
      (forState (Multifinger.initial k t)).potential = 0 := by
  simp only [forState, initial_marks]
  cases t with
  | nil => exact ⟨rfl, rfl⟩
  | node l r =>
    have root := build_singleton_root l r 0
    simp only [Nat.zero_add] at root
    simp only [Multifinger.initial, rootRank]
    rw [root]
    exact ⟨rfl, rfl⟩

theorem forState_valid {k : Nat} (s : Multifinger.State k) : (forState s).Valid :=
  build_valid (stateMarks s) s.tree 0

theorem forState_reference {k : Nat} (s : Multifinger.State k) : (forState s).reference = s.tree :=
  build_reference (stateMarks s) s.tree 0

theorem forState_count {k : Nat} (s : Multifinger.State k) : (forState s).count ≤ 2 * (k + 1) := by
  have count := build_count (stateMarks s) s.tree 0
  have marks := stateMarks_card s
  unfold forState
  omega

/-- Each actual finger is reachable in the packed whole BST with cost bounded
only by the finger count, even when its reference-tree depth is large. -/
theorem forState_visit {k : Nat} (s : Multifinger.State k) (valid : s.Valid) (i : Fin k) :
    ∃ (v : Pointer.Config) (m : Nat), Pointer.Trace ⟨(forState s).tree, []⟩ v m ∧
      v.key? = some (s.position i) ∧ Pointer.Trace v ⟨(forState s).tree, []⟩ m ∧ m < 10 * (k + 1) := by
  have marked : s.position i ∈ stateMarks s :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨v, m, down, key, up, bound⟩ := build_visit (stateMarks s) s.tree (s.position i) (valid i) marked
  have count := stateMarks_card s
  exact ⟨v, m, down, key, up, by omega⟩

theorem forState_serves {k : Nat} (s : Multifinger.State k) (valid : s.Valid) (i : Fin k) :
    ∃ m, Pointer.Serves (forState s).tree (forState s).tree (s.position i) m ∧ m ≤ 20 * (k + 1) := by
  obtain ⟨v, m, down, key, up, bound⟩ := forState_visit s valid i
  exact ⟨1 + m + m, ⟨v, ⟨(forState s).tree, []⟩, m, m, down, key, up, rfl, rfl⟩, by omega⟩

end RotationBST.FingerHand.Hand
