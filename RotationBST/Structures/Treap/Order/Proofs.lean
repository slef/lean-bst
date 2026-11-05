module

public import RotationBST.Models.Rotation.Search.Bounds
public import RotationBST.Structures.Treap.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric

/-- In a treap with distinct priorities, being an ancestor is equivalent to
having minimum priority on the inorder interval between the two keys. This is
the deterministic event characterization used in random-treap analysis. -/
theorem heap_ancestor_iff {α : Type} [LinearOrder α] (priority : Nat → α)
    (t : Tree) (lo a x : Nat) (heap : Heap priority t lo)
    (unique : Set.InjOn priority (Set.Ico lo (lo + t.size)))
    (ha : lo ≤ a ∧ a < lo + t.size) (hx : lo ≤ x ∧ x < lo + t.size) :
    a ∈ t.searchPath lo x ↔
      ∀ b, min a x ≤ b → b ≤ max a x → priority a ≤ priority b := by
  induction t generalizing lo a x with
  | nil => simp [Tree.size] at ha; omega
  | node l r ihl ihr =>
    have hroot : ∀ b, lo ≤ b → b < lo + (Tree.node l r).size →
        priority (lo + l.size) ≤ priority b := by
      intro b hb hb'
      have h := heap.1 (b - lo) (by simp only [Tree.size] at hb'; omega)
      simpa only [Nat.add_sub_of_le hb] using h
    have leftUnique : Set.InjOn priority (Set.Ico lo (lo + l.size)) := by
      intro i hi j hj he
      apply unique _ _ he <;> simp only [Set.mem_Ico, Tree.size] at * <;> omega
    have rightUnique : Set.InjOn priority
        (Set.Ico (lo + l.size + 1) (lo + l.size + 1 + r.size)) := by
      intro i hi j hj he
      apply unique _ _ he <;> simp only [Set.mem_Ico, Tree.size] at * <;> omega
    have rootRange : lo ≤ lo + l.size ∧ lo + l.size < lo + (Tree.node l r).size := by
      simp only [Tree.size]; omega
    have rootMin : ∀ b, min (lo + l.size) x ≤ b → b ≤ max (lo + l.size) x →
        priority (lo + l.size) ≤ priority b := by
      intro b hb hb'
      apply hroot b <;> omega
    have rootForced (h : ∀ b, min a x ≤ b → b ≤ max a x → priority a ≤ priority b)
        (between : min a x ≤ lo + l.size ∧ lo + l.size ≤ max a x) : a = lo + l.size := by
      apply unique ha rootRange
      exact le_antisymm (h _ between.1 between.2) (hroot a ha.1 ha.2)
    by_cases hxl : x < lo + l.size
    · simp only [Tree.searchPath, hxl, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact rootMin
        · have arange : lo ≤ a ∧ a < lo + l.size := l.searchPath_bounds lo x a h
          exact (ihl lo a x heap.2.1 leftUnique arange ⟨hx.1, hxl⟩).mp h
      · intro h
        by_cases hal : a < lo + l.size
        · exact Or.inr ((ihl lo a x heap.2.1 leftUnique ⟨ha.1, hal⟩ ⟨hx.1, hxl⟩).mpr h)
        · exact Or.inl (rootForced h ⟨by omega, by omega⟩)
    · by_cases hxe : x = lo + l.size
      · subst x
        simp only [Tree.searchPath, Nat.lt_irrefl, ↓reduceIte, List.mem_singleton]
        constructor
        · intro he; subst a; exact rootMin
        · intro h
          apply rootForced h
          constructor <;> omega
      · simp only [Tree.searchPath, hxl, hxe, ↓reduceIte, List.mem_cons]
        have xr : lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size := by
          simp only [Tree.size] at hx; omega
        constructor
        · rintro (rfl | h)
          · exact rootMin
          · have arange : lo + l.size + 1 ≤ a ∧ a < lo + l.size + 1 + r.size := r.searchPath_bounds (lo + l.size + 1) x a h
            exact (ihr _ a x heap.2.2 rightUnique arange xr).mp h
        · intro h
          by_cases har : lo + l.size < a
          · have ar : lo + l.size + 1 ≤ a ∧ a < lo + l.size + 1 + r.size := by
              simp only [Tree.size] at ha; omega
            exact Or.inr ((ihr _ a x heap.2.2 rightUnique ar xr).mpr h)
          · exact Or.inl (rootForced h ⟨by omega, by omega⟩)

/-- Distinct priorities determine a unique treap shape on an inorder interval. -/
theorem heap_unique {α : Type} [LinearOrder α] (priority : Nat → α)
    (t u : Tree) (lo : Nat) (size : t.size = u.size)
    (ht : Heap priority t lo) (hu : Heap priority u lo)
    (unique : Set.InjOn priority (Set.Ico lo (lo + t.size))) : t = u := by
  induction t generalizing u lo with
  | nil =>
    cases u with
    | nil => rfl
    | node l r => simp only [Tree.size] at size; omega
  | node l r ihl ihr =>
    cases u with
    | nil => simp only [Tree.size] at size; omega
    | node l' r' =>
      have hs : l.size + 1 + r.size = l'.size + 1 + r'.size := size
      have hroot : lo + l.size = lo + l'.size := by
        apply unique
        · simp only [Set.mem_Ico, Tree.size]; omega
        · simp only [Set.mem_Ico, Tree.size]; omega
        · apply le_antisymm
          · exact ht.1 l'.size (by omega)
          · exact hu.1 l.size (by omega)
      have hl : l.size = l'.size := by omega
      have hr : r.size = r'.size := by omega
      have hleft : l = l' := by
        apply ihl l' lo hl ht.2.1 hu.2.1
        intro a ha b hb he
        apply unique _ _ he <;> simp only [Set.mem_Ico, Tree.size] at * <;> omega
      have hright : r = r' := by
        apply ihr r' (lo + l.size + 1) hr ht.2.2
        · simpa only [hl] using hu.2.2
        · intro a ha b hb he
          apply unique _ _ he <;> simp only [Set.mem_Ico, Tree.size] at * <;> omega
      rw [hleft, hright]

end RotationBST.Geometric
