module

public import RotationBST.Models.Region.Basic
public import RotationBST.Structures.Treap.Priorities

@[expose] public section
namespace RotationBST.Geometric
open Pointer.Lazy.Skeleton

theorem heap_congr {α : Type} [LE α] {p q : Nat → α} (t : Tree) (lo : Nat)
    (h : Heap p t lo) (same : ∀ x, lo ≤ x → x < lo + t.size → p x = q x) :
    Heap q t lo := by
  induction t generalizing lo with
  | nil => trivial
  | node l r il ir =>
    obtain ⟨root, hl, hr⟩ := h
    refine ⟨?_, il lo hl ?_, ir (lo + l.size + 1) hr ?_⟩
    · intro x hx
      rw [← same (lo + l.size) (by omega) (by simp only [Tree.size]; omega),
        ← same (lo + x) (by omega) (by simp only [Tree.size]; omega)]
      exact root x hx
    · intro x hlo hhi
      exact same x hlo (by simp only [Tree.size]; omega)
    · intro x hlo hhi
      exact same x (by omega) (by simp only [Tree.size]; omega)

theorem no_current_of_root {P : Finset Point} {time lo : Nat} {l r : Tree}
    (h : Heap (nextTouch P time) (.node l r) lo)
    (root : (lo + l.size, time) ∉ P) :
    ∀ x, lo ≤ x → x < lo + (Tree.node l r).size → (x, time) ∉ P := by
  intro x hlo hhi hx
  have hhigh : ((time + 1 : Nat) : WithTop Nat) ≤ nextTouch P time (lo + l.size) := by
    apply le_nextTouch
    intro future hp ht
    have hne : future ≠ time := by rintro rfl; exact root hp
    exact_mod_cast (show time + 1 ≤ future by omega)
  have hr := h.1 (x - lo) (by simp only [Tree.size] at hhi; omega)
  have heq : lo + (x - lo) = x := by omega
  rw [heq, nextTouch_current hx] at hr
  have impossible := hhigh.trans hr
  have : time + 1 ≤ time := by exact_mod_cast impossible
  omega

namespace Region

theorem project_tree (P : Finset Point) (time : Nat) (t : Tree) (lo : Nat) :
    (project P time t lo).tree = t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [project]; split <;> simp [tree, il, ir]

theorem project_keys {P : Finset Point} {time : Nat} (t : Tree) (lo x : Nat)
    (h : Heap (nextTouch P time) t lo) :
    x ∈ keys (project P time t lo) lo ↔ (x, time) ∈ P ∧ lo ≤ x ∧ x < lo + t.size := by
  induction t generalizing lo with
  | nil => simp [project, keys, Tree.size]
  | node l r il ir =>
    simp only [project]
    split
    next hroot =>
      simp only [keys, project_tree, Finset.mem_insert, Finset.mem_union,
        il lo h.2.1, ir (lo + l.size + 1) h.2.2, Tree.size]
      constructor
      · rintro (rfl | ⟨hp, hlo, hhi⟩ | ⟨hp, hlo, hhi⟩)
        · exact ⟨hroot, by omega, by omega⟩
        · exact ⟨hp, hlo, by omega⟩
        · exact ⟨hp, by omega, by omega⟩
      · rintro ⟨hp, hlo, hhi⟩
        by_cases he : x = lo + l.size
        · exact Or.inl he
        · right
          by_cases hl : x < lo + l.size
          · exact Or.inl ⟨hp, hlo, hl⟩
          · exact Or.inr ⟨hp, by omega, by omega⟩
    next hroot =>
      simp only [keys, Finset.notMem_empty, false_iff, not_and]
      intro hp hlo hhi
      exact no_current_of_root h hroot x hlo hhi hp

theorem project_holes {P : Finset Point} {time : Nat} (t : Tree) (lo : Nat)
    (h : Heap (nextTouch P time) t lo) :
    ∀ entry ∈ holes (project P time t lo) lo,
      Heap (nextTouch P (time + 1)) entry.2 entry.1 := by
  induction t generalizing lo with
  | nil => simp [project, holes, Heap]
  | node l r il ir =>
    simp only [project]
    split
    next hroot =>
      intro entry he
      simp only [holes, project_tree, List.mem_append] at he
      rcases he with he | he
      · exact il lo h.2.1 entry he
      · exact ir (lo + l.size + 1) h.2.2 entry he
    next hroot =>
      intro entry he
      have heq : entry = (lo, .node l r) := by simpa only [holes, List.mem_singleton] using he
      subst entry
      apply heap_congr _ _ h
      intro x hlo hhi
      exact (nextTouch_unchanged (no_current_of_root h hroot x hlo hhi)).symm

end Region
end RotationBST.Geometric
