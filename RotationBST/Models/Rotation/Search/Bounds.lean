module

public import RotationBST.Models.Rotation.Search.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tree

theorem searchPath_bounds (t : Tree) (lo x a : Nat) (h : a ∈ t.searchPath lo x) :
    lo ≤ a ∧ a < lo + t.size := by
  induction t generalizing lo with
  | nil => simp [searchPath] at h
  | node l r ihl ihr =>
    simp only [searchPath] at h
    split at h
    · rcases List.mem_cons.mp h with he | h
      · subst a; simp only [Tree.size]; omega
      · have := ihl lo h
        simp only [Tree.size]; omega
    · split at h
      · simp only [List.mem_singleton] at h
        subst a; simp only [Tree.size]; omega
      · rcases List.mem_cons.mp h with he | h
        · subst a; simp only [Tree.size]; omega
        · have := ihr (lo + l.size + 1) h
          simp only [Tree.size]; omega

theorem searchPath_nodup (t : Tree) (lo x : Nat) : (t.searchPath lo x).Nodup := by
  induction t generalizing lo with
  | nil => simp [searchPath]
  | node l r ihl ihr =>
    simp only [searchPath]
    split
    · apply List.nodup_cons.mpr
      constructor
      · intro h
        have := l.searchPath_bounds lo x (lo + l.size) h
        omega
      · exact ihl lo
    · split
      · simp
      · apply List.nodup_cons.mpr
        constructor
        · intro h
          have := r.searchPath_bounds (lo + l.size + 1) x (lo + l.size) h
          omega
        · exact ihr _

theorem root_mem_searchPath (l r : Tree) (lo x : Nat) :
    lo + l.size ∈ (Tree.node l r).searchPath lo x := by
  simp only [searchPath]
  split
  · exact List.mem_cons_self
  · split
    · exact List.mem_singleton_self _
    · exact List.mem_cons_self

/-- Below the root, ancestor and target lie in the same child interval. -/
theorem searchPath_mem_side (l r : Tree) (lo x a : Nat)
    (h : a ∈ (Tree.node l r).searchPath lo x) (hne : a ≠ lo + l.size) :
    (x < lo + l.size ∧ a < lo + l.size) ∨
      (lo + l.size < x ∧ lo + l.size < a) := by
  simp only [searchPath] at h
  split at h
  · rename_i hx
    have hh := (List.mem_cons.mp h).resolve_left hne
    exact Or.inl ⟨hx, (l.searchPath_bounds lo x a hh).2⟩
  · rename_i hx
    split at h
    · simp only [List.mem_singleton] at h
      exact (hne h).elim
    · rename_i he
      have hh := (List.mem_cons.mp h).resolve_left hne
      have hb := r.searchPath_bounds (lo + l.size + 1) x a hh
      exact Or.inr ⟨by omega, by omega⟩

end RotationBST.Tree
