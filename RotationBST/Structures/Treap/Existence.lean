module

public import RotationBST.Structures.Treap.Abstract
import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section
namespace RotationBST.Arboral

/-- Every finite inorder interval admits a treap, with arbitrary ties. -/
theorem heap_exists (priority : Nat → WithTop Nat) (n lo : Nat) :
    ∃ t : Tree, t.size = n ∧ Heap priority t lo := by
  classical
  induction n using Nat.strong_induction_on generalizing lo with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨.nil, rfl, trivial⟩
    have positive : 0 < n := by omega
    obtain ⟨k, hk, hmin⟩ := (Finset.range n).exists_min_image
      (fun x => priority (lo + x)) ⟨0, Finset.mem_range.mpr positive⟩
    have hkn := Finset.mem_range.mp hk
    obtain ⟨l, hl, hheapl⟩ := ih k hkn lo
    obtain ⟨r, hr, hheapr⟩ := ih (n - k - 1) (by omega) (lo + k + 1)
    refine ⟨.node l r, ?_, ?_⟩
    · simp only [Tree.size, hl, hr]; omega
    · simp only [Heap, hl, hr]
      refine ⟨?_, hheapl, hheapr⟩
      intro x hx
      exact hmin x (Finset.mem_range.mpr (by omega))

end RotationBST.Arboral
