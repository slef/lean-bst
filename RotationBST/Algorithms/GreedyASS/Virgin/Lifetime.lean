module

public import RotationBST.Algorithms.GreedyASS.Virgin.History
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

theorem initially_virgin (t : Tree) (lo request : Nat) (c : Component) :
    ¬ NonVirgin t lo [] request c := by
  rintro ⟨prior, first, rest, _, split, _⟩
  have length := congrArg List.length split
  simp at length

/-- Exact lifetime update: a component survives into the next forest and
either was already non-virgin or is touched on the just-completed row.
Failure to survive erases all evidence from an older lifetime. -/
theorem advance (t : Tree) (lo : Nat) (history : List Nat) (request next : Nat) (c : Component) :
    NonVirgin t lo (history ++ [request]) next c ↔
      c ∈ forest t lo next ∧
        (NonVirgin t lo history request c ∨
          (c ∈ forest t lo request ∧ ∃ x ∈ keys history request, c.Contains x)) := by
  constructor
  · rintro ⟨prior, first, rest, accessed, split, point, within, persistent⟩
    refine ⟨persistent next (by simp), ?_⟩
    rcases List.eq_nil_or_concat rest with empty | ⟨ys, last, eq⟩
    · subst rest
      have parts := List.append_inj' split (by simp)
      have firstEq : request = first := by simpa using parts.2
      have priorEq := parts.1
      subst prior
      subst first
      exact Or.inr ⟨persistent request (by simp), accessed, point, within⟩
    · rw [List.concat_eq_append] at eq
      subst rest
      have split' : history ++ [request] = (prior ++ first :: ys) ++ [last] := by
        simpa [List.append_assoc] using split
      have parts := List.append_inj' split' (by simp)
      have lastEq : request = last := by simpa using parts.2
      subst last
      refine Or.inl ⟨prior, first, ys, accessed, parts.1, point, within, ?_⟩
      intro x hx
      apply persistent x
      simp only [List.mem_cons, List.mem_append] at hx ⊢
      tauto
  · rintro ⟨survives, old | ⟨member, accessed, point, within⟩⟩
    · obtain ⟨prior, first, rest, accessed, split, point, within, persistent⟩ := old
      refine ⟨prior, first, rest ++ [request], accessed, ?_, point, within, ?_⟩
      · simp [split, List.append_assoc]
      · intro x hx
        by_cases eq : x = next
        · simpa [eq] using survives
        · apply persistent x
          simp only [List.mem_cons, List.mem_append] at hx ⊢
          tauto
    · refine ⟨history, request, [], accessed, rfl, point, within, ?_⟩
      intro x hx
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact member
      · exact survives

/-- Keeping the current forest fixed during Phase II removes precisely the
virgin roots touched by the new row. This relates `after` to real lifetimes. -/
theorem roots_after (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    roots t lo (history ++ [request]) request =
      roots t lo history request \ touched t lo history request := by
  classical
  ext c
  simp only [roots, touched, Finset.mem_filter, List.mem_toFinset, Finset.mem_sdiff,
    advance]
  aesop

end RotationBST.Geometric.GreedyASS.Virgin
