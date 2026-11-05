module

public import RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Access
public import RotationBST.Algorithms.GreedyASS.Abstract
public import RotationBST.Models.Geometric.Online.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

theorem points_append (xs ys : List Nat) :
    points (xs ++ ys) = fill greedySweep xs.length (points xs) ys := by
  simpa [points] using fill_append greedySweep 0 ∅ xs ys

theorem points_snoc (xs : List Nat) (x : Nat) :
    points (xs ++ [x]) = points xs ∪ row xs.length (keys xs x) := by
  rw [points_append]
  rfl

theorem points_history (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    History n xs.length (points xs) := by
  have run := fill_spec (greedyASS n) 0 ∅ xs
    (by simp [History]) ass_empty valid
  simpa [points, greedyASS] using run.2.1

theorem old_member {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (old : NonVirgin t lo history request c) : c ∈ forest t lo request := by
  obtain ⟨_, _, _, _, _, _, _, persistent⟩ := old
  exact persistent request (by simp)

/-- An old root constrains every new access to one side of an earlier
accessed key within it. The witness comes from actual GreedyASS execution. -/
theorem old_barrier {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t)
    (old : NonVirgin t lo history request c) :
    ∃ accessed, c.Contains accessed ∧
      ((∀ x ∈ keys history request, x ≤ accessed) ∨
        (∀ x ∈ keys history request, accessed ≤ x)) := by
  obtain ⟨prior, first, rest, accessed, eq, touched, within, persistent⟩ := old
  subst history
  have headValid : ∀ x ∈ prior ++ [first], x < lo + leaves t := by
    intro x hx
    apply (valid x ?_).2
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto
  have tailValid : ∀ x ∈ rest ++ [request], lo ≤ x ∧ x < lo + leaves t := by
    intro x hx
    apply valid x
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto
  have headHistory : History (lo + leaves t) (prior.length + 1) (points (prior ++ [first])) := by
    simpa using points_history (lo + leaves t) (prior ++ [first]) headValid
  have point : (accessed, prior.length) ∈ points (prior ++ [first]) := by
    rw [points_snoc]
    exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨touched, rfl⟩)
  have barrier := Reference.persistent_barrier t lo (rest ++ [request]) headHistory point within
    tailValid (fun x hx => persistent x (List.mem_cons_of_mem _ hx))
  have continuation : points ((prior ++ first :: rest) ++ [request]) =
      fill greedySweep (prior.length + 1) (points (prior ++ [first])) (rest ++ [request]) := by
    have split : (prior ++ first :: rest) ++ [request] =
        (prior ++ [first]) ++ (rest ++ [request]) := by simp [List.append_assoc]
    rw [split, points_append]
    simp
  have rowPoint : ∀ x ∈ keys (prior ++ first :: rest) request,
      (x, (prior ++ first :: rest).length) ∈
        fill greedySweep (prior.length + 1) (points (prior ++ [first])) (rest ++ [request]) := by
    intro x hx
    rw [← continuation, points_snoc]
    exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩)
  have recent : prior.length < (prior ++ first :: rest).length := by simp
  refine ⟨accessed, within, ?_⟩
  rcases barrier with left | right
  · exact Or.inl (fun x hx => left.2 _ (rowPoint x hx) recent)
  · exact Or.inr (fun x hx => right.2 _ (rowPoint x hx) recent)

end RotationBST.Geometric.GreedyASS.Virgin
