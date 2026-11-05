module

public import RotationBST.Algorithms.OptimalLazyFinger.Recurrence
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger

theorem tabulate_size (w : Nat → Nat → Nat) (univSize stages : Nat) :
    (tabulate w univSize stages).size = stages + 1 := by
  induction stages with
  | zero => simp [tabulate]
  | succ stages ih => simp only [tabulate, Array.size_push, ih]

/-- Every valid cached interval agrees exactly with the recursive specification,
including the reconstructed shape and the deterministic tie breaking. -/
theorem tabulate_lookup (w : Nat → Nat → Nat) (univSize stages n lo : Nat)
    (hn : n ≤ stages) (valid : lo + n ≤ univSize) :
    lookup (tabulate w univSize stages) n lo = solve w n lo := by
  induction stages generalizing n lo with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simp [lookup, tabulate, solve, show lo < univSize + 1 by omega]
  | succ stages ih =>
    by_cases old : n ≤ stages
    · have hne : n ≠ (tabulate w univSize stages).size := by rw [tabulate_size]; omega
      simpa only [tabulate, lookup, Array.getElem?_push, hne, ↓reduceIte]
        using ih n lo old valid
    · have he : n = stages + 1 := by omega
      subst n
      have hsize := tabulate_size w univSize stages
      have hlo : lo < univSize + 1 := by omega
      simp only [tabulate, lookup, Array.getElem?_push, hsize, ↓reduceIte,
        Option.getD_some, Array.getElem?_ofFn, hlo]
      simp only [↓reduceDIte, show lo + stages + 1 ≤ univSize by omega, ↓reduceIte,
        Option.getD_some]
      rw [solve]
      have hc : (fun k : Fin (stages + 1) =>
          let l := lookup (tabulate w univSize stages) k.val lo
          let r := lookup (tabulate w univSize stages) (stages - k.val) (lo + k.val + 1)
          (Tree.node l.1 r.1, w lo (lo + stages + 1) + l.2 + r.2)) =
          (fun k : Fin (stages + 1) =>
          let l := solve w k.val lo
          let r := solve w (stages - k.val) (lo + k.val + 1)
          (Tree.node l.1 r.1, w lo (lo + stages + 1) + l.2 + r.2)) := by
        funext k
        have hl := ih (n := k.val) (lo := lo) (by omega) (by omega)
        have hr := ih (n := stages - k.val) (lo := lo + k.val + 1) (by omega) (by omega)
        rw [hl, hr]
      exact congrArg (fun f : Fin (stages + 1) → Entry =>
        minimum (f ⟨0, Nat.zero_lt_succ stages⟩) ((List.finRange (stages + 1)).map f)) hc

theorem optimize_eq_solve (w : Nat → Nat → Nat) (n : Nat) :
    optimize w n = solve w n 0 := tabulate_lookup w n n n 0 le_rfl (by omega)

end RotationBST.OptimalLazyFinger
