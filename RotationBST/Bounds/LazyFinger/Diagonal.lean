module

import Mathlib.Data.Nat.Find
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Turn eventual witnesses for each factor into one family indexed only by
length. The factor chosen at length `m` is the greatest eligible factor at
most `m`; short lengths use a one-key fallback. -/
theorem sequence_family_of_eventual_witnesses
    (Q : Nat → Nat → List Nat → Prop)
    (decreasing : ∀ a b n xs, a ≤ b → Q b n xs → Q a n xs)
    (witness : ∀ C, ∃ n threshold, 0 < n ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧ Q C n xs) :
    ∃ sizes : Nat → Nat, ∃ family : Nat → List Nat,
      (∀ m, 0 < sizes m ∧ (family m).length = m ∧
        (∀ x ∈ family m, x < sizes m)) ∧
      ∀ C, ∃ threshold, ∀ m, threshold ≤ m → Q C (sizes m) (family m) := by
  classical
  choose n threshold positive witnesses using witness
  let index (m : Nat) := Nat.findGreatest (fun C => threshold C ≤ m) m
  let sizes (m : Nat) := if threshold (index m) ≤ m then n (index m) else 1
  let family (m : Nat) := if h : threshold (index m) ≤ m then
    Classical.choose (witnesses (index m) m h) else List.replicate m 0
  refine ⟨sizes, family, ?_, ?_⟩
  · intro m
    by_cases eligible : threshold (index m) ≤ m
    · have spec := Classical.choose_spec (witnesses (index m) m eligible)
      simpa only [sizes, family, eligible, ↓reduceIte, ↓reduceDIte] using
        And.intro (positive (index m)) (And.intro spec.1 spec.2.1)
    · simp only [sizes, family, eligible, ↓reduceIte, ↓reduceDIte, List.length_replicate]
      refine ⟨by omega, trivial, ?_⟩
      intro x member
      have key := (List.mem_replicate.mp member).2
      omega
  · intro C
    refine ⟨max C (threshold C), ?_⟩
    intro m long
    have fits : C ≤ m := (le_max_left _ _).trans long
    have ready : threshold C ≤ m := (le_max_right _ _).trans long
    have eligible : threshold (index m) ≤ m := Nat.findGreatest_spec (P := fun C => threshold C ≤ m) fits ready
    have factor : C ≤ index m := Nat.le_findGreatest (P := fun C => threshold C ≤ m) fits ready
    have spec := Classical.choose_spec (witnesses (index m) m eligible)
    simpa only [sizes, family, eligible, ↓reduceIte, ↓reduceDIte] using
      decreasing C (index m) (n (index m)) _ factor spec.2.2

end RotationBST.LazyFinger
