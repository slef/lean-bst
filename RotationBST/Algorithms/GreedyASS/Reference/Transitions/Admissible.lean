module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Distance
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

theorem occurs_trans {t : Tree} {lo k m : Nat} {a b : Component}
    (outer : Distance.Occurs t lo a k) (inner : Distance.Occurs a.shape a.first b m) :
    Distance.Occurs t lo b (k + m) := by
  induction outer with
  | root => simpa using inner
  | left h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Distance.Occurs.left (ih inner)
  | right h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Distance.Occurs.right (ih inner)

theorem admissible_inverse {t : Tree} {lo : Nat} (event : Event) :
    Admissible t lo event.inverse ↔ Admissible t lo event := by
  cases event <;> rfl

theorem admissible_lift {t : Tree} {lo k : Nat} {c : Component} {event : Event}
    (outer : Distance.Occurs t lo c k) (inner : Admissible c.shape c.first event) :
    Admissible t lo event := by
  obtain ⟨m, inner⟩ := inner
  exact ⟨k + m, occurs_trans outer inner⟩

theorem descend_admissible (t : Tree) (lo searched : Nat) :
    ∀ event ∈ descend t lo searched, Admissible t lo event := by
  induction t generalizing lo with
  | nil => simp [descend]
  | node l r il ir =>
    intro event member
    rw [descend] at member
    rcases List.mem_cons.mp member with same | member
    · subst event
      exact ⟨0, .root _ _⟩
    · by_cases left : searched < lo + leaves l
      · rw [ite_eq_left left] at member
        exact admissible_lift (Distance.Occurs.left (.root l lo)) (il lo event member)
      · rw [ite_eq_right left] at member
        exact admissible_lift (Distance.Occurs.right (.root r (lo + leaves l)))
          (ir _ event member)

theorem ascend_admissible (t : Tree) (lo searched : Nat) :
    ∀ event ∈ ascend t lo searched, Admissible t lo event := by
  intro event member
  unfold ascend at member
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp member
  exact (admissible_inverse e).mpr
    (descend_admissible t lo searched e (List.mem_reverse.mp he))

theorem plan_admissible (t : Tree) (lo old new : Nat) :
    ∀ event ∈ plan t lo old new, Admissible t lo event := by
  induction t generalizing lo with
  | nil => simp [plan]
  | node l r il ir =>
    intro event member
    by_cases left : old < lo + leaves l ∧ new < lo + leaves l
    · rw [plan, ite_eq_left left] at member
      exact admissible_lift (Distance.Occurs.left (.root l lo)) (il lo event member)
    · by_cases right : lo + leaves l ≤ old ∧ lo + leaves l ≤ new
      · rw [plan, ite_eq_right left, ite_eq_left right] at member
        exact admissible_lift (Distance.Occurs.right (.root r (lo + leaves l)))
          (ir _ event member)
      · rw [plan, ite_eq_right left, ite_eq_right right] at member
        rcases List.mem_append.mp member with member | member
        · exact ascend_admissible _ _ _ event member
        · exact descend_admissible _ _ _ event member

end RotationBST.Geometric.GreedyASS.Reference.Transitions
