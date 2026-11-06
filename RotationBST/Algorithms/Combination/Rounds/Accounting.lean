module

public import RotationBST.Algorithms.Combination.Rounds.Cuts
public import RotationBST.Algorithms.Combination.Rounds.Partition

@[expose] public section
namespace RotationBST.Combo.Rounds

/-- The actual controller's round spans stay in the input prefix. -/
theorem spans_bounds {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    ∀ span ∈ spans worker budget restore s offset xs,
      offset ≤ span.start ∧ span.start ≤ span.stop ∧ span.stop ≤ offset + xs.length := by
  obtain ⟨ordered, inside⟩ := cuts_ordered worker budget restore s offset xs
  exact partition_bounds s.side offset (offset + xs.length) _ (by omega) ordered inside

theorem spans_separated {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    Separated (spans worker budget restore s offset xs) := by
  obtain ⟨ordered, inside⟩ := cuts_ordered worker budget restore s offset xs
  exact partition_separated s.side offset (offset + xs.length) _ (by omega) ordered inside

theorem spans_length {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) :
    (spans worker budget restore s offset xs).length = switches + 1 := by
  rw [spans, partition_length, cuts_length execution offset]

/-- Total rounds are bounded in terms of the rounds of either worker; choosing
a comparator affects only the analysis, never the executable controller. -/
theorem rounds_count {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) (selected : Bool) :
    switches + 1 ≤ 2 * count selected (spans worker budget restore s offset xs) + 1 := by
  have bound := partition_count selected s.side offset (offset + xs.length) (cuts worker budget restore s offset xs)
  change (spans worker budget restore s offset xs).length ≤
    2 * count selected (spans worker budget restore s offset xs) + 1 at bound
  simpa only [spans_length execution offset] using bound

/-- The operational work is linear in the number of rounds of either worker,
including the possibly partial first and last rounds. -/
theorem work_by_rounds {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (limit : s.left ≤ budget)
    (offset : Nat) (selected : Bool) :
    cost ≤ (2 * count selected (spans worker budget restore s offset xs) + 1) * (budget + restore) := by
  have account := execution.account
  have bound := rounds_count execution offset selected
  calc
    cost ≤ (switches + 1) * (budget + restore) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    _ ≤ _ := Nat.mul_le_mul_right _ bound

end RotationBST.Combo.Rounds
