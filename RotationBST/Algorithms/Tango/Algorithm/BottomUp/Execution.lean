module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Comparison
public import RotationBST.Algorithms.Tango.State.Preferences.Order
public import RotationBST.Algorithms.Tango.Algorithm.Policy
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Initialization

/-- Retain the precise update charge through the final component access. -/
theorem request_spec (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    Access s.tree (serve s reference past x).1.tree x (serve s reference past x).2 ∧
      Maintains (serve s reference past x).1 reference (past ++ [x]) ∧
      ((serve s reference past x).2 : ℝ) + (serve s reference past x).1.potential - s.potential ≤
        requestCharge reference past x := by
  let updated := (s.updatePreferences (canonical reference 0 past) (preferenceUpdates reference 0 past x).reverse).1
  obtain ⟨nesting, rotations, ba⟩ := log_spec s (canonical reference 0 past) (preferenceUpdates reference 0 past x).reverse
    maintained.2 (canonical_pathMarked reference 0 past)
    (by intro e member; simpa only [canonical_tree, Nat.zero_add] using
      (preferenceUpdates_bounds reference 0 past x e (List.mem_reverse.mp member)).2)
  rw [preferenceUpdates_reverse_canonical reference past x history valid] at nesting
  have invariant := maintains_of_nesting updated reference (past ++ [x]) nesting
  have onPath : x ∈ updated.region.keys 0 := by
    rw [invariant.1.2.2]
    exact List.mem_toFinset.mpr (request_on_root_path reference 0 past x (Nat.zero_le _) (by simpa using valid))
  obtain ⟨served, finalInvariant, bb⟩ := maintained_splayRoot updated reference (past ++ [x]) invariant x onPath
  refine ⟨⟨rotations.append served.1, served.2⟩, finalInvariant, ?_⟩
  simp only [serve, requestCharge, Nat.cast_add]
  dsimp only [updated] at bb
  linarith

private theorem extend_history {reference : Tree} {past : List Nat} {x : Nat}
    (history : ∀ y ∈ past, y < reference.size) (valid : x < reference.size) :
    ∀ y ∈ past ++ [x], y < reference.size := by
  intro y member
  rcases List.mem_append.mp member with member | member
  · exact history y member
  · simpa only [List.mem_singleton.mp member] using valid

/-- Flattening requests preserves the charged evolving reference, including
all intermediate component sizes used for first joins. -/
theorem sequenceCharge_eq (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    sequenceCharge reference past xs = logCharge (canonical reference 0 past) (log reference past xs) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  induction xs generalizing past with
  | nil => simp [sequenceCharge, logCharge, log]
  | cons x xs ih =>
    have key := valid x (by simp)
    have remaining := ih (past ++ [x]) (extend_history history key)
      (fun y member => valid y (by simp [member]))
    simp only [sequenceCharge, requestCharge, remaining, log, logCharge_append,
      preferenceUpdates_reverse_canonical reference past x history key, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- Telescoping holds from any maintained state and valid history. The step
equation identifies the concrete implementation whose bound is proved here. -/
theorem runFrom_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (s : MarkedTree) (past xs : List Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.runFrom past s xs).2 : ℝ) +
      (p.runFrom past s xs).1.potential - s.potential ≤ sequenceCharge reference past xs := by
  induction xs generalizing s past with
  | nil => simp [Policy.runFrom, sequenceCharge]
  | cons x xs ih =>
    have key := valid x (by simp)
    obtain ⟨_, invariant, first⟩ := request_spec s reference past x maintained history key
    have rest := ih (serve s reference past x).1 (past ++ [x]) invariant (extend_history history key)
      (fun y member => valid y (by simp [member]))
    simp only [Policy.runFrom, steps, Nat.cast_add, sequenceCharge]
    change _ ≤ requestCharge reference past x + sequenceCharge reference (past ++ [x]) xs
    linarith

/-- The complete executable Tango run pays the refined initialization-aware
log charge and one logarithmic component access per request. The initial
potential is zero; no separate uniform initialization charge is introduced. -/
theorem run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤
      logCharge (initial reference) (log reference [] xs) +
        xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  have bound := runFrom_bound p steps (initial reference) [] xs
    (initial_maintains reference) (by simp) valid
  rw [initial_potential, sequenceCharge_eq reference [] xs (by simp) valid, canonical_initial] at bound
  have nonnegative := potential_nonneg (p.run xs).1
  change ((p.run xs).2 : ℝ) + (p.run xs).1.potential - 0 ≤ _ at bound
  linarith

/-- The reordered implementation inhabits the same online policy contract. -/
def policy (reference : Tree) : Policy reference where
  step := fun past s x => serve s reference past x
  correct := by
    intro past s x maintained history valid
    obtain ⟨access, invariant, refined⟩ := request_spec s reference past x maintained history valid
    refine ⟨access, invariant, ?_⟩
    have uniform := Initialization.logCharge_le (canonical reference 0 past)
      (preferenceUpdates reference 0 past x).reverse (canonical_pathMarked reference 0 past)
      (by intro e member; simpa only [canonical_tree, Nat.zero_add] using
        (preferenceUpdates_bounds reference 0 past x e (List.mem_reverse.mp member)).2)
    simp only [List.length_reverse, canonical_tree] at uniform
    unfold requestCharge at refined
    linarith

/-- Choose the concrete executable policy before every input sequence. -/
theorem policy_exists (reference : Tree) :
    ∃ p : Policy reference,
      (∀ past s x, p.step past s x = serve s reference past x) ∧
      ∀ xs, (∀ x ∈ xs, x < reference.size) →
        ((p.run xs).2 : ℝ) ≤ logCharge (initial reference) (log reference [] xs) +
          xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  refine ⟨policy reference, fun _ _ _ => rfl, ?_⟩
  exact run_bound (policy reference) (fun _ _ _ => rfl)

end RotationBST.Tango.BottomUp
