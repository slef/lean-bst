module

public import RotationBST.Algorithms.Tango.Algorithm.Policy
public import RotationBST.Models.Rotation.Connectivity.Abstract
public import RotationBST.Algorithms.Splay.Online.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango

private theorem policy_append {reference : Tree} (p : Policy reference)
    (past : List Nat) (s : MarkedTree) (xs ys : List Nat) :
    p.runFrom past s (xs ++ ys) =
      let first := p.runFrom past s xs
      let last := p.runFrom (past ++ xs) first.1 ys
      (last.1, first.2 + last.2) := by
  induction xs generalizing past s with
  | nil => simp [Policy.runFrom]
  | cons x xs ih => simp [Policy.runFrom, ih, List.append_assoc, Nat.add_assoc]

private theorem history_step {reference : Tree} (p : Policy reference) (past : List Nat) (x : Nat) :
    (p.run (past ++ [x])).1 = (p.step past (p.run past).1 x).1 := by
  simp [Policy.run, policy_append, Policy.runFrom]

private noncomputable def repair (s t : Tree) : Nat :=
  if s = t then 0 else if same : s.size = t.size then Classical.choose (Geometry.reset s t same) else 0

private theorem repair_spec (s t : Tree) (same : s.size = t.size) :
    repair s t ≤ 2 * s.size ∧ Rotations s t (repair s t) := by
  classical
  by_cases equal : s = t
  · subst t
    simp only [repair, ↓reduceIte]
    exact ⟨Nat.zero_le _, .refl⟩
  · rw [repair, ite_eq_right equal, dite_eq_left same]
    exact Classical.choose_spec (Geometry.reset s t same)

private noncomputable def liftedStep {reference : Tree} (p : Policy reference)
    (past : List Nat) (s : Tree) (x : Nat) : Tree × Nat :=
  if (∀ y ∈ past, y < reference.size) ∧ s.size = reference.size ∧ x < reference.size then
    ((p.step past (p.run past).1 x).1.tree,
      repair s (p.run past).1.tree + (p.step past (p.run past).1 x).2)
  else Splay.algorithm.step past s x

private theorem lifted_correct {reference : Tree} (p : Policy reference)
    (past : List Nat) (s : Tree) (x : Nat) (valid : x < s.size) :
    Access s (liftedStep p past s x).1 x (liftedStep p past s x).2 := by
  classical
  unfold liftedStep
  split_ifs with good
  · obtain ⟨execution, maintained, _⟩ := p.run_spec past good.1
    have source := (p.correct past (p.run past).1 x maintained good.1 good.2.2).1
    have reset := (repair_spec s (p.run past).1.tree (good.2.1.trans execution.size_eq)).2
    exact ⟨reset.append source.1, source.2⟩
  · exact Splay.algorithm.correct past s x valid

private noncomputable def lifted {reference : Tree} (p : Policy reference) : RotationBST.Algorithm :=
  ⟨liftedStep p, lifted_correct p⟩

private theorem lifted_step {reference : Tree} (p : Policy reference) (past : List Nat) (x : Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : x < reference.size) :
    (lifted p).step past (p.run past).1.tree x =
      ((p.step past (p.run past).1 x).1.tree, (p.step past (p.run past).1 x).2) := by
  classical
  have size := (p.run_spec past history).1.size_eq.symm
  change liftedStep p past (p.run past).1.tree x = _
  rw [liftedStep, ite_eq_left ⟨history, size, valid⟩]
  simp [repair]

private theorem lifted_run {reference : Tree} (p : Policy reference) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    (lifted p).runFrom past (p.run past).1.tree xs =
      ((p.runFrom past (p.run past).1 xs).1.tree, (p.runFrom past (p.run past).1 xs).2) := by
  induction xs generalizing past with
  | nil => rfl
  | cons x xs ih =>
    have key := valid x (by simp)
    have extended : ∀ y ∈ past ++ [x], y < reference.size := by
      intro y member
      rcases List.mem_append.mp member with member | member
      · exact history y member
      · simpa only [List.mem_singleton.mp member] using key
    have tail := ih (past ++ [x]) extended (fun y member => valid y (by simp [member]))
    rw [history_step] at tail
    simp only [RotationBST.Algorithm.runFrom, lifted_step p past x history key, Policy.runFrom]
    rw [tail]

/-- Erase Tango's private marks into a causal rotation-model algorithm.
Reconstructing the marked state uses only the past. Starting from an arbitrary
same-size tree costs one reset of at most 2n rotations; subsequent steps exactly
follow the policy. Reconstruction time is outside the abstract BST cost model. -/
theorem Policy.rotation_algorithm {reference : Tree} (p : Policy reference) :
    ∃ a : RotationBST.Algorithm,
      (∀ xs, (∀ x ∈ xs, x < reference.size) →
        a.runFrom [] reference xs = ((p.run xs).1.tree, (p.run xs).2)) ∧
      ∀ saved : Tree, saved.size = reference.size → ∀ xs, (∀ x ∈ xs, x < reference.size) →
        a.totalCost saved xs ≤ xs.length + (p.run xs).2 + 2 * saved.size := by
  refine ⟨lifted p, ?_, ?_⟩
  · intro xs valid
    simpa only [Policy.run, Policy.runFrom, MarkedTree.initial_tree] using
      lifted_run p [] xs (by simp) valid
  · intro saved size xs valid
    cases xs with
    | nil => simp [RotationBST.Algorithm.totalCost, RotationBST.Algorithm.cost, RotationBST.Algorithm.runFrom]
    | cons x xs =>
      have key := valid x (by simp)
      have first : (lifted p).step [] saved x =
          ((p.step [] (p.run []).1 x).1.tree, repair saved reference + (p.step [] (p.run []).1 x).2) := by
        classical
        change liftedStep p [] saved x = _
        rw [liftedStep, ite_eq_left ⟨by simp, size, key⟩]
        simp only [Policy.run, Policy.runFrom, MarkedTree.initial_tree]
      have tail := lifted_run p [x] xs (by simpa using key)
        (fun y member => valid y (by simp [member]))
      have last : (p.run [x]).1 = (p.step [] (p.run []).1 x).1 := history_step p [] x
      rw [last] at tail
      have bound := (repair_spec saved reference size).1
      simp only [RotationBST.Algorithm.totalCost, RotationBST.Algorithm.cost,
        RotationBST.Algorithm.runFrom, first, List.length_cons, List.nil_append]
      rw [tail]
      have sourceCost : (p.run (x :: xs)).2 = (p.step [] (p.run []).1 x).2 +
          (p.runFrom [x] (p.step [] (p.run []).1 x).1 xs).2 := rfl
      rw [sourceCost]
      omega

end RotationBST.Tango
