import CostComposition

/-! A precise interface for the periodic-probe route. Existence of a probe with
this property is NOT assumed as an axiom or proved in this file. -/
namespace RotationBST

def repeatWord (xs : List Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => xs ++ repeatWord xs m

theorem treeOnly_repeat_endpoint (b : TreeAlgorithm) (s : Tree) (xs : List Nat)
    (h : (b.runFrom () s xs).2.1 = s) (m : Nat) :
    (b.runFrom () s (repeatWord xs m)).2.1 = s := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [repeatWord, StatefulAlgorithm.runFrom_append]
      have hq : (b.runFrom () s xs).1 = () := Subsingleton.elim _ _
      simpa only [hq, h] using ih

theorem treeOnly_repeat_cost (b : TreeAlgorithm) (s : Tree) (xs : List Nat)
    (h : (b.runFrom () s xs).2.1 = s) (m : Nat) :
    b.totalCost s (repeatWord xs m) = m * b.totalCost s xs := by
  induction m with
  | zero => simp [repeatWord, treeOnly_cost_eq, StatefulAlgorithm.runFrom]
  | succ m ih =>
      simp only [repeatWord, treeOnly_cost_append, h, ih, Nat.succ_mul]
      omega

theorem Execution.repeat (h : Execution t xs t k) (m : Nat) :
    Execution t (repeatWord xs m) t (m * k) := by
  induction m with
  | zero => simpa [repeatWord] using (Execution.nil (t := t))
  | succ m ih => simpa [repeatWord, Nat.succ_mul, Nat.add_comm] using h.append ih

/-- On every ultimately periodic input admitting a periodic serving schedule,
a probe eventually matches that schedule's average cost. The constant may
depend on the prefix, period, initial tree and schedule, but not repetitions. -/
def PeriodicProbe (a : StatefulAlgorithm σ) : Prop :=
  ∀ T pre t j word k,
    Execution T pre t j → Execution t word t k →
    ∃ K, ∀ m, a.totalCost T (pre ++ repeatWord word m) ≤
      m * (word.length + k) + K

/-- Dominating a periodic probe forbids a positive-cost repeated product loop.
The simulator must return to its own tree, and the offline execution to its
own tree; these two loop trees need not coincide. -/
theorem probe_forbids_positive_loop (a : StatefulAlgorithm σ) (hp : PeriodicProbe a)
    (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (dom : ∀ T xs, ValidInput T xs → b.totalCost T xs ≤ C * a.totalCost T xs + f T.size)
    (T : Tree) (pre word : List Nat) (t : Tree) (j k : Nat)
    (hpre : Execution T pre t j) (hloop : Execution t word t k)
    (hbloop : (b.runFrom () (b.runFrom () T pre).2.1 word).2.1 =
      (b.runFrom () T pre).2.1) :
    b.totalCost (b.runFrom () T pre).2.1 word ≤ C * (word.length + k) := by
  obtain ⟨K, hK⟩ := hp T pre t j word k hpre hloop
  apply Classical.byContradiction
  intro hn
  let m := C * K + f T.size + 1
  have hv := (hpre.append (hloop.repeat m)).validInput
  have hd := dom T (pre ++ repeatWord word m) hv
  have hu := Nat.mul_le_mul_left C (hK m)
  rw [treeOnly_cost_append, treeOnly_repeat_cost b _ word hbloop m] at hd
  have hg : C * (word.length + k) + 1 ≤
      b.totalCost (b.runFrom () T pre).2.1 word := by omega
  have hm := Nat.mul_le_mul_left m hg
  rw [Nat.mul_add, Nat.mul_one] at hm
  rw [Nat.mul_add, Nat.mul_left_comm C m] at hu
  dsimp [m] at *
  omega

/-- info: 'RotationBST.probe_forbids_positive_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms probe_forbids_positive_loop
end RotationBST
