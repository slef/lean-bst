module

public import RotationBST.Structures.TreeBuffer.Nodes.Initialization.Traversal
public import RotationBST.Structures.TreeBuffer.Nodes.Layout
public import RotationBST.Models.Labelled.Intervals.Initialization.Population

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes.Initialization
open LabelledCursor

theorem raw_payload {α : Type} (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α)
    (tree : Tree) (lo : Nat) : (raw fields data tree lo).map Entry.payload = Metadata.label data tree lo := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [raw, LabelledTree.map, Entry.payload, Metadata.label, il, ir]

theorem raw_erase {α : Type} (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α)
    (tree : Tree) (lo : Nat) : (raw fields data tree lo).erase = tree := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [raw, LabelledTree.erase, il, ir]

theorem tick_positive {α : Type} {s t : State α} {cost : Nat} (transition : tick s = some (cost, t)) :
    1 ≤ cost := by
  unfold tick at transition
  split at transition <;> simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals omega

/-- Every executed step preserves the entire key/cell projection, including
ancestors and siblings. This does not require initialized routing fields. -/
theorem tick_payload {α : Type} {s t : State α} {cost : Nat} (transition : tick s = some (cost, t)) :
    t.cursor.tree.map Entry.payload = s.cursor.tree.map Entry.payload := by
  rcases s with ⟨⟨focus, cs⟩, pending, mode⟩
  unfold tick at transition
  split at transition <;> simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals obtain ⟨rfl, rfl⟩ := transition
  all_goals simp only [Config.tree, plug, map_plug, LabelledTree.map, Entry.payload]

theorem Run.payload {α : Type} {s t : State α} {cost : Nat} (run : Run s t cost) :
    t.cursor.tree.map Entry.payload = s.cursor.tree.map Entry.payload := by
  induction run with
  | refl => rfl
  | step first _ ih => exact ih.trans (tick_payload first)

theorem Run.loop {α : Type} {s t : State α} {cost : Nat} (run : Run s t cost) (halt : tick t = none)
    (fuel : Nat) (enough : cost ≤ fuel) (spent : Nat) : runLoop fuel spent s = some (spent + cost, t) := by
  induction run generalizing fuel spent with
  | refl => cases fuel <;> simp only [runLoop, halt, Nat.add_zero]
  | @step s t u charge rest first tail ih =>
    have positive := tick_positive first
    cases fuel with
    | zero => omega
    | succ fuel => simpa only [runLoop, first, Nat.add_assoc] using ih halt fuel (by omega) (spent + charge)

theorem Run.execute {α : Type} {s t : State α} {cost : Nat} (run : Run s t cost) (halt : tick t = none)
    (fuel : Nat) (enough : cost ≤ fuel) : runFuel fuel s = some (cost, t) := by
  simpa only [runFuel, Nat.zero_add] using run.loop halt fuel enough 0

theorem Run.prefix_cost {α : Type} {s t : State α} {cost : Nat} (completeRun : Run s t cost) (halt : tick t = none)
    {u : State α} {prefixCost : Nat} (prefixRun : Run s u prefixCost) : prefixCost ≤ cost := by
  induction prefixRun generalizing t cost with
  | refl => exact Nat.zero_le _
  | step first _ ih =>
    cases completeRun with
    | refl => rw [halt] at first; contradiction
    | step next tail =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj (first.symm.trans next)
      have bound := ih tail halt
      omega

/-- Actual combined-node initialization, including the empty tree. The given
universe size is a scalar input; no recursive size calculation is executed. -/
theorem complete {α : Type} (tree : Tree) (n : Nat) (size : n = tree.size)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α) :
    ∃ final cost, runFuel (8 * n) (initial (raw fields data tree 0) n) = some (cost, final) ∧
      Run (initial (raw fields data tree 0) n) final cost ∧ tick final = none ∧
      final.cursor = ⟨label data tree 0, []⟩ ∧ cost = IntervalMetadata.Initialization.work tree ∧ cost ≤ 8 * n := by
  subst n
  have run : ∃ final, Run (initial (raw fields data tree 0) tree.size) final
      (IntervalMetadata.Initialization.work tree) ∧ tick final = none ∧ final.cursor = ⟨label data tree 0, []⟩ := by
    by_cases empty : tree = .nil
    · subst tree
      exact ⟨initial .nil 0, .refl, rfl, rfl⟩
    · obtain ⟨pending, run⟩ := traversal tree empty fields data 0 []
      refine ⟨⟨⟨label data tree 0, []⟩, pending, .up⟩, ?_, ?_, rfl⟩
      · simpa only [initial, Nat.zero_add] using run
      · cases tree <;> rfl
  obtain ⟨final, run, halt, cursor⟩ := run
  have bound := IntervalMetadata.Initialization.work_bound tree
  exact ⟨final, _, run.execute halt _ bound, run, halt, cursor, rfl, bound⟩

theorem prefix_work {α : Type} (tree : Tree) (n : Nat) (size : n = tree.size)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α) {final : State α} {cost : Nat}
    (run : Run (initial (raw fields data tree 0) n) final cost) : cost ≤ 8 * n := by
  obtain ⟨_, _, _, completed, halt, _, _, bound⟩ := complete tree n size fields data
  exact le_trans (completed.prefix_cost halt run) bound

end RotationBST.TreeBuffer.Nodes.Initialization
