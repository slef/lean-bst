module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Abstract
public import RotationBST.Bounds.StaticTree.Trace.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Interruption
open LabelledCursor

/-- One actual response retains both cost guarantees, its exact replay, and
weighted depth bounds at every physical interruption. The population term is
explicit; this is not the sharp weighted theorem of the paper. -/
theorem response {α : Type} {weight : α → ℝ} {p : Policy α}
    (bounded : PolicyBounded weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) :
    ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
        Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
        ∀ rank : Fin c.tree.inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            49 + 15 * Real.logb 2 (HeavyPath.mass weight c.tree /
              weight (c.tree.inorder[rank.val]'rank.isLt)) +
                24 * Real.logb 2 s.pair.tree.size := by
  have spec := bounded.1 c s op valid
  cases legal : perform op c with
  | none => simp only [legal] at spec; rw [spec] at responded; cases responded
  | some next =>
    rw [legal] at spec
    obtain ⟨actual, executed, _, preserved, replay, amortized⟩ := spec
    have same : actual = out := Option.some.inj (executed.symm.trans responded)
    subst actual
    have worst := bounded.2 c s op out valid responded
    refine ⟨preserved, replay, amortized, worst, ?_⟩
    intro cut
    obtain ⟨middle, first, last, drift⟩ :=
      StaticTree.Trace.Results.replay_prefix_bound replay worst cut
    refine ⟨middle, first, last, ?_⟩
    intro rank
    have start := Simulation.Results.depth valid rank
    have bound := drift rank.val
    change (Tree.depth middle.tree rank.val : ℝ) ≤
      Tree.depth s.pair.tree rank.val + (34 + 24 * Real.logb 2 s.pair.tree.size) at bound
    linarith

private theorem size_eq {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : s.pair.tree.size = c.tree.erase.size := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim valid
  | node l key r => exact History.Results.state_size valid

/-- Unit weights give a logarithmic bound for every key at every physical
interruption, including cuts after the end of a response. -/
theorem response_uniform {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < s.pair.tree.size,
        (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨_, _, _, _, prefixes⟩ := response bounded valid responded
  obtain ⟨middle, first, last, depths⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro x hx
  have key : x < c.tree.inorder.length := by
    rw [Representation.Bridge.inorder_length, ← size_eq valid]
    exact hx
  have bound := depths ⟨x, key⟩
  simp only [HeavyPath.Results.unit_mass, div_one, ← size_eq valid] at bound
  change (Tree.depth middle.tree x : ℝ) ≤
    49 + 15 * Real.logb 2 s.pair.tree.size + 24 * Real.logb 2 s.pair.tree.size at bound
  linarith

/-- The uniform depth guarantee covers every physical prefix of an entire
successful stream under one fixed policy, independently of stream length.
Initialization precedes the stream and is not included in this guarantee. -/
theorem run_uniform_prefix {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < s.pair.tree.size,
        (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 s.pair.tree.size := by
  induction ops generalizing c s out cut with
  | nil =>
    simp only [run, Option.some.injEq] at completed
    subst out
    refine ⟨⟨s.pair.tree, []⟩, by simp [Multifinger.replay], by simp [Multifinger.replay], ?_⟩
    intro x hx
    have key : x < c.tree.inorder.length := by
      rw [Representation.Bridge.inorder_length, ← size_eq valid]
      exact hx
    have depth := Simulation.Results.depth valid ⟨x, key⟩
    simp only [HeavyPath.Results.unit_mass, div_one, ← size_eq valid] at depth
    have logarithm : 0 ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_nonneg (by norm_num)
      have population : 1 ≤ s.pair.tree.size := by
        simp only [Pair.tree, Tree.size]
        omega
      exact_mod_cast population
    change (Tree.depth s.pair.tree x : ℝ) ≤ _
    change (Tree.depth s.pair.tree x : ℝ) ≤ 15 + 15 * Real.logb 2 s.pair.tree.size at depth
    linarith
  | cons op ops ih =>
    cases firstEq : p c s op with
    | none => simp [run, firstEq] at completed
    | some first =>
      simp only [run, firstEq, Option.bind_some] at completed
      cases lastEq : run p first.source first.state ops with
      | none => simp [lastEq] at completed
      | some last =>
        simp only [lastEq, Option.map_some, Option.some.injEq] at completed
        subst out
        obtain ⟨preserved, replay, _, _, _⟩ := response bounded valid firstEq
        have sameSize : s.pair.tree.size = first.state.pair.tree.size := by
          obtain ⟨_, _, rotations⟩ := (Multifinger.Replay.Results.physical replay).rotations
          exact rotations.size_eq
        by_cases early : cut ≤ first.instructions.length
        · obtain ⟨middle, beginning, ending, depths⟩ := response_uniform bounded valid firstEq cut
          obtain ⟨start, empty, suffix, _⟩ := ih preserved lastEq 0
          simp only [List.take_zero, Multifinger.replay, Option.some.injEq] at empty
          subst start
          simp only [List.drop_zero] at suffix
          refine ⟨middle, ?_, ?_, depths⟩
          · simpa only [List.take_append_of_le_length early] using beginning
          · simpa only [List.drop_append_of_le_length early, Multifinger.replay_append,
              ending, Option.bind_some] using suffix
        · obtain ⟨middle, beginning, ending, depths⟩ :=
            ih preserved lastEq (cut - first.instructions.length)
          have enough : first.instructions.length ≤ cut := by omega
          refine ⟨middle, ?_, ?_, ?_⟩
          · simpa only [List.take_append, List.take_of_length_le enough,
              Multifinger.replay_append, replay, Option.bind_some] using beginning
          · simpa only [List.drop_append, List.drop_eq_nil_of_le enough, List.nil_append] using ending
          · simpa only [sameSize] using depths

end RotationBST.HeavyPath.Finger.History.Simulation.Interruption
