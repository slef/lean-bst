module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Proofs
public import RotationBST.Models.Labelled.Cursor.Map.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Interruption
open LabelledCursor

/-- The chosen structural policy gives a purely weighted depth bound throughout
one response, with all cost and replay guarantees for that same opcode list. -/
theorem response_weighted {α : Type} {weight : α → ℝ} {p : Policy α}
    (certified : PolicyWithin weight p) {c : Config α} {s : State α}
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
            336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
              weight (c.tree.inorder[rank.val]'rank.isLt)) := by
  obtain ⟨preserved, replay, amortized, worst, _⟩ := response certified.1 valid responded
  refine ⟨preserved, replay, amortized, worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, depths⟩ := certified.2 c s op out valid responded cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have original := Simulation.Results.depth valid rank
  have structural : (Tree.depth middle.tree rank.val : ℝ) ≤
      16 * Tree.depth s.pair.tree rank.val + 96 := by exact_mod_cast depths rank.val
  linarith

private theorem mass_inorder {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    HeavyPath.mass weight t = (t.inorder.map weight).sum := by
  induction t with
  | nil => rfl
  | node l x r il ir =>
    simp only [HeavyPath.mass, LabelledTree.inorder, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, il, ir]
    ring

private theorem response_inorder {α : Type} {weight : α → ℝ} {p : Policy α}
    (bounded : PolicyBounded weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) : c.tree.inorder = out.source.tree.inorder := by
  have spec := bounded.1 c s op valid
  cases legal : perform op c with
  | none => simp only [legal] at spec; rw [spec] at responded; cases responded
  | some next =>
    rw [legal] at spec
    obtain ⟨actual, executed, source, _⟩ := spec
    have same : actual = out := Option.some.inj (executed.symm.trans responded)
    subst actual
    rw [← source] at legal
    exact perform_inorder legal

/-- Every physical prefix of the entire simulated stream has weighted depth
independent of the population and stream length. Re-established source-boundary
layouts prevent the affine per-response factor from accumulating. -/
theorem run_weighted_prefix {α : Type} {weight : α → ℝ} {p : Policy α}
    (certified : PolicyWithin weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ rank : Fin c.tree.inorder.length,
        (Tree.depth middle.tree rank.val : ℝ) ≤
          336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
            weight (c.tree.inorder[rank.val]'rank.isLt)) := by
  induction ops generalizing c s out cut with
  | nil =>
    simp only [run, Option.some.injEq] at completed
    subst out
    refine ⟨⟨s.pair.tree, []⟩, by simp [Multifinger.replay], by simp [Multifinger.replay], ?_⟩
    intro rank
    have original := Simulation.Results.depth valid rank
    have nonnegative : (0 : ℝ) ≤ Tree.depth s.pair.tree rank.val := Nat.cast_nonneg _
    change (Tree.depth s.pair.tree rank.val : ℝ) ≤ _
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
        obtain ⟨preserved, replay, _, _, prefixes⟩ := response_weighted certified valid firstEq
        by_cases early : cut ≤ first.instructions.length
        · obtain ⟨middle, beginning, ending, depths⟩ := prefixes cut
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
          · have order := response_inorder certified.1 valid firstEq
            have mass : HeavyPath.mass weight first.source.tree = HeavyPath.mass weight c.tree := by
              rw [mass_inorder, mass_inorder, order]
            intro rank
            have key : rank.val < first.source.tree.inorder.length := by rw [← order]; exact rank.isLt
            have bound := depths ⟨rank.val, key⟩
            simpa only [mass, ← order] using bound

end RotationBST.HeavyPath.Finger.History.Simulation.Interruption
