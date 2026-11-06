module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Flatten
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Abstract
public import RotationBST.Models.Pointer.Reshape
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Weighted
open HeavyPath.Finger.History

/-- Weighted bounded-depth simulation with one initial representation and
causal policy chosen before every source algorithm and request sequence.
Original-tree reshaping is charged separately from the multiplicative bound. -/
theorem simulation {α : Type} (weight : α → ℝ) (c : LabelledCursor.Config α)
    (live : c.focus ≠ .nil) (positive : HeavyPath.Positive weight c.tree) :
    ∃ (p : Simulation.Policy α) (start : State α) (startup : Nat),
      Simulation.PolicyWithin weight p ∧ Simulation.ConfigValid weight c start ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨start.pair.tree, []⟩ startup ∧
      startup ≤ 16 * c.tree.erase.size ∧
      ∀ (a : Simulation.Requests.Algorithm α) (past keys : List Nat),
        (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, Simulation.Requests.run p a past c start keys = some out ∧
          out.source = (a.runFrom past c keys).2 ∧
          Simulation.ConfigValid weight out.source out.state ∧
          Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          out.cost ≤ 248 * (a.runFrom past c keys).1.length ∧
          (Pointer.Config.mk out.state.pair.tree []).key? = out.source.erase.key? ∧
          ∀ cut, ∃ middle,
            Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
            Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
            ∀ rank : Fin c.tree.inorder.length,
              (Tree.depth middle.tree rank.val : ℝ) ≤
                336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
                  weight (c.tree.inorder[rank.val]'rank.isLt)) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim (live rfl)
  | node l key r =>
    obtain ⟨canonical, canonicalValid, _⟩ := Results.build_state positive
    obtain ⟨start, valid, minimum⟩ := Simulation.Minimum.Results.attained
      (c := ⟨.node l key r, cs⟩) canonicalValid
    have zero : Simulation.Minimum.excess weight ⟨.node l key r, cs⟩ start = 0 := by
      simp only [Simulation.Minimum.excess, minimum, Nat.sub_self]
    have size : start.pair.tree.size = (LabelledCursor.Config.mk (.node l key r) cs).tree.erase.size :=
      Results.state_size valid
    obtain ⟨startup, startupBound, startupTrace⟩ := Pointer.reshape
      (LabelledCursor.Config.mk (.node l key r) cs).tree.erase start.pair.tree size.symm
    obtain ⟨p, certified⟩ := Simulation.Results.policy_within_exists weight
    refine ⟨p, start, startup, certified, valid, startupTrace, startupBound, ?_⟩
    intro a past keys validKeys
    obtain ⟨out, completed, source, preserved, replay, execution, _⟩ :=
      Simulation.Requests.Results.run_spec certified.1.1 a past valid keys validKeys
    obtain ⟨physical, legal⟩ := Simulation.Requests.flatten certified.1.1 a past valid keys validKeys completed
    have work := Simulation.Minimum.Results.run_excess certified.1.1 valid legal physical
    rw [zero] at work
    refine ⟨out, completed, source, preserved, replay, execution, by omega,
      Simulation.Results.root_key preserved, ?_⟩
    exact Simulation.Interruption.Results.run_weighted_prefix certified valid physical

/-- Keeping the source algorithm fixed gives literal physical-code prefix
preservation, including searches with no instructions and post-visit work. -/
theorem online_prefix {α : Type} (p : Simulation.Policy α)
    (a : Simulation.Requests.Algorithm α) (past : List Nat) (c : LabelledCursor.Config α)
    (start : State α) (xs ys : List Nat) {out : Simulation.Output α}
    (completed : Simulation.Requests.run p a past c start (xs ++ ys) = some out) :
    ∃ first, Simulation.Requests.run p a past c start xs = some first ∧
      first.instructions <+: out.instructions :=
  Simulation.Requests.Results.run_prefix p a past c start xs ys completed

/-- The abstract weighted simulation theorem for an offline family of source
algorithms. A constant family has the online physical-prefix property. -/
theorem transform {α : Type} (family : List Nat → Simulation.Requests.Algorithm α)
    (weight : α → ℝ) (c : LabelledCursor.Config α) (live : c.focus ≠ .nil)
    (positive : HeavyPath.Positive weight c.tree) :
    ∃ (program : List Nat → Option (Simulation.Output α)) (start : State α) (startup : Nat),
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨start.pair.tree, []⟩ startup ∧
      startup ≤ 16 * c.tree.erase.size ∧
      (∀ keys, (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, program keys = some out ∧
          out.source = ((family keys).runFrom [] c keys).2 ∧
          Simulation.ConfigValid weight out.source out.state ∧
          Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          out.cost ≤ 248 * ((family keys).runFrom [] c keys).1.length ∧
          (Pointer.Config.mk out.state.pair.tree []).key? = out.source.erase.key? ∧
          ∀ cut, ∃ middle,
            Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
            Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
            ∀ rank : Fin c.tree.inorder.length,
              (Tree.depth middle.tree rank.val : ℝ) ≤
                336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
                  weight (c.tree.inorder[rank.val]'rank.isLt))) ∧
      ((∃ a, ∀ keys, family keys = a) →
        ∀ xs ys out, program (xs ++ ys) = some out →
          ∃ first, program xs = some first ∧ first.instructions <+: out.instructions) := by
  obtain ⟨p, start, startup, _, _, trace, startupBound, execute⟩ := simulation weight c live positive
  refine ⟨fun keys => Simulation.Requests.run p (family keys) [] c start keys,
    start, startup, trace, startupBound, ?_, ?_⟩
  · intro keys validKeys
    exact execute (family keys) [] keys validKeys
  · rintro ⟨a, fixed⟩ xs ys out completed
    simp only [fixed] at completed ⊢
    exact online_prefix p a [] c start xs ys completed

end RotationBST.Deamortization.Weighted
