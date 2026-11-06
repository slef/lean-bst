module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Detour
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Abstract
public import RotationBST.Algorithms.Deamortization.Window.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Interruption
open LabelledCursor

/-- An arbitrary source search can be served within one logarithmic window.
The output retains the original pending suffix and charges emitted movements
to the original prefix actually consumed, not to the whole planned search. -/
theorem search_window {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c final : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {target budget : Nat}
    (targetValid : target < s.pair.tree.size) (search : Requests.Serves c ops target final)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget) :
    ∃ (out : Output α) (consumed : Nat) (middle visited : Pointer.Config)
      (before after : List Multifinger.Opcode),
      run p c s ops = some out ∧ out.source = final ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      consumed ≤ budget ∧ consumed ≤ out.instructions.length ∧
      Multifinger.replay (out.instructions.take consumed) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop consumed) middle = some ⟨out.state.pair.tree, []⟩ ∧
      Multifinger.replay before ⟨s.pair.tree, []⟩ = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some middle ∧
      before.length + after.length ≤ 5 * consumed ∧
      1 + before.length + after.length ≤ 1 + 5 * budget ∧
      (consumed = budget ∨ middle.key? = some target) := by
  obtain ⟨out, completed, source, _, replay, amortized, _, visits⟩ :=
    Requests.Results.serves_recorded bounded.1 valid search
  have height : ∀ cut middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle →
      ∀ x < middle.tree.size, Tree.depth middle.tree x ≤ budget := by
    intro cut middle first x hx
    obtain ⟨actual, actualReplay, _, depths⟩ := run_uniform_prefix bounded valid completed cut
    have same : actual = middle := Option.some.inj (actualReplay.symm.trans first)
    subst actual
    have size : s.pair.tree.size = middle.tree.size := by
      obtain ⟨_, _, rotations⟩ := (Multifinger.Replay.Results.physical first).rotations
      exact rotations.size_eq
    have bound := (depths x (by rw [size]; exact hx)).trans budgetBound
    exact_mod_cast bound
  obtain ⟨consumed, middle, visited, before, after, certificates⟩ :=
    Deamortization.Window.Results.serve replay (by simp [Pair.tree]) targetValid visits height
  exact ⟨out, consumed, middle, visited, before, after, completed, source, amortized, certificates⟩

end RotationBST.HeavyPath.Finger.History.Simulation.Interruption
