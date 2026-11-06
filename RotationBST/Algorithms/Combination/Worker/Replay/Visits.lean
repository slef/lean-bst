module

public import RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

variable {σ : Type} {saved : Tree} (planner : Planner σ saved)

theorem seen_running (side : Bool) (x : Nat) (next : σ) (current : Pointer.Config) (ops : List Opcode)
    (visited : Visits x ops current) :
    Refinement.Visits.Seen (model planner) side x (ops.length + 1) (.running next current ops) := by
  induction ops generalizing current with
  | nil =>
    obtain ⟨before, after, atKey, split, ran, key⟩ := visited
    have empty : before = [] := (List.append_eq_nil_iff.mp split.symm).1
    subst before
    have same := Option.some.inj ran
    subst atKey
    exact Or.inl key
  | cons op ops ih =>
    obtain ⟨before, after, atKey, split, ran, key⟩ := visited
    cases before with
    | nil =>
      have same := Option.some.inj ran
      subst atKey
      exact Or.inl key
    | cons first before =>
      obtain ⟨rfl, rest⟩ := List.cons.inj split
      obtain ⟨moved, firstStep, restRun⟩ := Option.bind_eq_some_iff.mp ran
      have tail := ih moved ⟨before, after, atKey, rest, restRun, key⟩
      apply Or.inr
      simpa only [worker, step, firstStep, List.length_cons] using tail

theorem seen_access (side : Bool) (state : σ) (x : Nat)
    (size : (planner.tree side state).size = saved.size) (valid : x < saved.size) :
    Refinement.Visits.Seen (model planner) side x ((planner.plan side state x).2.length + 2) (.boundary state) := by
  exact Or.inr (seen_running planner side x _ _ _ (planner.visits side state x size valid))

theorem correct : Refinement.Visits.Correct (model planner) := by
  intro side state x final work boundary valid ran
  obtain ⟨original, rfl, size⟩ := request_boundary planner boundary
  have canonical := access planner side original x size valid
  obtain ⟨_, sameCost⟩ := Worker.Results.completed_unique ran rfl canonical rfl
  rw [sameCost]
  exact seen_access planner side original x size valid

end RotationBST.Combo.Worker.Replay
