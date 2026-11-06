module

public import RotationBST.Algorithms.Combination.Online.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Refinement.Visits.Comparison
public import RotationBST.Structures.FingerHand.Packed.Simulation.Execution

@[expose] public section
namespace RotationBST.Combo.Online

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget restore : Nat}

theorem completes (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : (Controller.serve worker budget restore s.controller x).done = true :=
  Controller.serve_done worker saved.size budget budget restore contract.fresh (Nat.le_refl _) s.controller x valid

theorem transition_exists (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : ∃ result, Transition restore s x result := by
  obtain ⟨final, events, sharedCost, visit, represented, boundary, reads, charged, positive⟩ :=
    Refinement.Visits.service model contract.correct (Controller.serve_service worker budget restore s.controller x)
      (completes contract s x valid) s.boundary valid contract.paid data contract.stored s.actual s.represented
  obtain ⟨pointerCost, served, pointerBound⟩ := visit.erase data s.represented.2.1
  obtain ⟨hand, cost, handRep, physical, amortized⟩ :=
    FingerHand.Hand.simulate_serves s.handRep s.represented.2.1.2.2 served
  let next : State model data budget :=
    ⟨(Controller.serve worker budget restore s.controller x).state, final, hand, represented, boundary, handRep,
      Controller.serve_left worker budget restore s.controller x s.left_le⟩
  refine ⟨(next, cost), rfl, physical, ?_, events, sharedCost, visit, reads, charged⟩
  change cost + hand.potential ≤ _
  norm_num at amortized
  omega

end RotationBST.Combo.Online
