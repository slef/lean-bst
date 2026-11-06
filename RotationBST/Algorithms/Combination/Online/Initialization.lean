module

public import RotationBST.Algorithms.Combination.Online.Startup.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Online.Step
public import RotationBST.Structures.TreeBuffer.Snapshot.Startup.Erasure

@[expose] public section
namespace RotationBST.Combo.Online
open TreeBuffer

theorem prepared_nonempty {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    (budget restore : Nat) (fresh : Controller.FreshBound worker saved.size budget)
    (paid : 841 * saved.size ≤ 15 * restore) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    Nonempty (Prepared model budget restore fields oldData) := by
  obtain ⟨ready, data, events, saveCost, setup, valid, stored, shape, atRoot, saveBound⟩ :=
    Snapshot.Startup.save saved saved.size rfl nonempty fields oldData
  have represented : Refinement.Represents model data ready false (worker.restart false) :=
    ⟨model.restart_ready false, valid,
      by simpa only [model.restart_cursor, Pointer.Config.tree, Pointer.plug] using shape,
      by simpa only [model.restart_cursor] using atRoot⟩
  have positive : 0 < saved.size := by cases saved <;> simp_all [Tree.size]
  obtain ⟨touches, erased, traceBound⟩ := setup.erase rfl nonempty
  obtain ⟨hand, cost, handRep, trace, bound⟩ := FingerHand.Hand.simulate_trace
    (FingerHand.Hand.forState_represents _) (Multifinger.initial_valid 2 saved positive) erased
  have initial := FingerHand.Hand.initial_tree 2 saved
  rw [initial.1] at trace
  rw [initial.2] at bound
  let state : State model data budget :=
    ⟨Controller.initial worker budget, ready, hand, represented,
      Refinement.Visits.boundary_restart worker saved.size false, handRep, Nat.le_refl _⟩
  refine ⟨⟨data, ⟨correct, stored, paid, fresh⟩, state, rfl, events, saveCost, setup, saveBound, cost, trace, ?_⟩⟩
  norm_num at bound
  change cost + hand.potential ≤ _
  omega

end RotationBST.Combo.Online
