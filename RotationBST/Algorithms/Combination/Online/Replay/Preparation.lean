module

public import RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Online.Abstract
public import RotationBST.Algorithms.Combination.Worker.Replay.Abstract
public import RotationBST.Structures.FingerHand.Packed.Invariant

@[expose] public section
namespace RotationBST.Combo.Online.Replay

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
  (p : Prepared model budget restore fields oldData)

theorem current_size (s : Option (Online.State model p.data budget)) : (p.current s).size = saved.size := by
  cases s with
  | none => rfl
  | some s =>
    exact s.handRep.size.trans ((congrArg Tree.size s.represented.2.2.1).trans
      (model.size _ _ s.represented.1))

theorem access_serves (s : Option (Online.State model p.data budget)) (x : Nat) (valid : x < saved.size) :
    Pointer.Serves (p.current s) (p.current (access p s x).1) x (access p s x).2 := by
  obtain ⟨_, _, _, _, physical, _⟩ := Online.Results.execute_from p s [x]
    (by intro y member; simpa using (List.mem_singleton.mp member ▸ valid))
  simp only [execute, Nat.add_zero] at physical
  have singleton : ∀ {a b : Tree} {key cost : Nat}, Pointer.Execution a [key] b cost → Pointer.Serves a b key cost := by
    intro a b key cost ran
    cases ran with
    | cons first rest => cases rest; simpa only [Nat.add_zero] using first
  exact singleton physical

theorem implementation_exists : Nonempty (Implementation p) := by
  obtain ⟨planner, initial, tree, expansion⟩ := Worker.Replay.Results.planner_exists
    (fun _ => none) (fun _ => p.current) (fun _ => access p) (fun _ => rfl)
    (fun _ state x _ valid => access_serves p state x valid)
  exact ⟨⟨planner, initial, tree, fun side state x valid => expansion side state x (current_size p state) valid⟩⟩

theorem source_run (side : Bool) (s : Option (Online.State model p.data budget)) (xs : List Nat) :
    Worker.Replay.policyRun (fun _ => access p) side s xs = execute p s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [Worker.Replay.policyRun, execute, ih]

theorem run_bound (implementation : Implementation p) (side : Bool)
    (s : Option (Online.State model p.data budget)) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    (Worker.Replay.run implementation.planner side s xs).1 = (execute p s xs).1 ∧
      (Worker.Replay.run implementation.planner side s xs).2 ≤ 2 * (execute p s xs).2 := by
  have compared := Worker.Replay.Results.run_bound implementation.planner (fun _ => access p)
    (fun side state x _ key => implementation.expansion side state x key) side s xs
    (by rw [implementation.tree]; exact current_size p s) valid
  simpa only [source_run] using compared

theorem requests (implementation : Implementation p) (side : Bool) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ cost, Worker.Requests (Worker.Replay.worker implementation.planner) side
      ((Worker.Replay.worker implementation.planner).restart side) xs
      (.boundary (execute p none xs).1) cost ∧ cost ≤ 2 * (execute p none xs).2 := by
  have ran := Worker.Replay.Results.requests implementation.planner side none xs
    (by rw [implementation.tree]; rfl) valid
  obtain ⟨same, bound⟩ := run_bound p implementation side none xs valid
  rw [same] at ran
  exact ⟨_, by simpa only [Worker.Replay.worker, implementation.initial] using ran, bound⟩

end RotationBST.Combo.Online.Replay
