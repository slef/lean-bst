module

public import RotationBST.Algorithms.Combination.Rounds.Certificates.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Rounds
public import RotationBST.Algorithms.Combination.Controller.Sequences

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates

/-- Every recorded exhausted round starts from its own worker's fixed restart
state and consumes the full round budget, including work before the cut. -/
theorem records_closed {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches)
    (start offset : Nat) (earlier : List Nat) (active : Active worker budget s earlier) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      Worker.ClosedRound worker record.span.side (worker.restart record.span.side) budget record.requests := by
  induction execution generalizing start offset earlier with
  | nil => simp [records]
  | @cons s t x xs cost switches done tail ih =>
    obtain ⟨spent, previous, account⟩ := active
    let first := Controller.attempt worker s.side x s.left s.workerState
    have firstRun := Controller.attempt_run worker s.side x s.left s.workerState
    by_cases firstDone : first.done = true
    · have next : Controller.serve worker budget restore s x =
          ⟨⟨s.side, first.state, first.left⟩, true, false, s.left - first.left⟩ := by
        simpa only [Controller.serve] using ite_eq_left firstDone
      have prefixRun := previous.append (Worker.Requests.cons (firstRun.to_access firstDone) .nil)
      have firstAccount := firstRun.account
      have nextActive : Active worker budget (Controller.serve worker budget restore s x).state (earlier ++ [x]) := by
        refine ⟨spent + (s.left - first.left), ?_, ?_⟩
        · simpa only [next, Nat.add_zero] using prefixRun
        · rw [next]
          dsimp only
          change s.left - first.left + first.left = s.left at firstAccount
          omega
      have rest := ih start (offset + 1) (earlier ++ [x]) nextActive
      simpa only [records, done, next, Bool.false_eq_true, ↓reduceIte] using rest
    · have failed : first.done = false := by cases h : first.done <;> simp_all
      let second := Controller.attempt worker (!s.side) x budget (worker.restart (!s.side))
      have next : Controller.serve worker budget restore s x =
          ⟨⟨!s.side, second.state, second.left⟩, second.done, true,
            s.left - first.left + restore + (budget - second.left)⟩ := by
        simpa only [Controller.serve] using ite_eq_right firstDone
      have secondRun := Controller.attempt_run worker (!s.side) x budget (worker.restart (!s.side))
      have secondDone : second.done = true := by simpa only [next] using done
      have nextActive : Active worker budget (Controller.serve worker budget restore s x).state [x] := by
        refine ⟨budget - second.left, ?_, ?_⟩
        · simpa only [next, Nat.add_zero] using Worker.Requests.cons (secondRun.to_access secondDone) Worker.Requests.nil
        · simpa only [next] using secondRun.account
      have closed := (Worker.ClosedRound.failed firstRun failed).prepend previous
      rw [account] at closed
      have rest := ih offset (offset + 1) [x] nextActive
      intro record member
      simp only [records, next, secondDone, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | member
      · exact closed
      · exact rest record (by simpa only [next] using member)

/-- The initial controller state has an empty certified completed prefix. -/
theorem initial_active {σ : Type} (worker : Controller.Worker σ) (budget : Nat) :
    Active worker budget (Controller.initial worker budget) [] := ⟨0, .nil, by simp [Controller.initial]⟩

end RotationBST.Combo.Rounds.Certificates
