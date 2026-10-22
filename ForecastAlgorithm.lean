import PeriodicCandidates
import AdditiveNormalization

/-! A legal stateful online BST rule that selects a forecast from observed
history and synchronizes with its preselected clairvoyant plan. -/
namespace RotationBST
namespace ForecastAlgorithm
open InfinitePlanning PeriodicCandidates

theorem plan_size (p : Plan word initial) (i : Nat) : (p.tree i).size = initial.size :=
  (p.execution i).size_eq.symm

noncomputable def repair (s t : Tree) (h : s.size = t.size) : Nat := by
  classical
  exact if s=t then 0 else Classical.choose (reset_linear s t h)

theorem repair_spec (s t : Tree) (h : s.size = t.size) :
    Rotations s t (repair s t h) ∧ repair s t h ≤ 2*s.size := by
  classical
  by_cases he : s=t
  · subst t
    simp only [repair,ite_true]
    exact ⟨.refl,by omega⟩
  · simp only [repair,if_neg he]
    exact ⟨(Classical.choose_spec (reset_linear s t h)).2,
      (Classical.choose_spec (reset_linear s t h)).1⟩

theorem repair_same (s : Tree) (h : s.size = s.size) : repair s s h = 0 := by
  simp [repair]

noncomputable def candidatePlan (n : Nat) (hn : 0<n) (p : Candidate) (hp : Valid n p) :
    Plan (forecast p) (spine n .nil) :=
  known_future_plan (forecast p) (spine n .nil)
    (fun i => by simpa [spine_size,Tree.size] using forecast_valid p hn hp i)

def Ready (history : List Nat) (s : Tree) (x : Nat) : Prop :=
  0<s.size ∧ ∀ y ∈ history ++ [x], y<s.size

theorem selected_valid (history : List Nat) (hv : ∀ y ∈ history, y<n) :
    Valid n (selected history hv).value :=
  covers_valid (List.mem_iff_getElem?.mpr ⟨_,(selected history hv).at_index⟩)

theorem selected_current (history : List Nat) (x : Nat)
    (hv : ∀ y ∈ history ++ [x], y<n) :
    forecast (selected (history++[x]) hv).value history.length = x := by
  have h := (selected (history++[x]) hv).consistent history.length (by simp)
  simpa [atRank] using h

noncomputable def planned (history : List Nat) (s : Tree) (x : Nat)
    (h : Ready history s x) : Tree × Nat :=
  let p := candidatePlan s.size h.1 (selected (history++[x]) h.2).value
    (selected_valid (history++[x]) h.2)
  let hs : s.size = (p.tree history.length).size := by
    rw [plan_size,spine_size,Tree.size,Nat.add_zero]
  (p.tree (history.length+1), repair s (p.tree history.length) hs + p.rotations history.length)

theorem planned_correct (history : List Nat) (s : Tree) (x : Nat)
    (h : Ready history s x) : Access s (planned history s x h).1 x (planned history s x h).2 := by
  let p := candidatePlan s.size h.1 (selected (history++[x]) h.2).value
    (selected_valid (history++[x]) h.2)
  have hs : s.size = (p.tree history.length).size := by
    rw [plan_size,spine_size,Tree.size,Nat.add_zero]
  have ha := p.access history.length
  have hx := selected_current history x h.2
  change forecast (selected (history++[x]) h.2).value history.length = x at hx
  rw [hx] at ha
  exact ⟨((repair_spec s (p.tree history.length) hs).1).append ha.1,ha.2⟩

noncomputable def algorithm : StatefulAlgorithm (List Nat) := by
  classical
  exact {
    init := fun _ => []
    step := fun history s x => (history++[x], if h : Ready history s x then
      planned history s x h else moveToRoot s x)
    correct := by
      intro history s x hx
      split
      next h => exact planned_correct history s x h
      next => exact (moveToRoot_correct s x hx).1
  }

theorem step_history (history : List Nat) (s : Tree) (x : Nat) :
    (algorithm.step history s x).1 = history++[x] := rfl

theorem step_planned (history : List Nat) (s : Tree) (x : Nat) (h : Ready history s x) :
    (algorithm.step history s x).2 = planned history s x h := by
  simp only [algorithm,dif_pos h]

theorem run_history (history xs : List Nat) (s : Tree) :
    (algorithm.runFrom history s xs).1 = history++xs := by
  induction xs generalizing history s with
  | nil => simp [StatefulAlgorithm.runFrom]
  | cons x xs ih =>
    simp only [StatefulAlgorithm.runFrom,ih,step_history,List.append_assoc,List.singleton_append]

theorem step_candidate (history : List Nat) (s : Tree) (x : Nat)
    (h : Ready history s x) (p : Candidate) (hp : Valid s.size p)
    (hsel : (selected (history++[x]) h.2).value = p) :
    (algorithm.step history s x).2 =
      let plan := candidatePlan s.size h.1 p hp
      let hs : s.size = (plan.tree history.length).size := by
        rw [plan_size,spine_size,Tree.size,Nat.add_zero]
      (plan.tree (history.length+1),
        repair s (plan.tree history.length) hs + plan.rotations history.length) := by
  rw [step_planned history s x h]
  cases hsel
  rfl

theorem synchronized_step (history : List Nat) (s : Tree) (x : Nat)
    (h : Ready history s x) (n : Nat) (hn : 0<n) (p : Candidate) (hp : Valid n p)
    (hsize : s.size = n)
    (hsel : (selected (history++[x]) h.2).value = p)
    (aligned : s = (candidatePlan n hn p hp).tree history.length) :
    (algorithm.step history s x).2 =
      ((candidatePlan n hn p hp).tree (history.length+1),
        (candidatePlan n hn p hp).rotations history.length) := by
  subst n
  rw [step_candidate history s x h p hp hsel]
  dsimp only
  have hz : repair s ((candidatePlan s.size hn p hp).tree history.length)
      (by rw [plan_size,spine_size,Tree.size,Nat.add_zero]) = 0 := by
    simp only [repair,if_pos aligned]
  rw [hz,Nat.zero_add]

theorem step_candidate_endpoint (history : List Nat) (s : Tree) (x : Nat)
    (h : Ready history s x) (n : Nat) (hn : 0<n) (p : Candidate) (hp : Valid n p)
    (hsize : s.size = n) (hsel : (selected (history++[x]) h.2).value = p) :
    (algorithm.step history s x).2.1 = (candidatePlan n hn p hp).tree (history.length+1) := by
  subst n
  rw [step_candidate history s x h p hp hsel]

/-- info: 'RotationBST.ForecastAlgorithm.synchronized_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms synchronized_step
end ForecastAlgorithm
end RotationBST
