import ForecastAlgorithm

namespace RotationBST
namespace ForecastTracking
open InfinitePlanning PeriodicCandidates ForecastAlgorithm

noncomputable def runAt (word : Nat → Nat) (initial : Tree) (i : Nat) :=
  algorithm.runFrom [] initial (segment word 0 i)

theorem history_at (word : Nat → Nat) (initial : Tree) (i : Nat) :
    (runAt word initial i).1 = segment word 0 i := by
  simpa [runAt] using run_history [] (segment word 0 i) initial

theorem successor (word : Nat → Nat) (initial : Tree) (i : Nat) :
    runAt word initial (i+1) =
      let s := algorithm.step (segment word 0 i) (runAt word initial i).2.1 (word i)
      (s.1,s.2.1,(runAt word initial i).2.2+s.2.2) := by
  unfold runAt
  rw [segment_add word 0 i 1,StatefulAlgorithm.runFrom_append]
  simp only [Nat.zero_add,segment,StatefulAlgorithm.runFrom,Nat.add_zero]
  rw [run_history]
  rfl

theorem size_at (word : Nat → Nat) (initial : Tree) (valid : ∀ i, word i<initial.size)
    (i : Nat) : (runAt word initial i).2.1.size = initial.size :=
  (algorithm.execution [] initial (segment word 0 i) (segment_valid word initial valid 0 i)).size_eq.symm

theorem history_succ (word : Nat → Nat) (i : Nat) :
    segment word 0 i ++ [word i] = segment word 0 (i+1) := by
  rw [segment_add word 0 i 1]
  simp [segment]

theorem ready_at (word : Nat → Nat) (initial : Tree) (valid : ∀ i, word i<initial.size)
    (i : Nat) : Ready (segment word 0 i) (runAt word initial i).2.1 (word i) := by
  constructor
  · rw [size_at word initial valid i]; have := valid i; omega
  · intro y hy
    rw [size_at word initial valid i]
    rw [history_succ] at hy
    exact segment_values word valid 0 (i+1) y hy

theorem selected_congr (xs ys : List Nat) (hn : n=m) (hxy : xs=ys)
    (hx : ∀ y ∈ xs, y<n) (hy : ∀ y ∈ ys, y<m) :
    (selected xs hx).value = (selected ys hy).value := by
  subst m
  subst ys
  rfl

theorem selection_at (word : Nat → Nat) (initial : Tree) (valid : ∀ i, word i<initial.size)
    (i : Nat) :
    (selected (segment word 0 i ++ [word i]) (ready_at word initial valid i).2).value =
    (selected (segment word 0 (i+1)) (segment_values word valid 0 (i+1))).value := by
  exact selected_congr _ _ (size_at word initial valid i) (history_succ word i) _ _

theorem endpoint_stable (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i<initial.size) (hn : 0<initial.size)
    (p : Candidate) (hp : Valid initial.size p) (N : Nat)
    (stable : ∀ i, N ≤ i →
      (selected (segment word 0 i) (segment_values word valid 0 i)).value = p)
    (i : Nat) (hi : N ≤ i+1) :
    (runAt word initial (i+1)).2.1 = (candidatePlan initial.size hn p hp).tree (i+1) := by
  have hs := step_candidate_endpoint (segment word 0 i) (runAt word initial i).2.1
    (word i) (ready_at word initial valid i) initial.size hn p hp
    (size_at word initial valid i) ((selection_at word initial valid i).trans (stable (i+1) hi))
  rw [successor]
  simpa only [segment_length] using hs

theorem cost_stable (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i<initial.size) (hn : 0<initial.size)
    (p : Candidate) (hp : Valid initial.size p) (N : Nat)
    (stable : ∀ i, N ≤ i →
      (selected (segment word 0 i) (segment_values word valid 0 i)).value = p)
    (i : Nat) (hi : N+1 ≤ i) :
    (runAt word initial (i+1)).2.2 = (runAt word initial i).2.2 +
      (candidatePlan initial.size hn p hp).rotations i := by
  have aligned : (runAt word initial i).2.1 =
      (candidatePlan initial.size hn p hp).tree (segment word 0 i).length := by
    rw [segment_length]
    cases i with
    | zero => omega
    | succ j => exact endpoint_stable word initial valid hn p hp N stable j (by omega)
  have hs := synchronized_step (segment word 0 i) (runAt word initial i).2.1 (word i)
    (ready_at word initial valid i) initial.size hn p hp (size_at word initial valid i)
    ((selection_at word initial valid i).trans (stable (i+1) (by omega))) aligned
  rw [successor]
  dsimp only
  rw [hs,segment_length]

theorem cost_mono (word : Nat → Nat) (initial : Tree) (i j : Nat) (hij : i≤j) :
    (runAt word initial i).2.2 ≤ (runAt word initial j).2.2 := by
  induction j with
  | zero => have he : i=0 := by omega
            subst i; exact Nat.le_refl _
  | succ j ih =>
    by_cases hi : i≤j
    · have hh := ih hi
      rw [successor]
      dsimp only
      omega
    · have he : i=j+1 := by omega
      subst i; exact Nat.le_refl _

theorem bounded_transient (a c r : Nat → Nat) (N : Nat)
    (mono : ∀ i j, i≤j → a i≤a j)
    (hc : ∀ i, c (i+1)=c i+r i)
    (ha : ∀ i, N≤i → a (i+1)=a i+r i) :
    ∀ i, a i ≤ a N + c i := by
  have eqn : ∀ m, a (N+m)+c N = a N+c (N+m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.add_succ,ha (N+m) (by omega),hc (N+m)]
      omega
  intro i
  by_cases hi : i≤N
  · have hh := mono i N hi; omega
  · have hh := eqn (i-N)
    have he : N+(i-N)=i := by omega
    rw [he] at hh
    omega

/-- On an input represented by a valid periodic candidate, all learning and
synchronization costs can be absorbed into a single finite additive constant.
The guarantee compares EVERY prefix with EVERY legal offline execution. -/
theorem eventual_offline_bound (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i<initial.size) (truth : Candidate) (hv : Valid initial.size truth)
    (heq : ∀ i, forecast truth i = word i) :
    ∃ K, ∀ i u k, Execution initial (segment word 0 i) u k →
      algorithm.totalCost initial (segment word 0 i) ≤ i+k+K := by
  have hn : 0<initial.size := by have := valid 0; omega
  obtain ⟨N,p,hp,hcorrect,stable⟩ := selected_eventually_correct word valid truth hv heq
  let plan := candidatePlan initial.size hn p hp
  have hb := bounded_transient (fun i => (runAt word initial i).2.2) plan.cost plan.rotations
    (N+1) (cost_mono word initial) plan.cost_step
    (cost_stable word initial valid hn p hp N stable)
  refine ⟨(runAt word initial (N+1)).2.2 + 4*initial.size,?_⟩
  intro i u k he
  have hplan := plan.prefix_bound i initial u k (by simp [spine_size,Tree.size])
  have hword : forecast p = word := funext hcorrect
  have hseg : segment (forecast p) 0 i = segment word 0 i := by rw [hword]
  have hpref := hplan (by rw [hseg]; exact he)
  have hcost := hb i
  change (runAt word initial i).2.2 ≤ _ at hcost
  simp only [spine_size,Tree.size,Nat.add_zero] at hpref
  change (segment word 0 i).length + (runAt word initial i).2.2 ≤ _
  rw [segment_length]
  omega

/-- info: 'RotationBST.ForecastTracking.eventual_offline_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_offline_bound
end ForecastTracking
end RotationBST
