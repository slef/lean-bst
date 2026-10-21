import PeriodicComparison
import FiniteWeightedPaths
import FiniteTrees
import AdditiveNormalization

/-! Conditional reduction from domination of a periodic probe to offline
competitiveness. The existence of such a probe remains a separate obligation. -/
namespace RotationBST
namespace ProbeReduction
open FiniteWeightedPaths

def endpoint (b : TreeAlgorithm) (s : Tree) (xs : List Nat) :=
  (b.runFrom () s xs).2.1

theorem endpoint_append (b : TreeAlgorithm) (s : Tree) (xs ys : List Nat) :
    endpoint b s (xs ++ ys) = endpoint b (endpoint b s xs) ys := by
  simp only [endpoint, StatefulAlgorithm.runFrom_append]

theorem endpoint_cons (b : TreeAlgorithm) (s : Tree) (x : Nat) (xs : List Nat) :
    endpoint b s (x :: xs) = endpoint b (b.step () s x).2.1 xs := by
  simp only [endpoint, StatefulAlgorithm.runFrom]

def Reach (b : TreeAlgorithm) (T : Tree) (p : Tree × Tree) : Prop :=
  ∃ xs k, Execution T xs p.2 k ∧ endpoint b T xs = p.1

theorem reach_start (b : TreeAlgorithm) (T : Tree) : Reach b T (T,T) :=
  ⟨[], 0, .nil, rfl⟩

theorem reach_sizes (b : TreeAlgorithm) (T : Tree) (h : Reach b T p) :
    p.1.size = T.size ∧ p.2.size = T.size := by
  obtain ⟨xs,k,he,hb⟩ := h
  have hbe := b.execution () T xs he.validInput
  exact ⟨by rw [← hb]; exact hbe.size_eq.symm, he.size_eq.symm⟩

theorem reach_next (b : TreeAlgorithm) (T : Tree) (h : Reach b T p)
    (ha : Access p.2 u x k) :
    Reach b T ((b.step () p.1 x).2.1, u) := by
  obtain ⟨xs,j,he,hb⟩ := h
  refine ⟨xs ++ [x], j + (k+0), he.append (.cons ha .nil), ?_⟩
  rw [endpoint_append, hb, endpoint_cons]
  rfl

def Edge (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (p q : Tree × Tree) (w : Int) : Prop :=
  Reach b T p ∧ ∃ x k, Access p.2 q.2 x k ∧ q.1 = (b.step () p.1 x).2.1 ∧
    w = (1 + (b.step () p.1 x).2.2 : Nat) - (C : Int) * (1 + k : Nat)

theorem trace_execution (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Trace (Edge b C T) p q steps) :
    ∃ xs k, Execution p.2 xs q.2 k ∧ endpoint b p.1 xs = q.1 ∧
      weight steps = (b.totalCost p.1 xs : Int) - (C : Int) * (xs.length + k : Nat) := by
  induction h with
  | @nil p =>
      refine ⟨[], 0, .nil, rfl, ?_⟩
      simp [weight, treeOnly_cost_eq, StatefulAlgorithm.runFrom]
  | @cons p r w q rest he ht ih =>
      obtain ⟨_,x,k,ha,hend,hw⟩ := he
      obtain ⟨xs,j,hex,hep,hec⟩ := ih
      refine ⟨x::xs, k+j, .cons ha hex, ?_, ?_⟩
      · rw [endpoint_cons, ← hend]; exact hep
      · change w + weight rest = _
        rw [hw, hec, treeOnly_cost_cons, ← hend]
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one, Int.mul_add,
          Int.mul_one]
        omega

theorem execution_trace (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (he : Execution t xs u k) (s : Tree) (hr : Reach b T (s,t)) :
    ∃ steps, Trace (Edge b C T) (s,t) (endpoint b s xs,u) steps ∧
      weight steps = (b.totalCost s xs : Int) - (C : Int) * (xs.length + k : Nat) := by
  induction he generalizing s with
  | nil =>
      refine ⟨[], .nil, ?_⟩
      simp [weight, treeOnly_cost_eq, StatefulAlgorithm.runFrom]
  | @cons t v x k xs u j ha ht ih =>
      obtain ⟨steps,hsteps,hw⟩ := ih _ (reach_next b T hr ha)
      let w : Int := (1 + (b.step () s x).2.2 : Nat) - (C : Int) * (1+k : Nat)
      refine ⟨((s,t),w)::steps, ?_, ?_⟩
      · rw [endpoint_cons]
        exact .cons ⟨hr,x,k,ha,rfl,rfl⟩ hsteps
      · change w + weight steps = _
        rw [hw, treeOnly_cost_cons]
        dsimp [w]
        simp only [Int.mul_add, Int.mul_one]
        omega

theorem no_positive_loops (a : StatefulAlgorithm σ) (hp : PeriodicProbe a)
    (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (dom : ∀ T xs, ValidInput T xs → b.totalCost T xs ≤ C * a.totalCost T xs + f T.size)
    (T : Tree) (p : Tree × Tree) (steps : List ((Tree × Tree) × Int))
    (h : Trace (Edge b C T) p p steps) : weight steps ≤ 0 := by
  by_cases hn : steps = []
  · subst steps; simp [weight]
  have hr : Reach b T p := by
    cases h with
    | nil => exact (hn rfl).elim
    | cons he _ => exact he.1
  obtain ⟨pre,j,hpre,hpreb⟩ := hr
  obtain ⟨xs,k,he,hb,hw⟩ := trace_execution b C T h
  have hloop : (b.runFrom () (b.runFrom () T pre).2.1 xs).2.1 =
      (b.runFrom () T pre).2.1 := by
    change endpoint b (endpoint b T pre) xs = endpoint b T pre
    rw [hpreb]; exact hb
  have hc := probe_forbids_positive_loop a hp b C f dom T pre xs p.2 j k hpre he hloop
  change b.totalCost (endpoint b T pre) xs ≤ _ at hc
  rw [hpreb] at hc
  rw [hw]
  have hi : (b.totalCost p.1 xs : Int) ≤ (C * (xs.length + k) : Nat) := by omega
  simp only [Int.natCast_mul] at hi
  omega

def pairCover (n : Nat) : List (Tree × Tree) :=
  (treeCover n).flatMap (fun s => (treeCover n).map (fun t => (s,t)))

theorem mem_pairCover (p : Tree × Tree) (hs : p.1.size = n) (ht : p.2.size = n) :
    p ∈ pairCover n := by
  apply List.mem_flatMap.mpr
  refine ⟨p.1, mem_treeCover _ _ (by omega), ?_⟩
  exact List.mem_map.mpr ⟨p.2, mem_treeCover _ _ (by omega), rfl⟩

theorem edge_closed (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Edge b C T p q w) : q ∈ pairCover T.size := by
  obtain ⟨hr,x,k,ha,he,_⟩ := h
  have hn := reach_next b T hr ha
  have hq : ((b.step () p.1 x).2.1, q.2) = q := by rw [← he]
  rw [hq] at hn
  obtain ⟨hs,ht⟩ := reach_sizes b T hn
  exact mem_pairCover q hs ht

theorem edge_bound (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Edge b C T p q w) : w ≤ (stepBound b T.size : Int) := by
  obtain ⟨hr,x,k,ha,_,hw⟩ := h
  obtain ⟨hs,ht⟩ := reach_sizes b T hr
  have hx : x < T.size := by rw [← ht]; exact ha.in_range
  have hb := step_le_stepBound b p.1 hs hx
  have hn : (0 : Int) ≤ (C : Int) * (1+k : Nat) :=
    Int.mul_nonneg (by omega) (by omega)
  rw [hw]
  omega

/-- The additive allowance obtained by cycle erasure can be huge, but is
independent of the request sequence length. -/
def graphAllowance (b : TreeAlgorithm) (n : Nat) : Nat :=
  (pairCover n).length * stepBound b n

theorem probe_domination_offline (a : StatefulAlgorithm σ) (hp : PeriodicProbe a)
    (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (dom : ∀ T xs, ValidInput T xs → b.totalCost T xs ≤ C * a.totalCost T xs + f T.size) :
    OfflineCompetitiveWith b C (graphAllowance b) := by
  intro T xs u k he
  obtain ⟨steps,hs,hw⟩ := execution_trace b C T he T (reach_start b T)
  have hg := finite_path_bound (Edge b C T) (pairCover T.size)
    (fun _ _ _ h => edge_closed b C T h) (stepBound b T.size)
    (fun _ _ _ h => edge_bound b C T h)
    (no_positive_loops a hp b C f dom T) hs (mem_pairCover (T,T) rfl rfl)
  rw [hw] at hg
  have heq : ((pairCover T.size).length : Int) * stepBound b T.size =
      (graphAllowance b T.size : Int) := by simp [graphAllowance]
  rw [heq] at hg
  have heq2 : (C : Int) * (xs.length+k : Nat) = (C * (xs.length+k) : Nat) := by simp
  rw [heq2] at hg
  omega

/-- A simulator for just one suitable periodic probe already entails a
tree-only offline-competitive algorithm with a linear additive allowance. -/
theorem probe_domination_linear (a : StatefulAlgorithm σ) (hp : PeriodicProbe a)
    (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (dom : ∀ T xs, ValidInput T xs → b.totalCost T xs ≤ C * a.totalCost T xs + f T.size) :
    ∃ b' : TreeAlgorithm, ∀ t xs u k, Execution t xs u k →
      b'.totalCost t xs ≤ C * (xs.length+k) + (2+6*C)*t.size :=
  normalize_additive b C (graphAllowance b) (probe_domination_offline a hp b C f dom)

/-- Under existence of a periodic probe, the apparently weaker elimination
question with arbitrary additive allowance is equivalent to existence of one
universally competitive tree-only algorithm. This theorem does not discharge
the probe-existence hypothesis or either existence statement. -/
theorem elimination_iff_universal_given_probe
    (probe : ∃ (σ : Type) (a : StatefulAlgorithm σ), PeriodicProbe a) :
    StateEliminationWithAdditive ↔ ∃ b : TreeAlgorithm, UniversallyCompetitive b := by
  constructor
  · intro he
    obtain ⟨σ,a,hp⟩ := probe
    obtain ⟨b,C,f,hb⟩ := he σ a
    obtain ⟨b',hb'⟩ := probe_domination_linear a hp b C f hb
    exact ⟨b',C,2+6*C,hb'⟩
  · intro hu
    exact linear_implies_arbitrary_additive (stateElimination_of_universal hu)

theorem arbitrary_iff_linear_given_probe
    (probe : ∃ (σ : Type) (a : StatefulAlgorithm σ), PeriodicProbe a) :
    StateEliminationWithAdditive ↔ StateElimination := by
  constructor
  · intro h
    exact stateElimination_of_universal ((elimination_iff_universal_given_probe probe).mp h)
  · exact linear_implies_arbitrary_additive

/-- info: 'RotationBST.ProbeReduction.probe_domination_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms probe_domination_linear
/-- info: 'RotationBST.ProbeReduction.elimination_iff_universal_given_probe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms elimination_iff_universal_given_probe
end ProbeReduction
end RotationBST
