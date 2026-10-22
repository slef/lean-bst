import ForecastTracking
import ProbeReduction

namespace RotationBST
namespace PeriodicProbeConstruction
open InfinitePlanning PeriodicCandidates ForecastAlgorithm ForecastTracking

theorem segment_eq_list (word : Nat → Nat) (start : Nat) (xs : List Nat)
    (h : ∀ i, i<xs.length → word (start+i)=atRank xs i) :
    segment word start xs.length = xs := by
  apply List.ext_getElem (segment_length word start xs.length)
  intro i hi hj
  have hh := (segment_atRank word start xs.length i hj).trans (h i hj)
  simpa [atRank,hi,hj] using hh

theorem forecast_head (pre per : List Nat) :
    segment (forecast (pre,per)) 0 pre.length = pre := by
  apply segment_eq_list
  intro i hi
  simp [forecast,hi]

theorem forecast_block (pre per : List Nat) (q : Nat) :
    segment (forecast (pre,per)) (pre.length+q*per.length) per.length = per := by
  apply segment_eq_list
  intro i hi
  have hnot : ¬(pre.length+q*per.length+i < pre.length) := by omega
  simp only [forecast,if_neg hnot]
  have hsub : pre.length+q*per.length+i-pre.length = q*per.length+i := by omega
  rw [hsub]
  simp [Nat.add_mod,Nat.mod_eq_of_lt hi]

theorem forecast_blocks (pre per : List Nat) (q m : Nat) :
    segment (forecast (pre,per)) (pre.length+q*per.length) (m*per.length) =
      repeatWord per m := by
  induction m generalizing q with
  | zero => simp [segment,repeatWord]
  | succ m ih =>
    have hlen : (m+1)*per.length = per.length+m*per.length := by rw [Nat.succ_mul]; omega
    rw [hlen,segment_add,forecast_block]
    have hstart : pre.length+q*per.length+per.length = pre.length+(q+1)*per.length := by
      rw [Nat.succ_mul]; omega
    rw [hstart,ih]
    rfl

theorem forecast_repetitions (pre per : List Nat) (m : Nat) :
    segment (forecast (pre,per)) 0 (pre.length+m*per.length) = pre++repeatWord per m := by
  rw [segment_add,forecast_head]
  have h := forecast_blocks pre per 0 m
  simpa using congrArg (List.append pre) h

theorem repeat_empty (m : Nat) : repeatWord [] m = [] := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [repeatWord] using ih

/-- The explicit forecast-based online algorithm is a periodic probe. It may
use unbounded private history and noncomputable planning, as allowed by the
current mathematical model. -/
theorem algorithm_is_probe : PeriodicProbe algorithm := by
  intro T pre t j word k hpre hloop
  cases word with
  | nil =>
    refine ⟨algorithm.totalCost T pre,?_⟩
    intro m
    simp [repeat_empty]
  | cons x xs =>
    let per := x::xs
    have hn : 0<T.size := by
      have hx := hloop.validInput x (by simp)
      have hs := hpre.size_eq
      omega
    have hv : Valid T.size (pre,per) := by
      refine ⟨hpre.validInput,?_⟩
      intro y hy
      rw [hpre.size_eq]
      exact hloop.validInput y hy
    have valid := forecast_valid (pre,per) hn hv
    obtain ⟨K,hK⟩ := eventual_offline_bound (forecast (pre,per)) T valid (pre,per) hv (fun _ => rfl)
    refine ⟨pre.length+j+K,?_⟩
    intro m
    have he := hpre.append (hloop.repeat m)
    have hb := hK (pre.length+m*per.length) t (j+m*k)
      (by rw [forecast_repetitions]; exact he)
    rw [forecast_repetitions] at hb
    change algorithm.totalCost T (pre++repeatWord per m) ≤ _
    change algorithm.totalCost T (pre++repeatWord per m) ≤ _ at hb
    simp only [Nat.mul_add]
    dsimp [per] at *
    omega

/-- State elimination with arbitrary sequence-independent additive allowance
is equivalent, in this model, to tree-only offline dynamic optimality. This
is an equivalence of existence statements, not a proof of their truth. -/
theorem state_elimination_iff_universal :
    StateEliminationWithAdditive ↔ ∃ b : TreeAlgorithm, UniversallyCompetitive b :=
  ProbeReduction.elimination_iff_universal_given_probe ⟨List Nat,algorithm,algorithm_is_probe⟩

theorem arbitrary_iff_linear : StateEliminationWithAdditive ↔ StateElimination :=
  ProbeReduction.arbitrary_iff_linear_given_probe ⟨List Nat,algorithm,algorithm_is_probe⟩

/-- info: 'RotationBST.PeriodicProbeConstruction.state_elimination_iff_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms state_elimination_iff_universal
end PeriodicProbeConstruction
end RotationBST
