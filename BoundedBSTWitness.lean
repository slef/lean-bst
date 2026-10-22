import BoundedCycles
import ProbeReduction

/-! Short request words witness every positive loop in the BST comparison graph.
The finite cover depends only on the number of keys, not on the algorithm. -/
namespace RotationBST.ProbeReduction
open FiniteWeightedPaths

theorem trace_execution_length (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Trace (Edge b C T) p q steps) :
    ∃ xs k, Execution p.2 xs q.2 k ∧ endpoint b p.1 xs = q.1 ∧
      weight steps = (b.totalCost p.1 xs : Int) - (C : Int) * (xs.length + k : Nat) ∧
      xs.length = steps.length := by
  induction h with
  | @nil p =>
      refine ⟨[], 0, .nil, rfl, ?_, rfl⟩
      simp [weight, treeOnly_cost_eq, StatefulAlgorithm.runFrom]
  | @cons p r w q rest he ht ih =>
      obtain ⟨_,x,k,ha,hend,hw⟩ := he
      obtain ⟨xs,j,hex,hep,hec,hlen⟩ := ih
      refine ⟨x::xs, k+j, .cons ha hex, ?_, ?_, by simp [hlen]⟩
      · rw [endpoint_cons, ← hend]; exact hep
      · change w + weight rest = _
        rw [hw, hec, treeOnly_cost_cons, ← hend]
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one, Int.mul_add,
          Int.mul_one]
        omega

theorem edge_reachable (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Edge b C T p q w) :
    ∃ pre, Trace (Edge b C T) (T,T) p pre := by
  obtain ⟨xs,k,he,hb⟩ := h.1
  obtain ⟨steps,hs,_⟩ := execution_trace b C T he T (reach_start b T)
  rw [hb] at hs
  exact ⟨steps,hs⟩

/-- A positive comparison loop has an ultimately periodic request witness with
both prefix and period bounded solely by the finite tree-pair cover. Repeating
its period gives a positive cost excess each time. -/
theorem bounded_request_witness (b : TreeAlgorithm) (C : Nat) (T : Tree)
    (h : Trace (Edge b C T) p p steps) (hw : 0 < weight steps) :
    ∃ s t pre word j k,
      Execution T pre t j ∧ endpoint b T pre = s ∧
      Execution t word t k ∧ endpoint b s word = s ∧
      C * (word.length+k) < b.totalCost s word ∧
      pre.length < (pairCover T.size).length ∧
      word.length ≤ (pairCover T.size).length := by
  have sources : ∀ p q w, Edge b C T p q w → p ∈ pairCover T.size := by
    intro p q w he
    obtain ⟨hs,ht⟩ := reach_sizes b T he.1
    exact mem_pairCover p hs ht
  obtain ⟨v,pre,cycle,hpre,hcycle,hpos,hplen,hclen⟩ :=
    bounded_lasso (Edge b C T) (pairCover T.size) (T,T)
      (mem_pairCover (T,T) rfl rfl) sources
      (fun _ _ _ he => edge_closed b C T he)
      (fun _ _ _ he => edge_reachable b C T he) h hw
  obtain ⟨xs,j,hex,heb,_,hlx⟩ := trace_execution_length b C T hpre
  obtain ⟨word,k,hew,heq,hweight,hlw⟩ := trace_execution_length b C T hcycle
  refine ⟨v.1,v.2,xs,word,j,k,hex,heb,hew,heq,?_,by omega,by omega⟩
  rw [hweight] at hpos
  have hcast : (C : Int) * (word.length+k : Nat) = (C*(word.length+k) : Nat) := by simp
  rw [hcast] at hpos
  omega

/-- Testing only the bounded prefix/period pairs suffices for a global offline
bound. The hypothesis compares all paired serving loops for those words. -/
theorem bounded_tests_suffice (b : TreeAlgorithm) (C : Nat)
    (tests : ∀ T s t pre word j k,
      Execution T pre t j → endpoint b T pre = s →
      Execution t word t k → endpoint b s word = s →
      pre.length < (pairCover T.size).length →
      word.length ≤ (pairCover T.size).length →
      b.totalCost s word ≤ C*(word.length+k)) :
    OfflineCompetitiveWith b C (graphAllowance b) := by
  have noPositive : ∀ T p steps, Trace (Edge b C T) p p steps → weight steps ≤ 0 := by
    intro T p steps hs
    apply Classical.byContradiction
    intro hn
    obtain ⟨s,t,pre,word,j,k,he,hb,hw,hloop,hcost,hpre,hword⟩ :=
      bounded_request_witness b C T hs (by omega)
    have ht := tests T s t pre word j k he hb hw hloop hpre hword
    omega
  intro T xs u k he
  obtain ⟨steps,hs,hw⟩ := execution_trace b C T he T (reach_start b T)
  have hg := finite_path_bound (Edge b C T) (pairCover T.size)
    (fun _ _ _ h => edge_closed b C T h) (stepBound b T.size)
    (fun _ _ _ h => edge_bound b C T h)
    (noPositive T) hs (mem_pairCover (T,T) rfl rfl)
  rw [hw] at hg
  have heq : ((pairCover T.size).length : Int) * stepBound b T.size =
      (graphAllowance b T.size : Int) := by simp [graphAllowance]
  rw [heq] at hg
  have heq2 : (C : Int) * (xs.length+k : Nat) = (C * (xs.length+k) : Nat) := by simp
  rw [heq2] at hg
  omega

/-- Only a finite family of prefix/period request words is needed at each size.
This property alone does not assert that the probe has finite private memory. -/
def BoundedPeriodicProbe (a : StatefulAlgorithm σ) : Prop :=
  ∀ T pre t j word k,
    Execution T pre t j → Execution t word t k →
    pre.length < (pairCover T.size).length →
    word.length ≤ (pairCover T.size).length →
    ∃ K, ∀ m, a.totalCost T (pre ++ repeatWord word m) ≤
      m * (word.length+k) + K

/-- A simulator for a bounded periodic probe is already offline competitive. -/
theorem bounded_probe_domination (a : StatefulAlgorithm σ)
    (hp : BoundedPeriodicProbe a) (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (dom : ∀ T xs, ValidInput T xs → b.totalCost T xs ≤ C*a.totalCost T xs+f T.size) :
    OfflineCompetitiveWith b C (graphAllowance b) := by
  apply bounded_tests_suffice b C
  intro T s t pre word j k hpre hbs hloop hbloop hplen hwlen
  obtain ⟨K,hK⟩ := hp T pre t j word k hpre hloop hplen hwlen
  apply Classical.byContradiction
  intro hn
  let m := C*K+f T.size+1
  have hd := dom T (pre ++ repeatWord word m) (hpre.append (hloop.repeat m)).validInput
  have hu := Nat.mul_le_mul_left C (hK m)
  rw [treeOnly_cost_append] at hd
  change b.totalCost T pre + b.totalCost (endpoint b T pre) (repeatWord word m) ≤ _ at hd
  rw [hbs,treeOnly_repeat_cost b s word hbloop m] at hd
  have hg : C*(word.length+k)+1 ≤ b.totalCost s word := by omega
  have hm := Nat.mul_le_mul_left m hg
  rw [Nat.mul_add,Nat.mul_one] at hm
  rw [Nat.mul_add,Nat.mul_left_comm C m] at hu
  dsimp [m] at *
  omega

/-- info: 'RotationBST.ProbeReduction.bounded_request_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded_request_witness
end RotationBST.ProbeReduction
