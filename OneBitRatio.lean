import OneBitSeparation
import PeriodicComparison

/-! Seven periodic tests strengthen the one-bit lower bound to 12/11.
The finite certificate uses kernel reduction (`decide`), not an external solver.
The test word may depend on B; the comparator algorithm is fixed. -/
namespace RotationBST.ThreeKey.OneBit

def witnesses : List (List Nat) :=
  [[0,1], [0,0,1], [2,1,1], [0,2,1,1], [2,2,1,1], [0,0,2,0,1], [2,0,2,0,2,1]]

def fullPolicy (a0 a2 b0 b2 c0 c2 d0 d2 e0 e2 : Bool) : Shape → Nat → Shape
  | .a, 0 => if a0 then .a else .b
  | .b, 0 => if b0 then .a else .b
  | .c, 0 => if c0 then .a else .b
  | .d, 0 => if d0 then .a else .b
  | .e, 0 => if e0 then .a else .b
  | .a, 2 => if a2 then .d else .e
  | .b, 2 => if b2 then .d else .e
  | .c, 2 => if c2 then .d else .e
  | .d, 2 => if d2 then .d else .e
  | .e, 2 => if e2 then .d else .e
  | _, _ => .c

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem ratio_certificate : ∀ a0 a2 b0 b2 c0 c2 d0 d2 e0 e2 : Bool,
    ∃ w ∈ witnesses, 12 * algorithm.totalCost Shape.c.tree w ≤
      11 * (w.length + cost (fullPolicy a0 a2 b0 b2 c0 c2 d0 d2 e0 e2) .c w) := by decide

theorem witnesses_loop : ∀ w ∈ witnesses,
    (algorithm.runFrom 0 Shape.c.tree w).1 = 0 ∧
    (algorithm.runFrom 0 Shape.c.tree w).2.1 = Shape.c.tree ∧
    (∀ x ∈ w, x < 3) ∧ w.getLast? = some 1 := by decide

def encoded (p : Shape → Nat → Shape) := fullPolicy
  (decide (p .a 0 = .a)) (decide (p .a 2 = .d))
  (decide (p .b 0 = .a)) (decide (p .b 2 = .d))
  (decide (p .c 0 = .a)) (decide (p .c 2 = .d))
  (decide (p .d 0 = .a)) (decide (p .d 2 = .d))
  (decide (p .e 0 = .a)) (decide (p .e 2 = .d))

theorem encoded_eq (p : Shape → Nat → Shape)
    (valid : ∀ s x, x<3 → root (p s x)=x) (s : Shape) (x : Nat) (hx : x<3) :
    encoded p s x = p s x := by
  have zero (s : Shape) : (if decide (p s 0 = .a) then Shape.a else .b) = p s 0 := by
    have hv := valid s 0 (by decide)
    cases h : p s 0 <;> simp_all [root]
  have two (s : Shape) : (if decide (p s 2 = .d) then Shape.d else .e) = p s 2 := by
    have hv := valid s 2 (by decide)
    cases h : p s 2 <;> simp_all [root]
  have one := resets p valid s
  have casesx : x=0 ∨ x=1 ∨ x=2 := by omega
  rcases casesx with rfl | rfl | rfl
  · cases s <;> exact zero _
  · cases s <;> exact (resets p valid _).symm
  · cases s <;> exact two _

theorem cost_congr_valid (p q : Shape → Nat → Shape)
    (eq : ∀ s x, x<3 → p s x=q s x) (w : List Nat) (valid : ∀x∈w,x<3) (s : Shape) :
    cost p s w = cost q s w := by
  induction w generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx := valid x (by simp)
    have ht : ∀y∈xs,y<3 := by intro y hy; exact valid y (by simp [hy])
    simp only [cost, eq s x hx, ih ht]

theorem policy_ratio_witness (p : Shape → Nat → Shape)
    (valid : ∀ s x, x<3 → root (p s x)=x) :
    ∃ w ∈ witnesses, 12*algorithm.totalCost Shape.c.tree w ≤ 11*(w.length+cost p .c w) := by
  obtain ⟨w,hw,hc⟩ := ratio_certificate
    (decide (p .a 0 = .a)) (decide (p .a 2 = .d))
    (decide (p .b 0 = .a)) (decide (p .b 2 = .d))
    (decide (p .c 0 = .a)) (decide (p .c 2 = .d))
    (decide (p .d 0 = .a)) (decide (p .d 2 = .d))
    (decide (p .e 0 = .a)) (decide (p .e 2 = .d))
  change 12*algorithm.totalCost Shape.c.tree w ≤ 11*(w.length+cost (encoded p) .c w) at hc
  rw [cost_congr_valid (encoded p) p (encoded_eq p valid) w (witnesses_loop w hw).2.2.1] at hc
  exact ⟨w,hw,hc⟩

theorem witness_tree_loop (p : Shape → Nat → Shape)
    (valid : ∀ s x, x<3 → root (p s x)=x) (w : List Nat) (hw : w∈witnesses) :
    finish p .c w = .c := by
  have one := resets p valid
  simp only [witnesses,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [finish,one]

theorem length_repeat (w : List Nat) (m : Nat) : (repeatWord w m).length = m*w.length := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih => simp [repeatWord,ih,Nat.succ_mul,Nat.add_comm]

theorem algorithm_repeat_cost (w : List Nat) (hw : w∈witnesses) (m : Nat) :
    algorithm.totalCost Shape.c.tree (repeatWord w m) = m*algorithm.totalCost Shape.c.tree w := by
  have hl := witnesses_loop w hw
  rcases hk : algorithm.runFrom 0 Shape.c.tree w with ⟨q,t,k⟩
  rw [hk] at hl
  dsimp only at hl
  obtain ⟨rfl,rfl,_⟩ := hl
  have repeated : algorithm.runFrom 0 Shape.c.tree (repeatWord w m) =
      (0,Shape.c.tree,m*k) := by
    induction m with
    | zero => simp [repeatWord,StatefulAlgorithm.runFrom]
    | succ m ih => simp [repeatWord,run_append,hk,ih,Nat.succ_mul,Nat.add_comm]
  unfold StatefulAlgorithm.totalCost
  change (repeatWord w m).length + (algorithm.runFrom 0 Shape.c.tree (repeatWord w m)).2.2 =
    m*(w.length+(algorithm.runFrom 0 Shape.c.tree w).2.2)
  rw [repeated,length_repeat,hk]
  simp [Nat.mul_add]

theorem simulator_witness (b : TreeAlgorithm) :
    ∃ w ∈ witnesses, (b.runFrom () Shape.c.tree w).2.1 = Shape.c.tree ∧
      12*algorithm.totalCost Shape.c.tree w ≤ 11*b.totalCost Shape.c.tree w := by
  have valid : ∀ s x, x<3 → root (induced b s x)=x :=
    fun s x hx => (induced_step b s x hx).2.1
  obtain ⟨w,hw,hc⟩ := policy_ratio_witness (induced b) valid
  obtain ⟨hend,hcost⟩ := finite_run b .c w (witnesses_loop w hw).2.2.1
  rw [witness_tree_loop _ valid w hw] at hend
  refine ⟨w,hw,hend,?_⟩
  have hi : b.init Shape.c.tree = () := Subsingleton.elim _ _
  unfold StatefulAlgorithm.totalCost
  rw [hi]
  exact Nat.le_trans hc (Nat.mul_le_mul_left 11 (Nat.add_le_add_left hcost _))

theorem no_ratio_below_12_11 (b : TreeAlgorithm) (f : Nat → Nat)
    (numerator denominator : Nat) (hgap : 11*numerator < 12*denominator) :
    ∃ t xs, ValidInput t xs ∧
      numerator*algorithm.totalCost t xs + f t.size < denominator*b.totalCost t xs := by
  obtain ⟨w,hw,hloop,hbound⟩ := simulator_witness b
  have positive : 0 < algorithm.totalCost Shape.c.tree w := by
    have allpos : ∀ v ∈ witnesses, 0 < algorithm.totalCost Shape.c.tree v := by decide
    exact allpos w hw
  have strict : numerator*algorithm.totalCost Shape.c.tree w <
      denominator*b.totalCost Shape.c.tree w := by
    have h1 := Nat.mul_le_mul_left denominator hbound
    have h2 := Nat.mul_lt_mul_of_pos_right hgap positive
    have h3 : 11*(numerator*algorithm.totalCost Shape.c.tree w) <
        11*(denominator*b.totalCost Shape.c.tree w) := by
      calc
        _ = (11*numerator)*algorithm.totalCost Shape.c.tree w := by rw [Nat.mul_assoc]
        _ < (12*denominator)*algorithm.totalCost Shape.c.tree w := h2
        _ = denominator*(12*algorithm.totalCost Shape.c.tree w) := by
          rw [Nat.mul_left_comm denominator 12,Nat.mul_assoc]
        _ ≤ denominator*(11*b.totalCost Shape.c.tree w) := h1
        _ = _ := by rw [Nat.mul_left_comm denominator 11]
    omega
  let m := f 3 + 1
  refine ⟨Shape.c.tree,repeatWord w m,?_,?_⟩
  · have valid : ValidInput Shape.c.tree w := by
      intro x hx
      rw [shape_size]
      exact (witnesses_loop w hw).2.2.1 x hx
    have he := algorithm.execution 0 Shape.c.tree w valid
    rw [(witnesses_loop w hw).2.1] at he
    exact (he.repeat m).validInput
  · rw [algorithm_repeat_cost w hw m,treeOnly_repeat_cost b _ w hloop m,shape_size]
    have hg : numerator*algorithm.totalCost Shape.c.tree w+1 ≤
        denominator*b.totalCost Shape.c.tree w := by omega
    have hm := Nat.mul_le_mul_left m hg
    rw [Nat.mul_add,Nat.mul_one] at hm
    rw [Nat.mul_left_comm numerator m,Nat.mul_left_comm denominator m]
    dsimp [m] at *
    omega

/-- info: 'RotationBST.ThreeKey.OneBit.no_ratio_below_12_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_ratio_below_12_11
end RotationBST.ThreeKey.OneBit
