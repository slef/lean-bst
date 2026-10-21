import OptimalPrefixes
import FiniteTrees
import FiniteBranching

/-! Constructing a clairvoyant plan for a fixed infinite request word.
This is not an online algorithm; the whole word is an input to the construction. -/
namespace RotationBST
namespace InfinitePlanning

def segment (word : Nat → Nat) (start : Nat) : Nat → List Nat
  | 0 => []
  | len+1 => word start :: segment word (start+1) len

theorem segment_add (word : Nat → Nat) (start m n : Nat) :
    segment word start (m+n) = segment word start m ++ segment word (start+m) n := by
  induction m generalizing start with
  | zero => simp [segment]
  | succ m ih =>
      simpa [segment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (List.cons (word start)) (ih (start+1))

theorem segment_valid (word : Nat → Nat) (t : Tree) (valid : ∀ i, word i < t.size)
    (start len : Nat) : ValidInput t (segment word start len) := by
  induction len generalizing start with
  | zero => simp [segment, ValidInput]
  | succ len ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact valid start
      · exact ih (start+1) x hx

/-- The current prefix can be completed to an optimum at arbitrarily distant
horizons. We do not require it to be optimal at every horizon. -/
def FutureOptimal (word : Nat → Nat) (initial : Tree) (time : Nat)
    (current : Tree) (cost : Nat) : Prop :=
  ∀ L, ∃ len u k, L ≤ len ∧ Execution current (segment word time len) u k ∧
    RotationOptimal initial (segment word 0 (time+len)) (cost+k)

theorem initial_future (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i < initial.size) : FutureOptimal word initial 0 initial 0 := by
  intro L
  obtain ⟨u,k,he,ho⟩ := optimal_execution_exists initial (segment word 0 L)
    (segment_valid word initial valid 0 L)
  exact ⟨L,u,k,Nat.le_refl _,he,by simpa using ho⟩

def choices (n : Nat) : List (Tree × Nat) :=
  (treeCover n).flatMap (fun t => (List.range (2*n+1)).map (fun k => (t,k)))

theorem choice_mem (v : Tree) (k : Nat) (hv : v.size = n) (hk : k ≤ 2*n) :
    (v,k) ∈ choices n := by
  apply List.mem_flatMap.mpr
  refine ⟨v,mem_treeCover v n (by omega),?_⟩
  exact List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩

/-- Finitely many legal first actions cover arbitrarily long optimal
completions, so one action retains the same unbounded-completion property. -/
theorem future_successor (word : Nat → Nat) (initial current : Tree)
    (time cost : Nat) (pre : Execution initial (segment word 0 time) current cost)
    (future : FutureOptimal word initial time current cost) :
    ∃ v k, Access current v (word time) k ∧ k ≤ 2*initial.size ∧
      FutureOptimal word initial (time+1) v (cost+k) := by
  let P : (Tree × Nat) → Nat → Prop := fun p L =>
    Access current p.1 (word time) p.2 ∧ p.2 ≤ 2*initial.size ∧
      ∃ len u k, L ≤ len ∧ Execution p.1 (segment word (time+1) len) u k ∧
        RotationOptimal initial (segment word 0 ((time+1)+len)) ((cost+p.2)+k)
  have down : ∀ p m n, m ≤ n → P p n → P p m := by
    intro p m n hmn hp
    obtain ⟨ha,hb,len,u,k,hn,he,ho⟩ := hp
    exact ⟨ha,hb,len,u,k,by omega,he,ho⟩
  have cover : ∀ L, ∃ p, p ∈ choices initial.size ∧ P p L := by
    intro L
    obtain ⟨len,u,k,hl,he,ho⟩ := future (L+1)
    cases len with
    | zero => omega
    | succ len =>
      cases he with
      | @cons _ v _ j _ _ m ha ht =>
        have hopt : RotationOptimal initial
            (segment word 0 time ++ word time :: segment word (time+1) len)
            (cost+(j+m)) := by
          have hcopy := ho
          rw [segment_add word 0 time (len+1)] at hcopy
          simpa only [Nat.zero_add, segment] using hcopy
        have hb := optimal_access_bound pre ha ht hopt
        have hv : v.size = initial.size := ha.1.size_eq.symm.trans pre.size_eq.symm
        refine ⟨(v,j),choice_mem v j hv hb,ha,hb,len,u,m,by omega,ht,?_⟩
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho
  obtain ⟨p,_,hp⟩ := FiniteBranching.finite_cover (choices initial.size) P down cover
  refine ⟨p.1,p.2,(hp 0).1,(hp 0).2.1,?_⟩
  intro L
  exact (hp L).2.2

structure Partial (word : Nat → Nat) (initial : Tree) (time : Nat) where
  tree : Tree
  cost : Nat
  execution : Execution initial (segment word 0 time) tree cost
  future : FutureOptimal word initial time tree cost

noncomputable def action (p : Partial word initial time) : Tree × Nat :=
  let h := future_successor word initial p.tree time p.cost p.execution p.future
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem action_spec (p : Partial word initial time) :
    Access p.tree (action p).1 (word time) (action p).2 ∧
    (action p).2 ≤ 2*initial.size ∧
    FutureOptimal word initial (time+1) (action p).1 (p.cost+(action p).2) :=
  Classical.choose_spec (Classical.choose_spec
    (future_successor word initial p.tree time p.cost p.execution p.future))

noncomputable def extend (p : Partial word initial time) : Partial word initial (time+1) where
  tree := (action p).1
  cost := p.cost+(action p).2
  execution := by
    have he := p.execution.append (Execution.cons (action_spec p).1 Execution.nil)
    rw [segment_add word 0 time 1]
    simpa [segment] using he
  future := (action_spec p).2.2

noncomputable def partialPlan (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i < initial.size) : (time : Nat) → Partial word initial time
  | 0 => ⟨initial,0,.nil,initial_future word initial valid⟩
  | time+1 => extend (partialPlan word initial valid time)

/-- A clairvoyant plan has bounded actions and a simultaneous prefix guarantee.
The functions may depend on the ENTIRE infinite request word. -/
structure Plan (word : Nat → Nat) (initial : Tree) where
  tree : Nat → Tree
  rotations : Nat → Nat
  cost : Nat → Nat
  start : tree 0 = initial
  zero_cost : cost 0 = 0
  cost_step : ∀ i, cost (i+1) = cost i + rotations i
  access : ∀ i, Access (tree i) (tree (i+1)) (word i) (rotations i)
  action_bound : ∀ i, rotations i ≤ 2*initial.size
  execution : ∀ i, Execution initial (segment word 0 i) (tree i) (cost i)
  prefix_bound : ∀ i v z j, initial.size = v.size →
    Execution v (segment word 0 i) z j → cost i ≤ j + 4*initial.size

/-- Compactness supplies one plan good for EVERY prefix of a known infinite
input. This does not give an online plan for an unknown input. -/
noncomputable def known_future_plan (word : Nat → Nat) (initial : Tree)
    (valid : ∀ i, word i < initial.size) : Plan word initial where
  tree := fun i => (partialPlan word initial valid i).tree
  rotations := fun i => (action (partialPlan word initial valid i)).2
  cost := fun i => (partialPlan word initial valid i).cost
  start := rfl
  zero_cost := rfl
  cost_step := fun _ => rfl
  access := fun i => (action_spec (partialPlan word initial valid i)).1
  action_bound := fun i => (action_spec (partialPlan word initial valid i)).2.1
  execution := fun i => (partialPlan word initial valid i).execution
  prefix_bound := by
    intro i v z j hsize he
    let p := partialPlan word initial valid i
    obtain ⟨len,u,k,_,hsuf,ho⟩ := p.future 0
    have hopt : RotationOptimal initial
        (segment word 0 i ++ segment word i len) (p.cost+k) := by
      rw [segment_add word 0 i len] at ho
      simpa only [Nat.zero_add] using ho
    exact optimal_prefix_other_start p.execution hsuf hopt he hsize

/-- info: 'RotationBST.InfinitePlanning.known_future_plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms known_future_plan
end InfinitePlanning
end RotationBST
