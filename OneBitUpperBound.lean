import OneBitRatio

/-! A matching tree-only simulator for the fixed one-bit comparator.
The finite potential is checked by kernel reduction and telescoped over all
valid inputs. At sizes other than three, both algorithms use move-to-root.
Together with OneBitRatio this establishes the exact coefficient 12/11 for
this comparator, not a universal state-elimination theorem. -/
namespace RotationBST.ThreeKey.OneBit

theorem distance_realized (s t : Shape) : Rotations s.tree t.tree (distance s t) := by
  cases s <;> cases t
  all_goals first
    | exact .refl
    | exact .step .left .refl
    | exact .step .right .refl
    | exact .step (.inLeft .left) .refl
    | exact .step (.inLeft .right) .refl
    | exact .step (.inRight .left) .refl
    | exact .step (.inRight .right) .refl
    | exact .step .left (.step .left .refl)
    | exact .step .left (.step .right .refl)
    | exact .step .left (.step (.inLeft .left) .refl)
    | exact .step .left (.step (.inLeft .right) .refl)
    | exact .step .left (.step (.inRight .left) .refl)
    | exact .step .left (.step (.inRight .right) .refl)
    | exact .step .right (.step .left .refl)
    | exact .step .right (.step .right .refl)
    | exact .step .right (.step (.inLeft .left) .refl)
    | exact .step .right (.step (.inLeft .right) .refl)
    | exact .step .right (.step (.inRight .left) .refl)
    | exact .step .right (.step (.inRight .right) .refl)
    | exact .step (.inLeft .left) (.step .left .refl)
    | exact .step (.inLeft .left) (.step .right .refl)
    | exact .step (.inLeft .left) (.step (.inLeft .left) .refl)
    | exact .step (.inLeft .left) (.step (.inLeft .right) .refl)
    | exact .step (.inLeft .left) (.step (.inRight .left) .refl)
    | exact .step (.inLeft .left) (.step (.inRight .right) .refl)
    | exact .step (.inLeft .right) (.step .left .refl)
    | exact .step (.inLeft .right) (.step .right .refl)
    | exact .step (.inLeft .right) (.step (.inLeft .left) .refl)
    | exact .step (.inLeft .right) (.step (.inLeft .right) .refl)
    | exact .step (.inLeft .right) (.step (.inRight .left) .refl)
    | exact .step (.inLeft .right) (.step (.inRight .right) .refl)
    | exact .step (.inRight .left) (.step .left .refl)
    | exact .step (.inRight .left) (.step .right .refl)
    | exact .step (.inRight .left) (.step (.inLeft .left) .refl)
    | exact .step (.inRight .left) (.step (.inLeft .right) .refl)
    | exact .step (.inRight .left) (.step (.inRight .left) .refl)
    | exact .step (.inRight .left) (.step (.inRight .right) .refl)
    | exact .step (.inRight .right) (.step .left .refl)
    | exact .step (.inRight .right) (.step .right .refl)
    | exact .step (.inRight .right) (.step (.inLeft .left) .refl)
    | exact .step (.inRight .right) (.step (.inLeft .right) .refl)
    | exact .step (.inRight .right) (.step (.inRight .left) .refl)
    | exact .step (.inRight .right) (.step (.inRight .right) .refl)

def simPolicy : Shape → Nat → Shape
  | .a, 0 | .c, 0 => .a
  | _, 0 => .b
  | .b, 2 | .d, 2 => .d
  | _, 2 => .e
  | _, _ => .c

theorem simPolicy_access (s : Shape) (x : Nat) (hx : x<3) :
    Access s.tree (simPolicy s x).tree x (distance s (simPolicy s x)) := by
  refine ⟨distance_realized _ _,?_⟩
  have h : x=0 ∨ x=1 ∨ x=2 := by omega
  rcases h with rfl | rfl | rfl
  all_goals cases s <;> rfl

def simulator : TreeAlgorithm where
  init _ := ()
  step _ t x := if t.size=3 then
    ((),(simPolicy (decode t) x).tree,distance (decode t) (simPolicy (decode t) x))
    else ((),moveToRoot t x)
  correct _ t x hx := by
    split
    next h =>
      obtain ⟨s,rfl⟩ := size_three t h
      rw [decode_shape]
      exact simPolicy_access s x (by rw [shape_size] at hx; exact hx)
    next => exact (moveToRoot_correct t x hx).1

def invariant (q : Fin 2) (s t : Shape) : Bool :=
  match q.val,s,t with
  | 0,.a,.a | 0,.b,.a | 0,.b,.b | 0,.c,.c | 0,.d,.d | 0,.d,.e | 0,.e,.e => true
  | 1,.a,.a | 1,.c,.c | 1,.d,.d | 1,.d,.e => true
  | _,_,_ => false

def potential (q : Fin 2) (s t : Shape) : Nat :=
  match q.val,s,t with
  | 0,.a,.a => 6 | 0,.b,.a => 21 | 0,.b,.b => 0
  | 0,.c,.c => 3 | 0,.d,.d => 3 | 0,.d,.e => 9 | 0,.e,.e => 5
  | 1,.a,.a => 5 | 1,.c,.c => 7 | 1,.d,.d => 2 | 1,.d,.e => 12
  | _,_,_ => 0

theorem step_certificate (q : Fin 2) (s t : Shape) : ∀ x : Fin 3,
    invariant q s t = true →
    let r := algorithm.step q s.tree x.val
    invariant r.1 (decode r.2.1) (simPolicy t x.val) = true ∧
    11*(1+distance t (simPolicy t x.val)) + potential r.1 (decode r.2.1) (simPolicy t x.val) ≤
      12*(1+r.2.2) + potential q s t := by
  have h : q=0 ∨ q=1 := by
    have hq := q.isLt
    have hv : q.val=0 ∨ q.val=1 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases h with rfl | rfl
  all_goals cases s <;> cases t <;> decide

theorem run_bound (q : Fin 2) (s t : Shape) (hi : invariant q s t = true)
    (xs : List Nat) (hv : ∀ x∈xs,x<3) :
    11*(xs.length+(simulator.runFrom () t.tree xs).2.2) ≤
      12*(xs.length+(algorithm.runFrom q s.tree xs).2.2)+potential q s t := by
  induction xs generalizing q s t with
  | nil => simp [StatefulAlgorithm.runFrom]
  | cons x xs ih =>
    have hx := hv x (by simp)
    have ht : ∀ y∈xs,y<3 := by intro y hy; exact hv y (by simp [hy])
    have hs := step_certificate q s t ⟨x,hx⟩ hi
    have ha := algorithm.correct q s.tree x (by rw [shape_size]; exact hx)
    rcases he : algorithm.step q s.tree x with ⟨q',u,k⟩
    rw [he] at ha hs
    have hu : u.size=3 := by rw [← ha.1.size_eq,shape_size]
    obtain ⟨s',rfl⟩ := size_three u hu
    simp only [decode_shape] at hs
    have hind := ih q' s' (simPolicy t x) hs.1 ht
    simp only [StatefulAlgorithm.runFrom,simulator,shape_size,ite_true,decode_shape,he,List.length_cons]
    change 11*(xs.length+1+(distance t (simPolicy t x)+
      (simulator.runFrom () (simPolicy t x).tree xs).2.2)) ≤
      12*(xs.length+1+(k+(algorithm.runFrom q' s'.tree xs).2.2))+potential q s t
    omega

theorem three_key_upper_bound (t : Tree) (hn : t.size=3) (xs : List Nat)
    (hv : ValidInput t xs) :
    11*simulator.totalCost t xs ≤ 12*algorithm.totalCost t xs+6 := by
  obtain ⟨s,rfl⟩ := size_three t hn
  have hi : invariant 0 s s = true := by cases s <;> decide
  have hp : potential 0 s s ≤ 6 := by cases s <;> decide
  have hb := run_bound 0 s s hi xs (by intro x hx; have h:=hv x hx; rwa [shape_size] at h)
  change 11*(xs.length+(simulator.runFrom () s.tree xs).2.2) ≤
    12*(xs.length+(algorithm.runFrom 0 s.tree xs).2.2)+6
  omega

theorem algorithm_step_other (q : Fin 2) (t : Tree) (x : Nat) (hn : t.size≠3) :
    algorithm.step q t x = (0,moveToRoot t x) := by
  have hne : t ≠ (plan (planIndex q t x)).source.tree := by
    intro he
    apply hn
    rw [he,shape_size]
  simp [algorithm,hne]

theorem simulator_step_other (t : Tree) (x : Nat) (hn : t.size≠3) :
    simulator.step () t x = ((),moveToRoot t x) := by simp [simulator,hn]

theorem other_size_run (q : Fin 2) (t : Tree) (hn : t.size≠3)
    (xs : List Nat) (hv : ValidInput t xs) :
    (simulator.runFrom () t xs).2.2 = (algorithm.runFrom q t xs).2.2 := by
  induction xs generalizing q t with
  | nil => rfl
  | cons x xs ih =>
    have hx := hv x (by simp)
    have ha := (moveToRoot_correct t x hx).1
    have hs := ha.1.size_eq
    have hn' : (moveToRoot t x).1.size≠3 := by omega
    have hv' : ValidInput (moveToRoot t x).1 xs := by
      intro y hy
      rw [← hs]
      exact hv y (by simp [hy])
    have hi := ih 0 _ hn' hv'
    simp only [StatefulAlgorithm.runFrom,simulator_step_other t x hn,algorithm_step_other q t x hn]
    rw [hi]

/-- The one-bit example has exactly optimal simulation coefficient 12/11:
this upper bound matches the lower bound proved in OneBitRatio.lean. -/
theorem matching_upper_bound (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    11*simulator.totalCost t xs ≤ 12*algorithm.totalCost t xs+6 := by
  by_cases hn : t.size=3
  · exact three_key_upper_bound t hn xs hv
  · have he := other_size_run 0 t hn xs hv
    change 11*(xs.length+(simulator.runFrom () t xs).2.2) ≤
      12*(xs.length+(algorithm.runFrom 0 t xs).2.2)+6
    omega

/-- The same simulator also has a linear initial-tree allowance. -/
theorem matching_linear_upper_bound (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    11*simulator.totalCost t xs ≤ 12*algorithm.totalCost t xs+2*t.size := by
  by_cases hn : t.size=3
  · have h := matching_upper_bound t xs hv
    simpa only [hn] using h
  · have he := other_size_run 0 t hn xs hv
    change 11*(xs.length+(simulator.runFrom () t xs).2.2) ≤
      12*(xs.length+(algorithm.runFrom 0 t xs).2.2)+2*t.size
    omega

/-- info: 'RotationBST.ThreeKey.OneBit.matching_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms matching_upper_bound
/-- info: 'RotationBST.ThreeKey.OneBit.three_key_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_key_upper_bound
end RotationBST.ThreeKey.OneBit
