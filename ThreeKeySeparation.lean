import StateElimination

/-! Purely additive state elimination is impossible, already on three keys.

One fixed online algorithm has total cost 19m on a repeated eight-request word;
every tree-only algorithm costs at least 20m. The full execution theorem below
rules out every additive function of tree size when the multiplicative factor
is one. It does not refute constant-factor state elimination.
-/
namespace RotationBST.ThreeKey

inductive Shape where
  | a | b | c | d | e
  deriving DecidableEq, Repr

def leaf : Tree := .node .nil .nil

def Shape.tree : Shape → Tree
  | .a => .node .nil (.node .nil leaf)
  | .b => .node .nil (.node leaf .nil)
  | .c => .node leaf leaf
  | .d => .node (.node .nil leaf) .nil
  | .e => .node (.node leaf .nil) .nil

def distance : Shape → Shape → Nat
  | .a, .a | .b, .b | .c, .c | .d, .d | .e, .e => 0
  | .a, .b | .b, .a | .a, .c | .c, .a | .b, .d | .d, .b
  | .c, .e | .e, .c | .d, .e | .e, .d => 1
  | _, _ => 2

/-- The five decisions used by the two test words. Other inputs are irrelevant. -/
def policy (ca a2 b2 d0 e0 : Bool) : Shape → Nat → Shape
  | .c, 0 => if ca then .a else .b
  | .a, 2 => if a2 then .d else .e
  | .b, 2 => if b2 then .d else .e
  | .d, 0 => if d0 then .a else .b
  | .e, 0 => if e0 then .a else .b
  | _, _ => .c

def cost (p : Shape → Nat → Shape) : Shape → List Nat → Nat
  | _, [] => 0
  | t, x :: xs => distance t (p t x) + cost p (p t x) xs

/-- Every tree-only policy loses at least one rotation across these two blocks.
`decide` is kernel checked; this does not use native_decide. -/
theorem two_blocks_certificate : ∀ ca a2 b2 d0 e0 : Bool,
    12 ≤ cost (policy ca a2 b2 d0 e0) .c [0, 2, 1] +
      cost (policy ca a2 b2 d0 e0) .c [0, 2, 0, 2, 1] := by decide

theorem distance_le_two (s t : Shape) : distance s t ≤ 2 := by
  cases s <;> cases t <;> decide

theorem tree_injective (s t : Shape) (h : s.tree = t.tree) : s = t := by
  cases s <;> cases t <;> simp_all [Shape.tree, leaf]

theorem distance_of_rotate (s t : Shape) (h : Rotate s.tree t.tree) :
    distance s t ≤ 1 := by
  cases s <;> cases t <;> simp only [distance] <;> try omega
  all_goals
    cases h <;> rename_i h
    all_goals cases h <;> rename_i h
    all_goals cases h

theorem distance_lower_bound (s t : Shape) (h : Rotations s.tree t.tree k) :
    distance s t ≤ k := by
  have zero_eq : ∀ {u v : Tree}, Rotations u v 0 → u = v := by
    intro u v hr
    cases hr
    rfl
  have one_rot : ∀ {u v : Tree}, Rotations u v 1 → Rotate u v := by
    intro u v hr
    cases hr with
    | step h hs =>
        have he := zero_eq hs
        subst v
        exact h
  cases k with
  | zero =>
      have he := tree_injective s t (zero_eq h)
      subst t
      cases s <;> decide
  | succ k =>
      cases k with
      | zero =>
          exact distance_of_rotate s t (one_rot h)
      | succ k => have := distance_le_two s t; omega

def root : Shape → Nat
  | .a | .b => 0
  | .c => 1
  | .d | .e => 2

theorem size_zero (t : Tree) (h : t.size = 0) : t = .nil := by
  cases t with
  | nil => rfl
  | node l r => simp only [Tree.size] at h; omega

theorem size_one (t : Tree) (h : t.size = 1) : t = leaf := by
  cases t with
  | nil => simp [Tree.size] at h
  | node l r =>
      simp only [Tree.size] at h
      rw [size_zero l (by omega), size_zero r (by omega)]
      rfl

theorem size_two (t : Tree) (h : t.size = 2) :
    t = .node .nil leaf ∨ t = .node leaf .nil := by
  cases t with
  | nil => simp [Tree.size] at h
  | node l r =>
      simp only [Tree.size] at h
      by_cases hl : l.size = 0
      · rw [size_zero l hl, size_one r (by omega)]
        exact Or.inl rfl
      · rw [size_one l (by omega), size_zero r (by omega)]
        exact Or.inr rfl

theorem size_three (t : Tree) (h : t.size = 3) : ∃ s : Shape, t = s.tree := by
  cases t with
  | nil => simp [Tree.size] at h
  | node l r =>
      simp only [Tree.size] at h
      by_cases hl : l.size = 0
      · rw [size_zero l hl]
        rcases size_two r (by omega) with hr | hr
        · exact ⟨.a, by rw [hr]; rfl⟩
        · exact ⟨.b, by rw [hr]; rfl⟩
      · by_cases hl1 : l.size = 1
        · exact ⟨.c, by rw [size_one l hl1, size_one r (by omega)]; rfl⟩
        · rw [size_zero r (by omega)]
          rcases size_two l (by omega) with hr | hr
          · exact ⟨.d, by rw [hr]; rfl⟩
          · exact ⟨.e, by rw [hr]; rfl⟩

theorem shape_size (s : Shape) : s.tree.size = 3 := by cases s <;> rfl

theorem access_root (s t : Shape) (h : Access s.tree t.tree x k) : root t = x := by
  have hh := h.2
  cases t <;> exact hh

def decode (t : Tree) : Shape :=
  if t = Shape.a.tree then .a else
  if t = Shape.b.tree then .b else
  if t = Shape.c.tree then .c else
  if t = Shape.d.tree then .d else .e

theorem decode_shape (s : Shape) : decode s.tree = s := by
  cases s <;> decide

def induced (b : TreeAlgorithm) (s : Shape) (x : Nat) : Shape :=
  decode (b.step () s.tree x).2.1

theorem induced_step (b : TreeAlgorithm) (s : Shape) (x : Nat) (hx : x < 3) :
    (b.step () s.tree x).2.1 = (induced b s x).tree ∧
    root (induced b s x) = x ∧
    distance s (induced b s x) ≤ (b.step () s.tree x).2.2 := by
  have ha := b.correct () s.tree x (by rw [shape_size]; exact hx)
  have hs : (b.step () s.tree x).2.1.size = 3 := by
    rw [← ha.1.size_eq, shape_size]
  obtain ⟨u, hu⟩ := size_three _ hs
  have hi : induced b s x = u := by simp [induced, hu, decode_shape]
  rw [hu] at ha
  rw [hi]
  exact ⟨hu, access_root s u ha, distance_lower_bound s u ha.1⟩

theorem policy_two_blocks (p : Shape → Nat → Shape)
    (valid : ∀ s x, x < 3 → root (p s x) = x) :
    12 ≤ cost p .c [0, 2, 1] + cost p .c [0, 2, 0, 2, 1] := by
  have one : ∀ s, p s 1 = .c := by
    intro s
    have h := valid s 1 (by decide)
    cases he : p s 1 <;> simp_all [root]
  have hca := valid .c 0 (by decide)
  have ha2 := valid .a 2 (by decide)
  have hb2 := valid .b 2 (by decide)
  have hd0 := valid .d 0 (by decide)
  have he0 := valid .e 0 (by decide)
  generalize hca' : p .c 0 = ca at *
  generalize ha2' : p .a 2 = a2 at *
  generalize hb2' : p .b 2 = b2 at *
  generalize hd0' : p .d 0 = d0 at *
  generalize he0' : p .e 0 = e0 at *
  cases ca <;> simp [root] at hca <;> try contradiction
  all_goals cases a2 <;> simp [root] at ha2 <;> try contradiction
  all_goals cases b2 <;> simp [root] at hb2 <;> try contradiction
  all_goals cases d0 <;> simp [root] at hd0 <;> try contradiction
  all_goals cases e0 <;> simp [root] at he0 <;> try contradiction
  all_goals simp [cost, hca', ha2', hb2', hd0', he0', one, distance]

def finish (p : Shape → Nat → Shape) : Shape → List Nat → Shape
  | t, [] => t
  | t, x :: xs => finish p (p t x) xs

theorem finite_run (b : TreeAlgorithm) (s : Shape) (xs : List Nat)
    (hv : ∀ x ∈ xs, x < 3) :
    (b.runFrom () s.tree xs).2.1 = (finish (induced b) s xs).tree ∧
    cost (induced b) s xs ≤ (b.runFrom () s.tree xs).2.2 := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
      have hx := hv x (by simp)
      obtain ⟨ht, _, hk⟩ := induced_step b s x hx
      have hi := ih (induced b s x) (by intro y hy; exact hv y (by simp [hy]))
      rcases he : b.step () s.tree x with ⟨q, u, k⟩
      cases q
      rw [he] at ht hk
      dsimp only at ht hk
      simp only [StatefulAlgorithm.runFrom, he, ht, finish, cost]
      exact ⟨hi.1, Nat.add_le_add hk hi.2⟩

def period : List Nat := [0, 2, 1, 0, 2, 0, 2, 1]

def repetitions : Nat → List Nat
  | 0 => []
  | n + 1 => period ++ repetitions n

theorem finish_append (p : Shape → Nat → Shape) (s : Shape) (xs ys : List Nat) :
    finish p s (xs ++ ys) = finish p (finish p s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (p s x)

theorem cost_append (p : Shape → Nat → Shape) (s : Shape) (xs ys : List Nat) :
    cost p s (xs ++ ys) = cost p s xs + cost p (finish p s xs) ys := by
  induction xs generalizing s with
  | nil => simp [cost, finish]
  | cons x xs ih => simp [cost, finish, ih, Nat.add_assoc]

theorem resets (p : Shape → Nat → Shape)
    (valid : ∀ s x, x < 3 → root (p s x) = x) : ∀ s, p s 1 = .c := by
  intro s
  have h := valid s 1 (by decide)
  cases he : p s 1 <;> simp_all [root]

theorem period_lower (p : Shape → Nat → Shape)
    (valid : ∀ s x, x < 3 → root (p s x) = x) :
    12 ≤ cost p .c period ∧ finish p .c period = .c := by
  have hr := resets p valid
  have hc := policy_two_blocks p valid
  constructor
  · change 12 ≤ cost p .c ([0, 2, 1] ++ [0, 2, 0, 2, 1])
    rw [cost_append]
    simpa only [finish, hr] using hc
  · simp [period, finish, hr]

theorem repetitions_lower (p : Shape → Nat → Shape)
    (valid : ∀ s x, x < 3 → root (p s x) = x) (m : Nat) :
    12 * m ≤ cost p .c (repetitions m) := by
  obtain ⟨hc, hf⟩ := period_lower p valid
  induction m with
  | zero => simp [repetitions, cost]
  | succ m ih =>
      rw [repetitions, cost_append, hf, Nat.mul_succ]
      omega

theorem repetitions_valid (m : Nat) : ∀ x ∈ repetitions m, x < 3 := by
  induction m with
  | zero => simp [repetitions]
  | succ m ih =>
      intro x hx
      simp only [repetitions, List.mem_append] at hx
      rcases hx with hx | hx
      · simp only [period, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega
      · exact ih x hx

theorem repetitions_length (m : Nat) : (repetitions m).length = 8 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [repetitions, period, ih, Nat.mul_succ]

theorem tree_only_lower (b : TreeAlgorithm) (m : Nat) :
    20 * m ≤ b.totalCost Shape.c.tree (repetitions m) := by
  have valid : ∀ s x, x < 3 → root (induced b s x) = x :=
    fun s x hx => (induced_step b s x hx).2.1
  have h1 := repetitions_lower (induced b) valid m
  have h2 := (finite_run b .c (repetitions m) (repetitions_valid m)).2
  unfold StatefulAlgorithm.totalCost
  have hi : b.init Shape.c.tree = () := Subsingleton.elim _ _
  rw [hi, repetitions_length]
  omega

structure Plan where
  source : Shape
  request : Nat
  target : Shape
  rotations : Nat

def plan (q : Fin 8) : Plan := match q.val with
  | 0 => ⟨.c, 0, .a, 1⟩
  | 1 => ⟨.a, 2, .e, 2⟩
  | 2 => ⟨.e, 1, .c, 1⟩
  | 3 => ⟨.c, 0, .b, 2⟩
  | 4 => ⟨.b, 2, .d, 1⟩
  | 5 => ⟨.d, 0, .b, 1⟩
  | 6 => ⟨.b, 2, .d, 1⟩
  | _ => ⟨.d, 1, .c, 2⟩

theorem plan_correct (q : Fin 8) :
    Access (plan q).source.tree (plan q).target.tree (plan q).request (plan q).rotations := by
  rcases q with ⟨q, hq⟩
  have cases_q : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
  rcases cases_q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  · exact .step .right .refl
  · rfl
  · exact .step .left (.step .left .refl)
  · rfl
  · exact .step .right .refl
  · rfl
  · exact .step .right (.step (.inRight .left) .refl)
  · rfl
  · exact .step .left .refl
  · rfl
  · exact .step .right .refl
  · rfl
  · exact .step .left .refl
  · rfl
  · exact .step (.inLeft .left) (.step .right .refl)
  · rfl

/-- One fixed online algorithm. A clock selects a preprogrammed legal action;
on every unexpected tree or request, a correct fallback serves the request. -/
def clockAlgorithm : StatefulAlgorithm (Fin 8) where
  init _ := 0
  step q t x :=
    if t = (plan q).source.tree ∧ x = (plan q).request then
      (⟨(q.val + 1) % 8, Nat.mod_lt _ (by decide)⟩, (plan q).target.tree, (plan q).rotations)
    else (0, moveToRoot t x)
  correct q t x hx := by
    split
    next h => obtain ⟨rfl, rfl⟩ := h; exact plan_correct q
    next => exact (moveToRoot_correct t x hx).1

theorem clock_period : clockAlgorithm.runFrom 0 Shape.c.tree period =
    (0, Shape.c.tree, 11) := by decide

theorem run_append (a : StatefulAlgorithm σ) (q : σ) (t : Tree) (xs ys : List Nat) :
    a.runFrom q t (xs ++ ys) =
      let r := a.runFrom q t xs
      let z := a.runFrom r.1 r.2.1 ys
      (z.1, z.2.1, r.2.2 + z.2.2) := by
  induction xs generalizing q t with
  | nil => simp [StatefulAlgorithm.runFrom]
  | cons x xs ih => simp [StatefulAlgorithm.runFrom, ih, Nat.add_assoc]

theorem clock_repetitions (m : Nat) :
    clockAlgorithm.runFrom 0 Shape.c.tree (repetitions m) = (0, Shape.c.tree, 11 * m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [repetitions, run_append, clock_period, ih, Nat.mul_succ, Nat.add_comm]

theorem clock_cost (m : Nat) : clockAlgorithm.totalCost Shape.c.tree (repetitions m) = 19 * m := by
  unfold StatefulAlgorithm.totalCost
  change (repetitions m).length + (clockAlgorithm.runFrom 0 Shape.c.tree (repetitions m)).2.2 = _
  rw [repetitions_length, clock_repetitions]
  dsimp only
  omega

/-- No sequence-length-independent additive allowance suffices at factor one.
The SAME online stateful algorithm and repeated word defeat EVERY tree-only rule. -/
theorem no_purely_additive_simulation (b : TreeAlgorithm) (f : Nat → Nat) :
    ∃ t xs, ValidInput t xs ∧
      clockAlgorithm.totalCost t xs + f t.size < b.totalCost t xs := by
  let m := f 3 + 1
  refine ⟨Shape.c.tree, repetitions m, ?_, ?_⟩
  · intro x hx
    rw [shape_size]
    exact repetitions_valid m x hx
  · have hl := tree_only_lower b m
    rw [clock_cost, shape_size]
    dsimp [m] at *
    omega

/-- info: 'RotationBST.ThreeKey.no_purely_additive_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_purely_additive_simulation

end RotationBST.ThreeKey
