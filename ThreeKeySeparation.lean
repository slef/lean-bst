import StateElimination

/-! A finite certificate for the purely additive (factor-one) question.
The bridge from these five-state calculations to arbitrary `TreeAlgorithm`
is developed separately; do not read the certificate alone as that theorem. -/
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

end RotationBST.ThreeKey
