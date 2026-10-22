import StateElimination

/-! A sufficient potential criterion for state elimination with an arbitrary
additive function of n. The criterion is proved; a potential satisfying it for
every stateful algorithm is NOT supplied or assumed. -/
namespace RotationBST

/-- Relax the desired linear additive allowance to any function of tree size.
The multiplicative coefficient remains independent of tree size and input. -/
def StateEliminationWithAdditive : Prop :=
  ∀ (σ : Type) (a : StatefulAlgorithm σ), ∃ b : TreeAlgorithm,
    ∃ C : Nat, ∃ f : Nat → Nat, ∀ t xs, ValidInput t xs →
      b.totalCost t xs ≤ C * a.totalCost t xs + f t.size

theorem linear_implies_arbitrary_additive (h : StateElimination) :
    StateEliminationWithAdditive := by
  intro σ a
  obtain ⟨b, C, D, hb⟩ := h σ a
  exact ⟨b, C, fun n => D * n, hb⟩

/-- Potential is proof bookkeeping only: B's decisions still depend solely on
its own tree and the request, even though the proof can inspect A's state. -/
def SimulationPotential (a : StatefulAlgorithm σ) (b : TreeAlgorithm)
    (C : Nat) (potential : σ → Tree → Tree → Nat) : Prop :=
  ∀ q s t x, s.size = t.size → x < s.size →
    1 + (b.step () t x).2.2 +
        potential (a.step q s x).1 (a.step q s x).2.1 (b.step () t x).2.1 ≤
      C * (1 + (a.step q s x).2.2) + potential q s t

theorem potential_run_bound (a : StatefulAlgorithm σ) (b : TreeAlgorithm)
    (C : Nat) (potential : σ → Tree → Tree → Nat)
    (hp : SimulationPotential a b C potential)
    (q : σ) (s t : Tree) (hs : s.size = t.size)
    (xs : List Nat) (hv : ValidInput s xs) :
    xs.length + (b.runFrom () t xs).2.2 ≤
      C * (xs.length + (a.runFrom q s xs).2.2) + potential q s t := by
  induction xs generalizing q s t with
  | nil => simp [StatefulAlgorithm.runFrom]
  | cons x xs ih =>
      have hx := hv x (by simp)
      have ha := a.correct q s x hx
      have hb := b.correct () t x (by omega)
      have hstep := hp q s t x hs hx
      rcases heA : a.step q s x with ⟨q', s', ka⟩
      rcases heB : b.step () t x with ⟨u, t', kb⟩
      cases u
      rw [heA] at ha
      rw [heB] at hb
      rw [heA, heB] at hstep
      have hsa : s.size = s'.size := ha.1.size_eq
      have htb : t.size = t'.size := hb.1.size_eq
      have hv' : ValidInput s' xs := by
        intro y hy
        rw [← hsa]
        exact hv y (by simp [hy])
      have hi := ih q' s' t' (by omega) hv'
      rcases hrA : a.runFrom q' s' xs with ⟨q'', s'', ma⟩
      rcases hrB : b.runFrom () t' xs with ⟨u', t'', mb⟩
      rw [hrA, hrB] at hi
      simp only [StatefulAlgorithm.runFrom, heA, heB, hrA, hrB, List.length_cons,
        Nat.mul_add] at *
      omega

/-- Any uniform bound on the initial potential becomes the additive allowance.
Taking f(n)=D*n would establish the user's preferred form for this A and B. -/
theorem potential_total_bound (a : StatefulAlgorithm σ) (b : TreeAlgorithm)
    (C : Nat) (f : Nat → Nat) (potential : σ → Tree → Tree → Nat)
    (hp : SimulationPotential a b C potential)
    (initial : ∀ t, potential (a.init t) t t ≤ f t.size)
    (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    b.totalCost t xs ≤ C * a.totalCost t xs + f t.size := by
  have h := potential_run_bound a b C potential hp (a.init t) t t rfl xs hv
  have hb : b.init t = () := Subsingleton.elim _ _
  unfold StatefulAlgorithm.totalCost
  rw [hb]
  exact Nat.le_trans h (Nat.add_le_add_left (initial t) _)

/-- info: 'RotationBST.potential_total_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms potential_total_bound

end RotationBST
