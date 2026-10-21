import CompetitiveCredit
import SimulationPotential

/-! Normalize an arbitrary additive allowance to O(n) for a tree-only algorithm
ALREADY competitive against all offline executions. This is a conditional
transformation; it does not construct a dynamically optimal algorithm. -/
namespace RotationBST

structure CreditCertificate (b : TreeAlgorithm) (C : Nat) where
  value : Tree → Tree → Nat
  seed : Nat → Tree
  anchor : Nat → Tree
  seed_size : ∀ n, (seed n).size = n
  anchor_size : ∀ n, (anchor n).size = n
  zero : ∀ n, value (seed n) (anchor n) = 0
  variation : ∀ s t u, s.size = t.size → s.size = u.size →
    value s t ≤ value s u + C * (2 * s.size)
  oneStep : ∀ s t u x k, s.size = t.size → Access t u x k →
    1 + (b.step () s x).2.2 + value (b.step () s x).2.1 u ≤
      C * (1 + k) + value s t

theorem spine_size (n : Nat) (t : Tree) : (spine n t).size = n + t.size := by
  induction n with
  | zero => simp [spine]
  | succ n ih => simp [spine, Tree.size, ih, Nat.add_assoc, Nat.add_left_comm]

noncomputable def certificateOfCompetitive (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) : CreditCertificate b C := by
  have pairs : ∀ n, ∃ p : Tree × Tree,
      p.1.size = n ∧ p.2.size = n ∧ credit b C f h p.1 p.2 = 0 := by
    intro n
    obtain ⟨s, t, hs, ht, hz⟩ := zero_credit_pair b C f h (spine n .nil)
    refine ⟨(s, t), ?_, ?_, hz⟩
    · simpa [spine_size, Tree.size] using hs
    · simpa [spine_size, Tree.size] using ht
  exact {
    value := credit b C f h
    seed := fun n => (Classical.choose (pairs n)).1
    anchor := fun n => (Classical.choose (pairs n)).2
    seed_size := fun n => (Classical.choose_spec (pairs n)).1
    anchor_size := fun n => (Classical.choose_spec (pairs n)).2.1
    zero := fun n => (Classical.choose_spec (pairs n)).2.2
    variation := credit_lipschitz b C f h
    oneStep := fun s t u _ _ hs ha => credit_step b C f h s t u hs ha
  }

namespace CreditCertificate

variable {b : TreeAlgorithm} {C : Nat} (d : CreditCertificate b C)

def low (s : Tree) : Prop :=
  d.value s (d.anchor s.size) ≤ 2 * s.size + 2 * (C * (2 * s.size))

noncomputable def potential (s t : Tree) : Nat := by
  classical
  exact if d.low s then d.value s t else 2 * s.size + d.value (d.seed s.size) t

theorem seed_bound (s t : Tree) (hs : s.size = t.size) :
    d.value (d.seed s.size) t ≤ C * (2 * s.size) := by
  have h := d.variation (d.seed s.size) t (d.anchor s.size)
    (by rw [d.seed_size, hs]) (by rw [d.seed_size, d.anchor_size])
  simpa only [d.seed_size, d.zero, Nat.zero_add] using h

theorem potential_le (s t : Tree) (hs : s.size = t.size) :
    d.potential s t ≤ d.value s t := by
  classical
  by_cases hl : d.low s
  · simp [potential, hl]
  · have hv := d.variation s (d.anchor s.size) t (d.anchor_size s.size).symm hs
    have hb := d.seed_bound s t hs
    simp only [low] at hl
    simp only [potential, if_neg (show ¬d.low s from hl)]
    omega

theorem potential_bounded (s t : Tree) (hs : s.size = t.size) :
    d.potential s t ≤ 2 * s.size + 3 * (C * (2 * s.size)) := by
  classical
  by_cases hl : d.low s
  · have hv := d.variation s t (d.anchor s.size) hs (d.anchor_size s.size).symm
    simp only [potential, if_pos hl]
    simp only [low] at hl
    omega
  · have hb := d.seed_bound s t hs
    simp only [potential, if_neg hl]
    omega

noncomputable def resetCount (s : Tree) : Nat :=
  Classical.choose (reset_linear s (d.seed s.size) (d.seed_size s.size).symm)

theorem resetCount_spec (s : Tree) :
    d.resetCount s ≤ 2 * s.size ∧ Rotations s (d.seed s.size) (d.resetCount s) :=
  Classical.choose_spec (reset_linear s (d.seed s.size) (d.seed_size s.size).symm)

/-- A reset decision made entirely from the current tree. No clock or persistent
private state is introduced. -/
noncomputable def normalized : TreeAlgorithm := by
  classical
  exact {
    init := fun _ => ()
    step := fun _ s x => if d.low s then b.step () s x else
      ((), (b.step () (d.seed s.size) x).2.1,
        d.resetCount s + (b.step () (d.seed s.size) x).2.2)
    correct := by
      intro q s x hx
      split
      next => exact b.correct () s x hx
      next =>
        have ha := b.correct () (d.seed s.size) x (by rw [d.seed_size]; exact hx)
        exact ⟨(d.resetCount_spec s).2.append ha.1, ha.2⟩
  }

theorem normalized_step (s t u : Tree) (hs : s.size = t.size) (ha : Access t u x k) :
    1 + (d.normalized.step () s x).2.2 +
        d.potential (d.normalized.step () s x).2.1 u ≤
      C * (1 + k) + d.potential s t := by
  classical
  have hx : x < s.size := by rw [hs]; exact ha.in_range
  by_cases hl : d.low s
  · have hb := b.correct () s x hx
    have hsz : (b.step () s x).2.1.size = u.size := by
      rw [← hb.1.size_eq, hs, ha.1.size_eq]
    have hp := d.potential_le (b.step () s x).2.1 u hsz
    have hc := d.oneStep s t u x k hs ha
    have hcurrent : d.potential s t = d.value s t := by simp [potential, hl]
    rw [hcurrent]
    simp only [normalized, if_pos hl]
    change 1 + (b.step () s x).2.2 + d.potential (b.step () s x).2.1 u ≤ _
    omega
  · have hb := b.correct () (d.seed s.size) x (by rw [d.seed_size]; exact hx)
    have hsz : (b.step () (d.seed s.size) x).2.1.size = u.size := by
      rw [← hb.1.size_eq, d.seed_size, hs, ha.1.size_eq]
    have hp := d.potential_le (b.step () (d.seed s.size) x).2.1 u hsz
    have hc := d.oneStep (d.seed s.size) t u x k (by rw [d.seed_size, hs]) ha
    have hr := (d.resetCount_spec s).1
    simp only [normalized, if_neg hl]
    have hcurrent : d.potential s t = 2 * s.size + d.value (d.seed s.size) t := by
      simp [potential, hl]
    rw [hcurrent]
    omega

theorem normalized_execution (he : Execution t xs u k) (s : Tree)
    (hs : s.size = t.size) :
    d.normalized.totalCost s xs ≤ C * (xs.length + k) + d.potential s t := by
  induction he generalizing s with
  | nil => simp [StatefulAlgorithm.totalCost, StatefulAlgorithm.runFrom]
  | @cons t v x j xs u k ha ht ih =>
      have hx : x < s.size := by rw [hs]; exact ha.in_range
      have hb := d.normalized.correct () s x hx
      have hp := d.normalized_step s _ _ hs ha
      have hsize : (d.normalized.step () s x).2.1.size = v.size :=
        hb.1.size_eq.symm.trans (hs.trans ha.1.size_eq)
      have hi := ih (d.normalized.step () s x).2.1 hsize
      rw [treeOnly_cost_cons]
      simp only [List.length_cons, Nat.mul_add] at *
      omega

end CreditCertificate

/-- Arbitrary additive allowance can be reduced to a linear one, without
changing the competitive coefficient, for an already offline-competitive
tree-only algorithm. The transformation is noncomputable. -/
theorem normalize_additive (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) :
    ∃ b' : TreeAlgorithm, ∀ t xs u k, Execution t xs u k →
      b'.totalCost t xs ≤ C * (xs.length + k) + (2 + 6 * C) * t.size := by
  let d := certificateOfCompetitive b C f h
  refine ⟨d.normalized, ?_⟩
  intro t xs u k he
  have hb := d.normalized_execution he t rfl
  have hp := d.potential_bounded t t rfl
  have heq : 2 * t.size + 3 * (C * (2 * t.size)) = (2 + 6 * C) * t.size := by
    simp only [Nat.add_mul, Nat.mul_left_comm C 2, ← Nat.mul_assoc]
  rw [heq] at hp
  omega

/-- info: 'RotationBST.normalize_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalize_additive

end RotationBST
