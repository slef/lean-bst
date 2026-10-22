import RotationBST

/-!
# Stateful versus tree-only BST algorithms

Costs in this file include one unit per request, in addition to rotations.
`StateElimination` is the research target, not an asserted theorem.

Proved: constructive access existence; an n-factor tree-only baseline;
exact erasure for recoverable private state; and a conditional implication
from a universally competitive tree-only algorithm. None establishes the
uniform constant-factor theorem, and no counterexample to it is claimed.
-/
namespace RotationBST

/-- Private state is initialized from the initial tree, never from future requests. -/
structure StatefulAlgorithm (σ : Type) where
  init : Tree → σ
  step : σ → Tree → Nat → σ × Tree × Nat
  correct : ∀ q t x, x < t.size →
    Access t (step q t x).2.1 x (step q t x).2.2

/-- The original history-based interface is a special case of private state. -/
def Algorithm.withHistory (a : Algorithm) : StatefulAlgorithm (List Nat) where
  init _ := []
  step past t x := (past ++ [x], a.step past t x)
  correct past t x hx := a.correct past t x hx

/-- The only persistent memory is the current tree. -/
abbrev TreeAlgorithm := StatefulAlgorithm Unit

def StatefulAlgorithm.runFrom (a : StatefulAlgorithm σ) (q : σ) (t : Tree) :
    List Nat → σ × Tree × Nat
  | [] => (q, t, 0)
  | x :: xs =>
      let (q', u, k) := a.step q t x
      let (q'', v, m) := a.runFrom q' u xs
      (q'', v, k + m)

/-- History-based and explicit-state execution agree exactly. -/
theorem Algorithm.withHistory_runFrom (a : Algorithm) (past : List Nat)
    (t : Tree) (xs : List Nat) :
    (a.withHistory.runFrom past t xs).2 = a.runFrom past t xs := by
  induction xs generalizing past t with
  | nil => rfl
  | cons x xs ih =>
      rcases he : a.step past t x with ⟨u, k⟩
      simpa only [StatefulAlgorithm.runFrom, Algorithm.runFrom, Algorithm.withHistory, he] using
        congrArg (fun r : Tree × Nat => (r.1, k + r.2)) (ih (past ++ [x]) u)

def StatefulAlgorithm.totalCost (a : StatefulAlgorithm σ) (t : Tree) (xs : List Nat) : Nat :=
  xs.length + (a.runFrom (a.init t) t xs).2.2

def ValidInput (t : Tree) (xs : List Nat) : Prop := ∀ x ∈ xs, x < t.size

/-- Constants may depend on A, but are uniform in the tree size and input.
The simulator starts at the same tree and cannot depend on the future input. -/
def StateElimination : Prop :=
  ∀ (σ : Type) (a : StatefulAlgorithm σ), ∃ b : TreeAlgorithm, ∃ C D : Nat,
    ∀ t xs, ValidInput t xs → b.totalCost t xs ≤ C * a.totalCost t xs + D * t.size

namespace Rotations

theorem append (h : Rotations s t k) (g : Rotations t u m) : Rotations s u (k + m) := by
  induction h with
  | refl => simpa using g
  | step h _ ih => simpa only [Nat.add_assoc, Nat.add_comm 1 m] using Rotations.step h (ih g)

theorem inLeft (h : Rotations s t k) : Rotations (.node s r) (.node t r) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (.inLeft h) ih

theorem inRight (h : Rotations s t k) : Rotations (.node l s) (.node l t) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (.inRight h) ih

end Rotations

/-- Recursively expose x in its child subtree, then rotate it one level up.
Out-of-range inputs have arbitrary behavior; correctness is required only in range. -/
def moveToRoot : Tree → Nat → Tree × Nat
  | .nil, _ => (.nil, 0)
  | .node l r, x =>
      if x < l.size then
        let (u, k) := moveToRoot l x
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node a (.node b r), k + 1)
      else if x = l.size then (.node l r, 0)
      else
        let (u, k) := moveToRoot r (x - l.size - 1)
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node (.node l a) b, k + 1)

theorem moveToRoot_correct (t : Tree) (x : Nat) (hx : x < t.size) :
    Access t (moveToRoot t x).1 x (moveToRoot t x).2 ∧ (moveToRoot t x).2 < t.size := by
  induction t generalizing x with
  | nil => simp only [Tree.size] at hx; omega
  | node l r il ir =>
      by_cases hl : x < l.size
      · obtain ⟨ha, hk⟩ := il x hl
        rcases he : moveToRoot l x with ⟨u, k⟩
        rw [he] at ha hk
        cases u with
        | nil => exact ha.2.elim
        | node a b =>
            have hrun : Rotations (.node l r) (.node a (.node b r)) (k + 1) :=
              ha.1.inLeft.append (.step .right .refl)
            simp only [moveToRoot, if_pos hl, he]
            exact ⟨⟨hrun, ha.2⟩, by simp only [Tree.size]; omega⟩
      · by_cases heq : x = l.size
        · simp only [moveToRoot, if_neg hl, if_pos heq]
          exact ⟨⟨.refl, heq.symm⟩, by simp only [Tree.size]; omega⟩
        · have hr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
          obtain ⟨ha, hk⟩ := ir (x - l.size - 1) hr
          rcases he : moveToRoot r (x - l.size - 1) with ⟨u, k⟩
          rw [he] at ha hk
          cases u with
          | nil => exact ha.2.elim
          | node a b =>
              have hrun : Rotations (.node l r) (.node (.node l a) b) (k + 1) :=
                ha.1.inRight.append (.step .left .refl)
              simp only [moveToRoot, if_neg hl, if_neg heq, he]
              refine ⟨⟨hrun, ?_⟩, ?_⟩
              · have hf : a.size = x - l.size - 1 := ha.2
                simp only [Tree.size]
                omega
              · simp only [Tree.size]; omega

/-- A concrete tree-only algorithm: fewer than n rotations per valid access. -/
def moveToRootAlgorithm : TreeAlgorithm where
  init _ := ()
  step _ t x := ((), moveToRoot t x)
  correct _ t x hx := (moveToRoot_correct t x hx).1

/-- The tree-only baseline serves every valid request. -/
theorem access_exists (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ u k, Access t u x k ∧ k < t.size :=
  ⟨_, _, moveToRoot_correct t x hx⟩

namespace StatefulAlgorithm

theorem execution (a : StatefulAlgorithm σ) (q : σ) (t : Tree) (xs : List Nat)
    (hv : ValidInput t xs) :
    Execution t xs (a.runFrom q t xs).2.1 (a.runFrom q t xs).2.2 := by
  induction xs generalizing q t with
  | nil => exact .nil
  | cons x xs ih =>
      have hx := hv x (by simp)
      have ha := a.correct q t x hx
      have ht := ha.1.size_eq
      have hr : ValidInput (a.step q t x).2.1 xs := by
        intro y hy
        rw [← ht]
        exact hv y (by simp [hy])
      exact .cons ha (ih (a.step q t x).1 (a.step q t x).2.1 hr)

/-- A per-access bound telescopes because accesses preserve the key universe. -/
theorem runFrom_bound (a : StatefulAlgorithm σ) (f : Nat → Nat)
    (bound : ∀ q t x, x < t.size → 1 + (a.step q t x).2.2 ≤ f t.size)
    (q : σ) (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    xs.length + (a.runFrom q t xs).2.2 ≤ xs.length * f t.size := by
  induction xs generalizing q t with
  | nil => simp [runFrom]
  | cons x xs ih =>
      have hx := hv x (by simp)
      have ha := a.correct q t x hx
      have hb := bound q t x hx
      rcases he : a.step q t x with ⟨q', u, k⟩
      rw [he] at ha hb
      have hs : t.size = u.size := ha.1.size_eq
      have hr : ValidInput u xs := by
        intro y hy
        rw [← hs]
        exact hv y (by simp [hy])
      have hi := ih q' u hr
      rw [← hs] at hi
      rcases hr : a.runFrom q' u xs with ⟨q'', v, m⟩
      rw [hr] at hi
      simp only [runFrom, he, hr, List.length_cons, Nat.succ_mul]
      dsimp only at hb hi ⊢
      omega

/-- Use a state reconstructed from the current tree, then forget the next state. -/
def erase (a : StatefulAlgorithm σ) (recover : Tree → σ) : TreeAlgorithm where
  init _ := ()
  step _ t x := ((), (a.step (recover t) t x).2)
  correct _ t x hx := a.correct (recover t) t x hx

/-- Exact elimination when the private state is recoverable and this invariant
is maintained by each valid step. No finite-state assumption is needed. -/
theorem erase_runFrom (a : StatefulAlgorithm σ) (recover : Tree → σ)
    (preserves : ∀ t x, x < t.size →
      (a.step (recover t) t x).1 = recover (a.step (recover t) t x).2.1)
    (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    ((a.erase recover).runFrom () t xs).2 = (a.runFrom (recover t) t xs).2 := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
      have hx := hv x (by simp)
      have ha := a.correct (recover t) t x hx
      have hp := preserves t x hx
      rcases he : a.step (recover t) t x with ⟨q', u, k⟩
      rw [he] at ha hp
      have hs : t.size = u.size := ha.1.size_eq
      have hr : ValidInput u xs := by
        intro y hy
        rw [← hs]
        exact hv y (by simp [hy])
      have hi := ih u hr
      simpa only [runFrom, erase, he, hp] using
        congrArg (fun r : Tree × Nat => (r.1, k + r.2)) hi

theorem erase_totalCost (a : StatefulAlgorithm σ) (recover : Tree → σ)
    (initial : ∀ t, a.init t = recover t)
    (preserves : ∀ t x, x < t.size →
      (a.step (recover t) t x).1 = recover (a.step (recover t) t x).2.1)
    (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    (a.erase recover).totalCost t xs = a.totalCost t xs := by
  unfold totalCost
  rw [initial t]
  exact congrArg (fun r : Tree × Nat => xs.length + r.2)
    (a.erase_runFrom recover preserves t xs hv)

end StatefulAlgorithm

/-- The constructive baseline has total cost at most n times the request count. -/
theorem moveToRoot_totalCost_le (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    moveToRootAlgorithm.totalCost t xs ≤ xs.length * t.size := by
  apply StatefulAlgorithm.runFrom_bound moveToRootAlgorithm id ?_ () t xs hv
  intro q u x hx
  have hk := (moveToRoot_correct u x hx).2
  change 1 + (moveToRoot u x).2 ≤ u.size
  omega

/-- A size-dependent simulation is easy. The requested constant-factor theorem
must remove this factor n; it is NOT proved by this result. -/
theorem size_factor_simulation (a : StatefulAlgorithm σ) (t : Tree) (xs : List Nat)
    (hv : ValidInput t xs) :
    moveToRootAlgorithm.totalCost t xs ≤ t.size * a.totalCost t xs := by
  apply Nat.le_trans (moveToRoot_totalCost_le t xs hv)
  unfold StatefulAlgorithm.totalCost
  calc
    xs.length * t.size ≤ (xs.length + (a.runFrom (a.init t) t xs).2.2) * t.size :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    _ = t.size * (xs.length + (a.runFrom (a.init t) t xs).2.2) := Nat.mul_comm _ _

/-- A single tree-only algorithm competitive with every offline execution. -/
def UniversallyCompetitive (b : TreeAlgorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs u k, Execution t xs u k →
    b.totalCost t xs ≤ C * (xs.length + k) + D * t.size

/-- A universally competitive tree-only algorithm would settle state elimination.
This theorem does not supply such an algorithm. -/
theorem stateElimination_of_universal
    (h : ∃ b : TreeAlgorithm, UniversallyCompetitive b) : StateElimination := by
  obtain ⟨b, C, D, hc⟩ := h
  intro σ a
  refine ⟨b, C, D, ?_⟩
  intro t xs hv
  exact hc t xs _ _ (a.execution (a.init t) t xs hv)

end RotationBST
