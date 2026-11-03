module

public import RotationBST.Bounds.Interleave.Wilber.Normalization
public import RotationBST.Bounds.Interleave.Transition.Stability
public import RotationBST.Bounds.Interleave.Transition.Intervals
public import RotationBST.Bounds.Interleave.Basic

@[expose] public section
namespace RotationBST.Wilber
open Geometric

def primary (t : Tree) (low cut high : Nat) : Option Bool :=
  (topIn t 0 low high).map fun x => decide (x ≤ cut)

def mismatch (previous current : Option Bool) : Nat :=
  match previous, current with
  | some a, some b => if a = b then 0 else 1
  | _, _ => 0

def cutPotential (t : Tree) (past : List Nat) (low cut high : Nat) : Nat :=
  mismatch (labels low cut high past).getLast? (primary t low cut high)

theorem mismatch_le_one (a b : Option Bool) : mismatch a b ≤ 1 := by
  cases a <;> cases b <;> simp only [mismatch]
  · omega
  · omega
  · omega
  · split <;> omega

theorem primary_from_transition {t : Tree} {low cut high point : Nat}
    (h : transition t low cut high = some point) :
    primary t low cut high = some (!decide (point ≤ cut)) := by
  unfold transition at h
  cases ht : topIn t 0 low high with
  | none => simp only [ht] at h; contradiction
  | some root =>
    simp only [ht] at h
    by_cases side : root ≤ cut
    · rw [ite_eq_left side] at h
      have hb := topIn_bounds h
      have hp : ¬ point ≤ cut := by omega
      simp [primary, ht, side, hp]
    · rw [ite_eq_right side] at h
      have hb := topIn_bounds h
      have hp : point ≤ cut := by omega
      simp [primary, ht, side, hp]

theorem avoided_side {s : Region} {low cut high point x : Nat}
    (h : transition s.tree low cut high = some point)
    (untouched : point ∉ Region.keys s 0) (active : x ∈ Region.keys s 0)
    (lowx : low ≤ x) (xhigh : x < high) :
    primary s.tree low cut high = some (decide (x ≤ cut)) := by
  unfold transition at h
  cases ht : topIn s.tree 0 low high with
  | none => simp only [ht] at h; contradiction
  | some root =>
    simp only [ht] at h
    by_cases side : root ≤ cut
    · rw [ite_eq_left side] at h
      have hx : x ≤ cut := by
        by_contra hn
        exact untouched (topIn_active s 0 (cut + 1) high x point active (by omega) xhigh h)
      simp [primary, ht, side, hx]
    · rw [ite_eq_right side] at h
      have hx : ¬ x ≤ cut := by
        intro hx
        exact untouched (topIn_active s 0 low (cut + 1) x point active lowx (by omega) h)
      simp [primary, ht, side, hx]

private theorem labels_append (low cut high : Nat) (past : List Nat) (x : Nat) :
    labels low cut high (past ++ [x]) = labels low cut high past ++
      if low ≤ x ∧ x < high then [decide (x ≤ cut)] else [] := by
  by_cases hlo : low ≤ x <;> by_cases hhi : x < high <;> simp [labels, hlo, hhi]

/-- One interleave switch is paid by a drop of mismatch potential, unless the
operation touches the transition point. A touch pays for at most two units. -/
theorem cut_bound {s u : Region} {low cut high x : Nat}
    (same : Region.Same s u 0) (lower : low ≤ cut) (split : cut + 1 < high)
    (upper : high ≤ s.tree.size) (active : x ∈ Region.keys s 0)
    (past : List Nat) :
    alternations (labels low cut high (past ++ [x])) + cutPotential u.tree (past ++ [x]) low cut high ≤
      alternations (labels low cut high past) + cutPotential s.tree past low cut high +
      2 * (((transition s.tree low cut high).toList.filter
        fun key => decide (key ∈ Region.keys s 0)).length) := by
  obtain ⟨point, ht⟩ := transition_exists s.tree low cut high lower split upper
  by_cases touched : point ∈ Region.keys s 0
  · have hnew := mismatch_le_one (labels low cut high (past ++ [x])).getLast? (primary u.tree low cut high)
    have increment : alternations (labels low cut high (past ++ [x])) ≤
        alternations (labels low cut high past) + 1 := by
      rw [labels_append]
      split
      · rw [alternations_append]
        have := switch_le_one (labels low cut high past) (decide (x ≤ cut))
        omega
      · simp
    simp only [ht, Option.toList_some, List.filter_cons, decide_eq_true touched,
      ↓reduceIte, List.filter_nil, List.length_cons, List.length_nil] at ⊢
    unfold cutPotential at *
    omega
  · have ht' := transition_stable same lower split upper ht touched
    have hp : primary u.tree low cut high = primary s.tree low cut high := by
      rw [primary_from_transition ht, primary_from_transition ht']
    simp only [ht, Option.toList_some, List.filter_cons, decide_eq_false touched, Bool.false_eq_true,
      ↓reduceIte, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
    by_cases inside : low ≤ x ∧ x < high
    · have current := avoided_side ht touched active inside.1 inside.2
      unfold cutPotential
      rw [labels_append, ite_eq_left inside, alternations_append]
      rw [hp, current]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        mismatch, ite_true, Nat.add_zero]
      unfold switch
      cases (labels low cut high past).getLast? <;> simp
    · unfold cutPotential
      rw [labels_append, ite_eq_right inside, List.append_nil, hp]

end RotationBST.Wilber
