module

public import RotationBST.Bounds.Interleave.Wilber.Cut
public import RotationBST.Bounds.Interleave.Transition.Distinct

@[expose] public section
namespace RotationBST.Tango.Wilber
open Arboral

def potential : Tree → Nat → Tree → List Nat → Nat
  | .nil, _, _, _ => 0
  | .node l r, lo, actual, past =>
      (if r.size = 0 then 0 else cutPotential actual past lo (lo + l.size) (lo + l.size + 1 + r.size)) +
      potential l lo actual past + potential r (lo + l.size + 1) actual past

def charges (reference : Tree) (lo : Nat) (s : Region) : Nat :=
  ((transitionKeys reference lo s.tree).filter fun x => decide (x ∈ Arboral.Region.keys s 0)).length

private theorem uniform_alternations (xs : List Bool) (b : Bool) (all : ∀ x ∈ xs, x = b) :
    alternations xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := all a (List.mem_cons_self ..)
    have tail := ih (fun x hx => all x (List.mem_cons_of_mem _ hx))
    cases xs with
    | nil => rfl
    | cons c cs =>
      have hc := all c (by simp)
      simp only [alternations, ha, hc, ite_true, Nat.zero_add]
      simpa only [hc] using tail

private theorem no_right_alternations (lo left : Nat) (past : List Nat) :
    alternations (labels lo (lo + left) (lo + left + 1) past) = 0 := by
  apply uniform_alternations _ true
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  have hi := (List.mem_filter.mp hx).2
  have hb : lo ≤ x ∧ x < lo + left + 1 := by simpa using hi
  simp only [decide_eq_true_eq]
  omega

theorem potential_empty (reference : Tree) (lo : Nat) (actual : Tree) :
    potential reference lo actual [] = 0 := by
  induction reference generalizing lo with
  | nil => rfl
  | node l r il ir => simp [potential, cutPotential, labels, mismatch, il, ir]

theorem absolute_empty (reference : Tree) (lo : Nat) : absoluteInterleave reference lo [] = 0 := by
  induction reference generalizing lo with
  | nil => rfl
  | node l r il ir => simp [absoluteInterleave, labels, alternations, il, ir]

theorem charges_le (reference : Tree) (lo : Nat) (s : Region) : charges reference lo s ≤ s.size := by
  unfold charges
  have nd := (transitionKeys_nodup reference lo s.tree).filter
    (fun x => decide (x ∈ Arboral.Region.keys s 0))
  rw [← List.toFinset_card_of_nodup nd, ← Arboral.Region.keys_card s 0]
  apply Finset.card_le_card
  intro x hx
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hx)).2

theorem reference_step (reference : Tree) (lo : Nat) (past : List Nat)
    {s u : Region} {x : Nat} (same : Arboral.Region.Same s u 0)
    (upper : lo + reference.size ≤ s.tree.size) (active : x ∈ Arboral.Region.keys s 0) :
    absoluteInterleave reference lo (past ++ [x]) + potential reference lo u.tree (past ++ [x]) ≤
      absoluteInterleave reference lo past + potential reference lo s.tree past + 2 * charges reference lo s := by
  induction reference generalizing lo with
  | nil => simp [absoluteInterleave, potential, charges, transitionKeys]
  | node l r il ir =>
    have hl := il lo (by simp only [Tree.size] at upper; omega)
    have hr := ir (lo + l.size + 1) (by simp only [Tree.size] at upper; omega)
    have cut : alternations (labels lo (lo + l.size) (lo + l.size + 1 + r.size) (past ++ [x])) +
        (if r.size = 0 then 0 else cutPotential u.tree (past ++ [x]) lo (lo + l.size) (lo + l.size + 1 + r.size)) ≤
        alternations (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past) +
        (if r.size = 0 then 0 else cutPotential s.tree past lo (lo + l.size) (lo + l.size + 1 + r.size)) +
        2 * (((transition s.tree lo (lo + l.size) (lo + l.size + 1 + r.size)).toList.filter
          fun key => decide (key ∈ Arboral.Region.keys s 0)).length) := by
      by_cases empty : r.size = 0
      · simp only [empty, Nat.add_zero, ite_true, no_right_alternations, Nat.zero_add]
        omega
      · simp only [ite_eq_right empty]
        exact cut_bound same (by omega) (by omega) (by simp only [Tree.size] at upper; omega) active past
    simp only [absoluteInterleave, potential, charges, transitionKeys,
      List.filter_append, List.length_append] at ⊢
    unfold charges at hl hr
    omega

theorem amortized_step (reference : Tree) (lo : Nat) (past : List Nat)
    {s u : Region} {x : Nat} (same : Arboral.Region.Same s u 0)
    (upper : lo + reference.size ≤ s.tree.size) (active : x ∈ Arboral.Region.keys s 0) :
    absoluteInterleave reference lo (past ++ [x]) + potential reference lo u.tree (past ++ [x]) ≤
      absoluteInterleave reference lo past + potential reference lo s.tree past + 2 * s.size := by
  have := reference_step reference lo past same upper active
  have := charges_le reference lo s
  omega

end RotationBST.Tango.Wilber
