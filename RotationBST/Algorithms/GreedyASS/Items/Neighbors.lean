module

public import RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract
public import RotationBST.Models.Geometric.Offline.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

theorem greatest_some (s : Finset Nat) (x : Nat) :
    greatest s = some x ↔ x ∈ s ∧ ∀ y ∈ s, y ≤ x := by
  unfold greatest
  split
  · simpa only [Option.some.injEq] using Finset.max'_eq_iff s _ x
  · constructor
    · simp
    · rintro ⟨member, _⟩
      exact (by assumption : ¬ s.Nonempty) ⟨x, member⟩ |>.elim

theorem least_some (s : Finset Nat) (x : Nat) :
    least s = some x ↔ x ∈ s ∧ ∀ y ∈ s, x ≤ y := by
  unfold least
  split
  · simpa only [Option.some.injEq] using Finset.min'_eq_iff s _ x
  · constructor
    · simp
    · rintro ⟨member, _⟩
      exact (by assumption : ¬ s.Nonempty) ⟨x, member⟩ |>.elim

theorem greatest_none (s : Finset Nat) : greatest s = none ↔ s = ∅ := by
  simp [greatest, Finset.not_nonempty_iff_eq_empty]

theorem least_none (s : Finset Nat) : least s = none ↔ s = ∅ := by
  simp [least, Finset.not_nonempty_iff_eq_empty]

theorem mem_times (P : Finset Point) (key stamp : Nat) : stamp ∈ times P key ↔ (key, stamp) ∈ P := by
  constructor
  · intro member
    obtain ⟨p, hp, time⟩ := Finset.mem_image.mp member
    obtain ⟨hp, coord⟩ := Finset.mem_filter.mp hp
    have eq : p = (key, stamp) := Prod.ext coord time
    simpa only [eq] using hp
  · intro member
    exact Finset.mem_image.mpr ⟨(key, stamp), Finset.mem_filter.mpr ⟨member, rfl⟩, rfl⟩

/-- The executable latest-time query identifies exactly the active point. -/
theorem latest_spec (P : Finset Point) (key stamp : Nat) :
    latest P key = some stamp ↔ Active P (key, stamp) := by
  rw [latest, greatest_some]
  constructor
  · rintro ⟨member, greatest⟩
    refine ⟨(mem_times P key stamp).mp member, ?_⟩
    intro p hp eq
    apply greatest p.2
    apply (mem_times P key p.2).mpr
    have coord : p.1 = key := eq
    have pair : p = (key, p.2) := Prod.ext coord rfl
    simpa only [← pair] using hp
  · rintro ⟨member, active⟩
    exact ⟨(mem_times P key stamp).mpr member,
      fun time ht => active (key, time) ((mem_times P key time).mp ht) rfl⟩

theorem left_spec (P : Finset Point) (q : Point) (key : Nat) :
    leftNeighbor P q = some key ↔
      (key, q.2) ∈ P ∧ key < q.1 ∧
        ∀ x, (x, q.2) ∈ P → x < q.1 → x ≤ key := by
  simp only [leftNeighbor, greatest_some, Finset.mem_filter, mem_keysAt]
  aesop

theorem right_spec (P : Finset Point) (q : Point) (key : Nat) :
    rightNeighbor P q = some key ↔
      (key, q.2) ∈ P ∧ q.1 < key ∧
        ∀ x, (x, q.2) ∈ P → q.1 < x → key ≤ x := by
  simp only [rightNeighbor, least_some, Finset.mem_filter, mem_keysAt]
  aesop

/-- For active points, missing row neighbors are precisely externality. -/
theorem left_none {P : Finset Point} {q : Point} (active : Active P q) :
    leftNeighbor P q = none ↔ LeftExternal P q := by
  rw [leftNeighbor, greatest_none, Finset.filter_eq_empty_iff]
  simp only [mem_keysAt]
  constructor
  · intro missing
    refine ⟨active, ?_⟩
    intro p hp same
    have member : (p.1, q.2) ∈ P := by simpa only [← same, Prod.eta] using hp
    have := missing member
    omega
  · intro external x member
    have := external.2 (x, q.2) member rfl
    omega

theorem right_none {P : Finset Point} {q : Point} (active : Active P q) :
    rightNeighbor P q = none ↔ RightExternal P q := by
  rw [rightNeighbor, least_none, Finset.filter_eq_empty_iff]
  simp only [mem_keysAt]
  constructor
  · intro missing
    refine ⟨active, ?_⟩
    intro p hp same
    have member : (p.1, q.2) ∈ P := by simpa only [← same, Prod.eta] using hp
    have := missing member
    omega
  · intro external x member
    have := external.2 (x, q.2) member rfl
    omega

theorem neighbors_exist {P : Finset Point} {q : Point} (active : Active P q)
    (notExternal : ¬ External P q) :
    ∃ l r, leftNeighbor P q = some l ∧ rightNeighbor P q = some r := by
  cases left : leftNeighbor P q with
  | none => exact (notExternal (Or.inl ((left_none active).mp left))).elim
  | some l =>
    cases right : rightNeighbor P q with
    | none => exact (notExternal (Or.inr ((right_none active).mp right))).elim
    | some r => exact ⟨l, r, rfl, rfl⟩

end RotationBST.Geometric.GreedyASS.Items
