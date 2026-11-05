module

public import RotationBST.Algorithms.GreedyASS.Reference.Sides
public import RotationBST.Algorithms.GreedyASS.Barrier.Streams
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference

/-- Combine reference-forest persistence with the executable sweep barrier.
Once a component has an access, later accesses cannot go beyond that access
on the side opposite the searches, while it remains an unsearched component.
This is the geometric part of the non-virgin-component argument. -/
theorem access_barrier (t : Tree) (lo first : Nat) (xs : List Nat)
    {c : Component} {n stamp accessed : Nat} {P : Finset Point}
    (history : History n (stamp + 1) P) (point : (accessed, stamp) ∈ P)
    (within : c.Contains accessed)
    (valid : ∀ x ∈ first :: xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ first :: xs, c ∈ forest t lo x)
    (other : ∀ x ∈ first :: xs, c ≠ ⟨x, .nil⟩) :
    ((∀ x ∈ first :: xs, x < c.first) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ accessed) ∨
    ((∀ x ∈ first :: xs, c.last ≤ x) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → accessed ≤ p.1) := by
  rcases stream_side t lo first xs valid member other with left | right
  · refine Or.inl ⟨left, ?_⟩
    apply Barrier.no_right_access xs history point
    intro x hx
    have side := left x (by simp [hx])
    exact le_trans (Nat.le_of_lt side) within.1
  · refine Or.inr ⟨right, ?_⟩
    apply Barrier.no_left_access xs history point
    intro x hx
    have side := right x (by simp [hx])
    exact le_trans (Nat.le_of_lt within.2) side

/-- The weak point-side formulation also covers searched singleton
components and empty streams. No excluded-component hypothesis is needed. -/
theorem persistent_barrier (t : Tree) (lo : Nat) (xs : List Nat)
    {c : Component} {n stamp accessed : Nat} {P : Finset Point}
    (history : History n (stamp + 1) P) (point : (accessed, stamp) ∈ P)
    (within : c.Contains accessed)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ xs, c ∈ forest t lo x) :
    ((∀ x ∈ xs, x ≤ accessed) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ accessed) ∨
    ((∀ x ∈ xs, accessed ≤ x) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → accessed ≤ p.1) := by
  rcases point_side t lo xs within valid member with left | right
  · exact Or.inl ⟨left, Barrier.no_right_access xs history point left⟩
  · exact Or.inr ⟨right, Barrier.no_left_access xs history point right⟩

end RotationBST.Geometric.GreedyASS.Reference
