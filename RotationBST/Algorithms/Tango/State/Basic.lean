module

public import RotationBST.Algorithms.Tango.State.Defs
public import RotationBST.Algorithms.Tango.Auxiliary.Cut

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

@[simp] theorem region_tree (s : MarkedTree) : s.region.tree = s.tree := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir => cases cl <;> cases cr <;> simp [region, tree, Pointer.Lazy.Skeleton.tree, il, ir]

@[simp] theorem initial_tree (t : Tree) : (initial t).tree = t := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [initial, tree, il, ir]

theorem region_potential_nonneg (s : Arboral.Region) : 0 ≤ auxiliaryPotential s :=
  Splay.Updates.unitPotential_nonneg s.shape

theorem potential_nonneg (s : MarkedTree) : 0 ≤ s.potential := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact region_potential_nonneg p.2

/-- Empty subtrees never introduce empty auxiliary components. -/
theorem components_nonempty (s : MarkedTree) (lo : Nat) :
    ∀ p ∈ s.components lo, 0 < p.2.size := by
  have root (s : MarkedTree) (lo : Nat) : ∀ p ∈ s.rootComponent lo, 0 < p.2.size := by
    cases s with
    | nil => simp [rootComponent]
    | node l r cl cr =>
      intro p hp
      have hp' : p = (lo, (MarkedTree.node l r cl cr).region) := by simpa [rootComponent] using hp
      subst p
      simp [region, size]
  have rest (s : MarkedTree) (lo : Nat) : ∀ p ∈ s.detached lo, 0 < p.2.size := by
    induction s generalizing lo with
    | nil => simp [detached]
    | node l r cl cr il ir =>
      cases cl <;> cases cr <;>
        simp only [detached, Bool.false_eq_true, ite_false, ite_true, List.nil_append,
          List.append_nil, List.mem_append]
      all_goals
        intro p hp
        have h1 := root l lo p
        have h2 := il lo p
        have h3 := root r (lo + l.tree.size + 1) p
        have h4 := ir (lo + l.tree.size + 1) p
        tauto
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact root s lo p hp
  · exact rest s lo p hp

end RotationBST.Tango.MarkedTree
