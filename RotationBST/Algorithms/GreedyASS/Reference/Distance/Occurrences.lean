module

public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Ordered
public import RotationBST.Algorithms.GreedyASS.Reference.Partition
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Distance

theorem Occurs.bounds {t : Tree} {lo k : Nat} {c : Component} (occurs : Occurs t lo c k) :
    lo ≤ c.first ∧ c.last ≤ lo + leaves t := by
  induction occurs with
  | root => simp [Component.last]
  | left h ih => simp only [leaves]; omega
  | right h ih => simp only [leaves]; omega

theorem Occurs.valid {t : Tree} {lo k x : Nat} {c : Component} (occurs : Occurs t lo c k)
    (inside : c.Contains x) : lo ≤ x ∧ x < lo + leaves t := by
  have := occurs.bounds
  unfold Component.Contains at inside
  omega

theorem Occurs.depth_eq {t : Tree} {lo k x : Nat} {c : Component} (occurs : Occurs t lo c k)
    (inside : c.Contains x) : depth t lo x = k + depth c.shape c.first x := by
  induction occurs with
  | root => simp
  | left h ih =>
    have child := ih inside
    have valid := h.valid inside
    simp only [depth, ite_eq_left valid.2]
    omega
  | right h ih =>
    have child := ih inside
    have valid := h.valid inside
    have side : ¬ x < _ := Nat.not_lt.mpr valid.1
    simp only [depth, ite_eq_right side]
    omega

theorem Occurs.lca_eq {t : Tree} {lo k a b : Nat} {c : Component} (occurs : Occurs t lo c k)
    (insideA : c.Contains a) (insideB : c.Contains b) :
    lcaDepth t lo a b = k + lcaDepth c.shape c.first a b := by
  induction occurs with
  | root => simp
  | left h ih =>
    have child := ih insideA insideB
    have va := h.valid insideA
    have vb := h.valid insideB
    simp only [lcaDepth, ite_eq_left (And.intro va.2 vb.2)]
    omega
  | @right l r lo c k h ih =>
    have child := ih insideA insideB
    have va := h.valid insideA
    have vb := h.valid insideB
    have notLeft : ¬ (a < lo + leaves l ∧ b < lo + leaves l) := by omega
    simp only [lcaDepth, ite_eq_right notLeft, ite_eq_left (And.intro va.1 vb.1)]
    omega

theorem forest_occurs (t : Tree) (lo searched : Nat) {c : Component}
    (member : c ∈ forest t lo searched) : ∃ k, Occurs t lo c k := by
  induction t generalizing lo with
  | nil =>
    have same : c = ⟨lo, .nil⟩ := by simpa only [forest, List.mem_singleton] using member
    subst c
    exact ⟨0, .root _ _⟩
  | node l r il ir =>
    simp only [forest] at member
    split at member
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨k, occurrence⟩ := il lo member
        exact ⟨k + 1, .left occurrence⟩
      · have same : c = ⟨lo + leaves l, r⟩ := List.mem_singleton.mp member
        subst c
        exact ⟨1, .right (.root _ _)⟩
    · rcases List.mem_cons.mp member with same | member
      · subst c
        exact ⟨1, .left (.root _ _)⟩
      · obtain ⟨k, occurrence⟩ := ir (lo + leaves l) member
        exact ⟨k + 1, .right occurrence⟩

theorem lca_occurs (t : Tree) (lo a b : Nat) :
    Occurs t lo (lca t lo a b) (lcaDepth t lo a b) := by
  induction t generalizing lo with
  | nil => exact .root _ _
  | node l r il ir =>
    by_cases left : a < lo + leaves l ∧ b < lo + leaves l
    · simp only [lca, lcaDepth, ite_eq_left left]
      exact .left (il lo)
    · by_cases right : lo + leaves l ≤ a ∧ lo + leaves l ≤ b
      · simp only [lca, lcaDepth, ite_eq_right left, ite_eq_left right]
        exact .right (ir (lo + leaves l))
      · simp only [lca, lcaDepth, ite_eq_right left, ite_eq_right right]
        exact .root _ _

theorem lca_contains (t : Tree) (lo a b : Nat)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    (lca t lo a b).Contains a ∧ (lca t lo a b).Contains b := by
  induction t generalizing lo with
  | nil => simpa only [lca, Component.Contains, Component.last] using And.intro validA validB
  | node l r il ir =>
    by_cases left : a < lo + leaves l ∧ b < lo + leaves l
    · simp only [lca, ite_eq_left left]
      exact il lo ⟨validA.1, left.1⟩ ⟨validB.1, left.2⟩
    · by_cases right : lo + leaves l ≤ a ∧ lo + leaves l ≤ b
      · simp only [lca, ite_eq_right left, ite_eq_left right]
        apply ir (lo + leaves l) <;> simp only [leaves] at validA validB <;> omega
      · simp only [lca, ite_eq_right left, ite_eq_right right, Component.Contains, Component.last]
        exact ⟨validA, validB⟩

theorem lca_lowest {t : Tree} {lo k a b : Nat} {c : Component} (occurs : Occurs t lo c k)
    (insideA : c.Contains a) (insideB : c.Contains b) : k ≤ lcaDepth t lo a b := by
  rw [occurs.lca_eq insideA insideB]
  omega

/-- Distances within one subtree do not depend on the ancestors above it. -/
theorem Occurs.toLCA_eq {t : Tree} {lo k a x b : Nat} {c : Component}
    (occurs : Occurs t lo c k) (insideX : c.Contains x)
    (insideA : c.Contains a) (insideB : c.Contains b) :
    toLCA t lo x a b = toLCA c.shape c.first x a b := by
  simp only [toLCA, occurs.depth_eq insideX, occurs.lca_eq insideA insideB,
    Nat.add_sub_add_left]

/-- The depth-subtraction formula is the node-counted upward path within
the actual LCA subtree, rather than merely an arithmetic surrogate. -/
theorem toLCA_eq (t : Tree) (lo a x b : Nat) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    toLCA t lo x a b = toRoot (lca t lo a b) x := by
  obtain ⟨ha, hb⟩ := lca_contains t lo a b validA validB
  have inside : (lca t lo a b).Contains x := by
    unfold Component.Contains at *
    omega
  have height := (lca_occurs t lo a b).depth_eq inside
  unfold toLCA toRoot
  omega

end RotationBST.Geometric.GreedyASS.Reference.Distance
