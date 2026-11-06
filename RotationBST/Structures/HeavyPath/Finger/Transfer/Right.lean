module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Left
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open PopTart PopTart.WeightedTree PopTart.Chocolate

theorem flip_tree (p : Pair) : p.flip.tree = p.tree.mirror := by
  simp only [Pair.flip, Pair.tree, Tree.mirror, Tree.mirror_mirror]

theorem flip_mass (p : Pair) : p.flip.mass = p.mass := by simp only [Pair.flip, Pair.mass, add_comm]

theorem flip_potential (p : Pair) : p.flip.potential = p.potential := by
  simp only [Pair.flip, Pair.potential, Nat.add_comm]

private theorem reflected_exposure {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge) :
    p.flip.lower.top = .leaf (Tree.node b.mirror a.mirror).mirror oldCharge := by
  simpa only [Pair.flip, Tree.mirror, Tree.mirror_mirror] using exposed

theorem downRight_trace {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge) (lowerCharge upperCharge : ℝ) :
    Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ p.downRightCost := by
  have trace := (downLeft_trace (reflected_exposure exposed) upperCharge lowerCharge).mirror
  simpa only [Pointer.Config.mirror, Pair.downRight, Pair.downRightCost, flip_tree,
    Tree.mirror_mirror, List.map_nil] using trace

theorem downRight_valid {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    (p.downRight a b lowerCharge upperCharge).Valid := by
  have transferred := downLeft_valid (p := p.flip) ⟨valid.2, valid.1⟩ b.mirror a.mirror
    upperNonnegative lowerNonnegative
  exact ⟨transferred.2, transferred.1⟩

theorem downRight_amortized {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    p.downRightCost + (p.downRight a b lowerCharge upperCharge).potential ≤ 26 + p.potential := by
  have bound := downLeft_amortized (p := p.flip) ⟨valid.2, valid.1⟩ b.mirror a.mirror
    upperCharge lowerNonnegative
  simpa only [Pair.downRight, Pair.downRightCost, flip_potential] using bound

theorem downRight_mass {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    (p.downRight a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge := by
  have balance := downLeft_mass (p := p.flip) ⟨valid.2, valid.1⟩
    (reflected_exposure exposed) upperCharge lowerNonnegative
  simpa only [Pair.downRight, flip_mass, add_assoc, add_comm, add_left_comm] using balance

theorem downRight_root_key (p : Pair) (a b : Tree) (lowerCharge upperCharge : ℝ) :
    (Pointer.Config.mk (p.downRight a b lowerCharge upperCharge).tree []).key? =
      some (p.lower.decode.tree.mirror.size + a.size + 1) := by
  obtain ⟨_, _, rotations⟩ := (Chocolate.Results.push_trace p.lower (.leaf a.mirror lowerCharge)).rotations
  have size := rotations.size_eq
  change (Tree.node a.mirror p.lower.decode.tree).size =
    (p.lower.push (.leaf a.mirror lowerCharge)).decode.tree.size at size
  simp only [Tree.size, Tree.mirror_size] at size
  simp only [Pointer.Config.key?, Pair.downRight, Pair.downLeft, Pair.flip, Pair.tree,
    Pointer.offset, Nat.zero_add, Tree.mirror_size]
  congr 1
  omega

end RotationBST.HeavyPath.Finger
