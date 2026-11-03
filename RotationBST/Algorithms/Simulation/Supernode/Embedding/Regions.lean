module

public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Proofs
public import RotationBST.Models.Region.Basic

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- Lifting a key-only rotation preserves absolute active keys and the offsets
of every gap, not just the unlabelled fringe list. -/
theorem withGaps_same_step {s t : Tree} (step : Rotate s t)
    (gaps : Nat → Tree) (offset lo : Nat) :
    Region.Same (withGaps s gaps offset) (withGaps t gaps offset) lo := by
  induction step generalizing offset lo with
  | @right a b c =>
    simpa only [withGaps, Tree.size, Nat.add_assoc] using
      Region.same_right (withGaps a gaps offset) (withGaps b gaps (offset + a.size + 1))
        (withGaps c gaps (offset + a.size + 1 + b.size + 1)) lo
  | @left a b c =>
    have reverse := Region.same_right (withGaps a gaps offset) (withGaps b gaps (offset + a.size + 1))
        (withGaps c gaps (offset + a.size + 1 + b.size + 1)) lo
    simpa only [withGaps, Tree.size, Nat.add_assoc] using
      (show Region.Same _ _ lo from ⟨reverse.1.symm, reverse.2.1.symm, reverse.2.2.symm⟩)
  | inLeft step ih =>
    simpa only [withGaps, step.size_eq] using Region.same_node (ih offset lo) (Region.Same.refl _ _)
  | inRight step ih => exact Region.same_node (Region.Same.refl _ _) (ih _ _)

theorem withGaps_same {s t : Tree} {cost : Nat} (steps : Rotations s t cost)
    (gaps : Nat → Tree) (offset lo : Nat) :
    Region.Same (withGaps s gaps offset) (withGaps t gaps offset) lo := by
  induction steps with
  | refl => exact Region.Same.refl _ _
  | step first rest ih => exact (withGaps_same_step first gaps offset lo).trans ih

end RotationBST.Geometric.Online.Supernode
