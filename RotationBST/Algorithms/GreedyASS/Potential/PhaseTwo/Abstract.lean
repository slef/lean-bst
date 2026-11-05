module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results
open Items Reference

/-- The total item potential includes both accessed and untouched keys. -/
theorem items (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t)
    (domain : Finset Nat) (covers : Virgin.keys searches searched ⊆ domain) :
    let keys := Virgin.keys searches searched
    let Q := Virgin.points (searches ++ [searched])
    keys.card + totalAmount t lo (searches ++ [searched]) Q domain ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) domain +
        (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
        (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
        3 * (unseenKeys (Virgin.points searches) keys).card :=
  PhaseTwo.items t lo searches searched valid domain covers

/-- At most six blue or purple new accesses per touched reference root. -/
theorem colors (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t) :
    (coloredKeys t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched]))
        (Virgin.keys searches searched) .blue).card +
      (coloredKeys t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched]))
        (Virgin.keys searches searched) .purple).card ≤ 6 * (Virgin.touched t lo searches searched).card :=
  PhaseTwo.color_counts t lo searches searched valid

/-- The Phase-II bound on any finite domain containing the accessed row. -/
theorem domain_bound (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t)
    (domain : Finset Nat) (covers : Virgin.keys searches searched ⊆ domain) :
    (Virgin.keys searches searched).card +
        totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) domain +
        Virgin.after t lo searches searched ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) domain +
        Virgin.before t lo searches searched + 24 +
        3 * (unseenKeys (Virgin.points searches) (Virgin.keys searches searched)).card :=
  PhaseTwo.bound t lo searches searched valid domain covers

/-- Complete Phase-II amortization on the full key universe; first accesses retain their explicit allowance. -/
theorem step (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.keys searches searched).card +
        totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) (Finset.range (lo + leaves t)) +
        Virgin.after t lo searches searched ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) (Finset.range (lo + leaves t)) +
        Virgin.before t lo searches searched + 24 +
        3 * (unseenKeys (Virgin.points searches) (Virgin.keys searches searched)).card :=
  PhaseTwo.step t lo searches searched valid

end RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.PhaseTwo.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract]
