module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Decomposition
public import RotationBST.Algorithms.MoveToRoot.Abstract
public import RotationBST.Models.Region.Bounds

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- An exposed key can be brought to the root by rotating only the exposed
key shape, with cost less than the number of exposed keys. -/
theorem Assembly.access {assembly : Assembly} {key : Nat}
    (member : key ∈ Region.keys assembly.region 0) :
    ∃ target cost, Access assembly.region.tree target key cost ∧
      cost < (Region.keys assembly.region 0).card := by
  let gaps := fun (j : Nat) => ((assembly.children.map Nested.tree)[j]?).getD Tree.nil
  have source : withGaps assembly.shape gaps 0 = assembly.region := assembly.decomposition
  rw [← source, withGaps_keys] at member
  obtain ⟨rank, bound, equal⟩ := member
  have moved := moveToRoot_correct assembly.shape rank bound
  have lifted := withGaps_access moved.1 gaps 0
  rw [source] at lifted
  simp only [Nat.zero_add] at equal
  refine ⟨_, _, equal ▸ lifted, ?_⟩
  rw [Region.keys_card, ← assembly.shape_size]
  exact moved.2

end RotationBST.Geometric.Online.Supernode
