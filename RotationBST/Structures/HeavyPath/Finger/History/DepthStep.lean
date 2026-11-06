module

public import RotationBST.Structures.HeavyPath.Finger.History.Preservation
public import RotationBST.Structures.HeavyPath.Finger.DepthStep
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem payload_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {subtree : LabelledTree α}
    {shape : Tree} {credit : Nat} (layout : Recursive.History.Layout weight subtree shape credit) {charge : ℝ} (charged : HeavyPath.mass weight subtree ≤ charge)
    {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) shape charge offset depth) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) offset subtree.inorder := by
  have positive := Recursive.History.layout_positive layout
  intro before key after split
  obtain ⟨keyPositive, keyMass⟩ := inorder_weight positive (x := key) (by rw [split]; simp)
  have chargePositive := lt_of_lt_of_le keyPositive (keyMass.trans charged)
  have inside : before.length < shape.size := by
    rw [Recursive.History.layout_size layout, ← Representation.Bridge.inorder_length, split]
    simp only [List.length_append, List.length_cons]
    omega
  have bound := located_key_bound valid slot chargePositive before.length inside
  have child := Recursive.History.layout_depth layout split
  apply payload_estimate keyPositive keyMass charged (located_mass valid slot).2 sourceMass
  linarith

end RotationBST.HeavyPath.Finger.History
