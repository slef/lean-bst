module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Push

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

theorem empty_valid : Stacks.empty.Valid := by
  constructor <;> exact ⟨trivial, ⟨.leaf .nil 0, le_rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem push_trace {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks)
    (cs : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, frame.erase :: cs⟩ ⟨(p.push weight frame).tree, cs⟩ (p.pushCost frame) :=
  pushWith_trace weight LabelledTree.erase frame p cs

theorem push_valid {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) : (p.push weight frame).Valid :=
  pushWith_valid LabelledTree.erase valid nonnegative

theorem push_amortized {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    p.pushCost frame + (p.push weight frame).potential ≤ 23 + p.potential :=
  pushWith_amortized LabelledTree.erase valid nonnegative

theorem push_mass {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.push weight frame).mass = p.mass + frameMass weight frame :=
  pushWith_mass LabelledTree.erase valid nonnegative

theorem push_lower_size {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks) :
    (p.push weight frame).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset [frame.erase] :=
  pushWith_lower_size weight LabelledTree.erase frame p

end RotationBST.HeavyPath.Paired
