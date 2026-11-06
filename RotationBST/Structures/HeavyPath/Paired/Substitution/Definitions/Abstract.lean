module

public import RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

def framePayload {α : Type} : Frame α → LabelledTree α
  | .left _ r => r
  | .right l _ => l

/-- Replace the physical off-path subtree, retaining the side of the path. -/
def replaceFrame {α : Type} (payload : LabelledTree α → Tree) : Frame α → Pointer.Frame
  | .left _ r => .left (payload r)
  | .right l _ => .right (payload l)

namespace Stacks

/-- Analysis charges come from the original labelled tree, even when the
physical payload has already been recursively restructured. -/
noncomputable def pushWith {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (frame : Frame α) (p : Stacks) : Stacks :=
  match frame with
  | .left x r => ⟨p.lower, p.upper.push (.leaf (payload r).mirror (weight x + HeavyPath.mass weight r))⟩
  | .right l x => ⟨p.lower.push (.leaf (payload l) (HeavyPath.mass weight l + weight x)), p.upper⟩

noncomputable def buildWith {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    List (Frame α) → Stacks → Stacks
  | [], p => p
  | frame :: cs, p => buildWith weight payload cs (p.pushWith weight payload frame)

noncomputable def buildWithCost {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    List (Frame α) → Stacks → Nat
  | [], _ => 0
  | frame :: cs, p => p.pushCost frame + buildWithCost weight payload cs (p.pushWith weight payload frame)

end Stacks

def lowerSlotsWith {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    List (Frame α) → List (Tree × ℝ)
  | [] => []
  | .left _ _ :: cs => lowerSlotsWith weight payload cs
  | .right l x :: cs => (payload l, HeavyPath.mass weight l + weight x) :: lowerSlotsWith weight payload cs

def upperSlotsWith {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    List (Frame α) → List (Tree × ℝ)
  | [] => []
  | .left x r :: cs => (payload r, weight x + HeavyPath.mass weight r) :: upperSlotsWith weight payload cs
  | .right _ _ :: cs => upperSlotsWith weight payload cs

end RotationBST.HeavyPath.Paired
