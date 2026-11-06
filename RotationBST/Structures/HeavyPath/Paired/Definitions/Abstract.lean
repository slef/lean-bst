module

public import RotationBST.Structures.HeavyPath.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract
public import RotationBST.Structures.PopTart.Mirror.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

/-- The endpoint is the root between the two stacks. The second stack is
stored in reversed coordinates and reflected when decoded physically. -/
structure Stacks where
  lower : Layer
  upper : Layer

namespace Stacks

def tree (p : Stacks) : Tree := .node p.lower.decode.tree p.upper.decode.tree.mirror
def mass (p : Stacks) : ℝ := p.lower.decode.mass + p.upper.decode.mass
def potential (p : Stacks) : Nat := p.lower.potential + p.upper.potential
def Valid (p : Stacks) : Prop := p.lower.Valid 0 ∧ p.upper.Valid 0

def empty : Stacks := ⟨.last .zero (.base (.leaf .nil 0)), .last .zero (.base (.leaf .nil 0))⟩

/-- Insert the next ancestor into the appropriate stack. The off-path subtree
is opaque; an upper subtree is reflected on entry so physical decoding restores
its original orientation. Node weights are included in the fringe charges. -/
noncomputable def push {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks) : Stacks :=
  match frame with
  | .left x r => ⟨p.lower, p.upper.push (.leaf r.erase.mirror (weight x + HeavyPath.mass weight r))⟩
  | .right l x => ⟨p.lower.push (.leaf l.erase (HeavyPath.mass weight l + weight x)), p.upper⟩

/-- One rotation raises the endpoint over the next ancestor; entering and
leaving the updated stack adds two moves to its rebalancing cost. -/
noncomputable def pushCost {α : Type} (frame : Frame α) (p : Stacks) : Nat :=
  match frame with
  | .left _ _ => p.upper.pushCost + 3
  | .right _ _ => p.lower.pushCost + 3

noncomputable def build {α : Type} (weight : α → ℝ) : List (Frame α) → Stacks → Stacks
  | [], p => p
  | frame :: cs, p => build weight cs (p.push weight frame)

noncomputable def buildCost {α : Type} (weight : α → ℝ) : List (Frame α) → Stacks → Nat
  | [], _ => 0
  | frame :: cs, p => p.pushCost frame + buildCost weight cs (p.push weight frame)

end Stacks

def lowerSlots {α : Type} (weight : α → ℝ) : List (Frame α) → List (Tree × ℝ)
  | [] => []
  | .left _ _ :: cs => lowerSlots weight cs
  | .right l x :: cs => (l.erase, HeavyPath.mass weight l + weight x) :: lowerSlots weight cs

def upperSlots {α : Type} (weight : α → ℝ) : List (Frame α) → List (Tree × ℝ)
  | [] => []
  | .left x r :: cs => (r.erase, weight x + HeavyPath.mass weight r) :: upperSlots weight cs
  | .right _ _ :: cs => upperSlots weight cs

end RotationBST.HeavyPath.Paired
