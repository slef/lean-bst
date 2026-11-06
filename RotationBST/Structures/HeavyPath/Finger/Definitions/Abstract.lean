module

public import RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate

/-- Ancestors are charged to the next payload toward the finger. The first
outer payload has no preceding separator; the last payload is a finger child. -/
def sideSlots {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) : ℝ → List (Frame α) → List (Tree × ℝ)
  | carry, [] => [(payload boundary, carry + HeavyPath.mass weight boundary)]
  | carry, f :: fs => (payload (framePayload f), carry + HeavyPath.mass weight (framePayload f)) ::
      sideSlots weight payload boundary (weight (frameKey f)) fs

/-- Assemble a nonempty fringe by actual Chocolate pushes, starting at its
last leaf. The empty case is only a totalization of this auxiliary function. -/
noncomputable def assemble : List (Tree × ℝ) → Layer
  | [] => .last .zero (.base (.leaf .nil 0))
  | [entry] => .last .zero (.base (.leaf entry.1 entry.2))
  | entry :: next :: rest => (assemble (next :: rest)).push (.leaf entry.1 entry.2)

def reflectSlot (entry : Tree × ℝ) : Tree × ℝ := (entry.1.mirror, entry.2)

/-- The inverted path has the opposite stack orientations from a downward
heavy path. Its physical root is the original finger node. -/
structure Pair where
  lower : Layer
  upper : Layer

def Pair.tree (p : Pair) : Tree := .node p.lower.decode.tree.mirror p.upper.decode.tree
def Pair.mass (p : Pair) : ℝ := p.lower.decode.mass + p.upper.decode.mass
def Pair.Valid (p : Pair) : Prop := p.lower.Valid 0 ∧ p.upper.Valid 0

noncomputable def build {α : Type} (weight : α → ℝ) (cs : List (Frame α))
    (left right : LabelledTree α) : Pair :=
  ⟨assemble ((sideSlots weight (rebuild weight) left 0 (lowerFrames cs)).map reflectSlot).reverse,
   assemble (sideSlots weight (rebuild weight) right 0 (upperFrames cs).reverse).reverse⟩

end RotationBST.HeavyPath.Finger
