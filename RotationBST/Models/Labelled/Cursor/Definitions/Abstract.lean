module

public import RotationBST.Models.Multifinger.Program.Definitions.Abstract

@[expose] public section
namespace RotationBST.LabelledCursor

inductive Frame (α : Type) where
  | left (entry : α) (right : LabelledTree α)
  | right (left : LabelledTree α) (entry : α)
  deriving DecidableEq

def plug {α : Type} : List (Frame α) → LabelledTree α → LabelledTree α
  | [], t => t
  | .left entry r :: cs, t => plug cs (.node t entry r)
  | .right l entry :: cs, t => plug cs (.node l entry t)

def Frame.erase {α : Type} : Frame α → Pointer.Frame
  | .left _ r => .left r.erase
  | .right l _ => .right l.erase

structure Config (α : Type) where
  focus : LabelledTree α
  context : List (Frame α)
  deriving DecidableEq

def Config.tree {α : Type} (c : Config α) : LabelledTree α := plug c.context c.focus

def Config.erase {α : Type} (c : Config α) : Pointer.Config :=
  ⟨c.focus.erase, c.context.map Frame.erase⟩

/-- Read the entry physically under the cursor. -/
def Config.read {α : Type} (c : Config α) : Option α :=
  match c.focus with | .nil => none | .node _ entry _ => some entry

/-- Replace only the entry physically under the cursor. -/
def Config.write {α : Type} (c : Config α) (entry : α) : Option (Config α) :=
  match c.focus with
  | .nil => none
  | .node l _ r => some ⟨.node l entry r, c.context⟩

/-- Stored labels travel with their physical nodes. No rank or subtree size
computation is used by these pointer primitives. -/
def perform {α : Type} : Multifinger.Opcode → Config α → Option (Config α)
  | .downLeft, ⟨.node (.node a x b) y r, cs⟩ => some ⟨.node a x b, .left y r :: cs⟩
  | .downRight, ⟨.node l x (.node a y b), cs⟩ => some ⟨.node a y b, .right l x :: cs⟩
  | .upLeft, ⟨.node a x b, .left y r :: cs⟩ => some ⟨.node (.node a x b) y r, cs⟩
  | .upRight, ⟨.node a y b, .right l x :: cs⟩ => some ⟨.node l x (.node a y b), cs⟩
  | .rotateLeftChild, ⟨.node a x b, .left y r :: cs⟩ => some ⟨.node a x (.node b y r), cs⟩
  | .rotateRightChild, ⟨.node a y b, .right l x :: cs⟩ => some ⟨.node (.node l x a) y b, cs⟩
  | _, _ => none

end RotationBST.LabelledCursor
