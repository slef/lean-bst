module

public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST.Deamortization.Scheduler

/-- A pending program keeps every intermediate physical tree within the budget. -/
def Height (budget : Nat) (start : Pointer.Config) (ops : List Multifinger.Opcode) : Prop :=
  ∀ cut middle, Multifinger.replay (ops.take cut) start = some middle →
    ∀ x < middle.tree.size, Tree.depth middle.tree x ≤ budget

/-- The original algorithm supplies only the next request's physical program. -/
structure Request where
  target : Nat
  instructions : List Multifinger.Opcode

/-- A prepared original request contains an actual visit in its recorded code. -/
def Prepared (budget : Nat) (start : Pointer.Config) (request : Request) (finish : Pointer.Config) : Prop :=
  Multifinger.replay request.instructions start = some finish ∧
  (∃ cut visited, cut ≤ request.instructions.length ∧
    Multifinger.replay (request.instructions.take cut) start = some visited ∧ visited.key? = some request.target) ∧
  Height budget start request.instructions

/-- The actual cursor can lag behind the planned endpoint by exactly pending.
No original operation is lost when a new request is appended. -/
structure State where
  cursor : Pointer.Config
  pending : List Multifinger.Opcode
  planned : Pointer.Config

def Valid (budget : Nat) (s : State) : Prop :=
  s.cursor.focus ≠ .nil ∧ Multifinger.replay s.pending s.cursor = some s.planned ∧
    Height budget s.cursor s.pending

def initial (cursor : Pointer.Config) : State := ⟨cursor, [], cursor⟩

structure Response where
  state : State
  visited : Pointer.Config
  before : List Multifinger.Opcode
  after : List Multifinger.Opcode
  consumed : Nat

def Response.instructions (out : Response) : List Multifinger.Opcode := out.before ++ out.after

def Correct (budget : Nat) (s : State) (request : Request) (out : Response) : Prop :=
  Valid budget out.state ∧
  Multifinger.replay request.instructions s.planned = some out.state.planned ∧
  out.consumed ≤ budget ∧ out.consumed ≤ (s.pending ++ request.instructions).length ∧
  out.state.pending = (s.pending ++ request.instructions).drop out.consumed ∧
  Multifinger.replay ((s.pending ++ request.instructions).take out.consumed) s.cursor = some out.state.cursor ∧
  Multifinger.replay out.before s.cursor = some out.visited ∧ out.visited.key? = some request.target ∧
  Multifinger.replay out.after out.visited = some out.state.cursor ∧
  out.instructions.length ≤ 5 * out.consumed ∧
  1 + out.instructions.length ≤ 1 + 5 * budget

abbrev Policy := State → Request → Option Response

def PolicyValid (budget : Nat) (p : Policy) : Prop :=
  ∀ s request, Valid budget s → (∃ finish, Prepared budget s.planned request finish) →
    ∃ out, p s request = some out ∧ Correct budget s request out

/-- Preparation follows the original cursor, independently of scheduler lag. -/
inductive PreparedStream (budget : Nat) : Pointer.Config → List Request → Pointer.Config → Prop where
  | nil {cursor : Pointer.Config} : PreparedStream budget cursor [] cursor
  | cons {a b c : Pointer.Config} {request : Request} {requests : List Request} :
      Prepared budget a request b → PreparedStream budget b requests c →
      PreparedStream budget a (request :: requests) c

/-- Each charged request has its own contiguous physical instruction segment,
with a recorded visit and the exact segment length. Adjacent segments share
one actual cursor; concatenation is the emitted program. -/
inductive ServedStream : Pointer.Config → List Nat → Pointer.Config →
    List Multifinger.Opcode → List Nat → Prop where
  | nil {cursor : Pointer.Config} : ServedStream cursor [] cursor [] []
  | cons {a visited b c : Pointer.Config} {key : Nat} {keys costs : List Nat}
      {before after rest : List Multifinger.Opcode} :
      Multifinger.replay before a = some visited → visited.key? = some key →
      Multifinger.replay after visited = some b → ServedStream b keys c rest costs →
      ServedStream a (key :: keys) c ((before ++ after) ++ rest)
        ((1 + (before ++ after).length) :: costs)

structure Output where
  state : State
  instructions : List Multifinger.Opcode
  consumed : Nat
  costs : List Nat

def run (p : Policy) (s : State) : List Request → Option Output
  | [] => some ⟨s, [], 0, []⟩
  | request :: requests => (p s request).bind fun first =>
      (run p first.state requests).map fun last =>
        ⟨last.state, first.instructions ++ last.instructions,
          first.consumed + last.consumed, (1 + first.instructions.length) :: last.costs⟩

/-- Existing persistent single-finger semantics, with the actual cursor key. -/
def cursorState (c : Pointer.Config) : Multifinger.State 1 :=
  ⟨c.tree, fun _ => c.key?.getD 0⟩

end RotationBST.Deamortization.Scheduler
