module

public import CslibFrontier.Computability.PointerMachine.Basic
public import RotationBST.Models.Labelled.Cursor.Abstract
public import RotationBST.Models.Labelled.Ordering.Abstract

@[expose] public section
namespace RotationBST.RealWorld.PointerMachine


/-- The scalar instruction vocabulary is independent of word width. -/
inductive WordOp where
  | literal (n : Nat) | add | sub

inductive WordTest where
  | eq | lt

/-- Modular words, with no conversion from a word to a pointer. -/
abbrev words (w : Nat) : Cslib.PointerMachine.Model where
  Value := BitVec w
  undefined := 0
  Op := WordOp
  Test := WordTest
  evalOp
    | .literal n, _, _ => BitVec.ofNat w n
    | .add, x, y => x + y
    | .sub, x, y => x - y
  evalTest
    | .eq, x, y => decide (x = y)
    | .lt, x, y => decide (x.toNat < y.toNat)

/-- Three pointer registers (cursor and two temporaries), two child fields,
one key field and `extra` metadata words. This initial representation has no
parent links: upward navigation needs a later representation extension. -/
abbrev layout (extra : Nat) : Cslib.PointerMachine.Layout := ⟨3, 2, 2, extra + 1⟩

abbrev State (w extra : Nat) := Cslib.PointerMachine.State (words w) (layout extra)
abbrev Record (w extra : Nat) := Cslib.PointerMachine.Record (words w) (layout extra)
abbrev Instruction (w extra : Nat) := Cslib.PointerMachine.Instr (words w) (layout extra)
abbrev Tree (w : Nat) := LabelledTree (Nat × BitVec w)

/-- Addresses in this specification are ghost labels, never scalar machine data. -/
def root {w : Nat} : Tree w → Cslib.PointerMachine.Pointer
  | .nil => none
  | .node _ x _ => some x.1

def addresses {w : Nat} (t : Tree w) : List Nat := t.inorder.map Prod.fst

def keys {w : Nat} : Tree w → LabelledTree Nat
  | .nil => .nil
  | .node l x r => .node (keys l) x.2.toNat (keys r)

/-- Recursive representation in an actual upstream heap. Metadata is unrestricted. -/
def Represents {w e : Nat} (heap : List (Record w e)) : Tree w → Prop
  | .nil => True
  | .node l x r =>
      (∃ record, heap[x.1]? = some record ∧ record.ptr 0 = root l ∧
        record.ptr 1 = root r ∧ record.data 0 = x.2) ∧
      Represents heap l ∧ Represents heap r

/-- At a boundary all allocated records are exactly the distinct tree nodes.
There is no separate unaccounted work heap. -/
structure Boundary {w e : Nat} (s : State w e) (t : Tree w) : Prop where
  valid : s.Valid
  represents : Represents s.heap t
  distinct : (addresses t).Nodup
  covers : ∀ a, a < s.heap.length ↔ a ∈ addresses t
  ordered : (keys t).Ordered
  cursor : s.ptr 0 = root t

/-- Accepting the next key changes only its designated register and the entry
label. A suspended computation and all retained history must reside in `s`. -/
def accept {w e : Nat} (entry : Nat) (key : BitVec w) (s : State w e) : State w e :=
  { s.setData 0 key with pc := entry }

/-- Fixed code and a restart label. Halting is the request boundary. -/
structure Protocol (w e : Nat) where
  code : List (Instruction w e)
  entry : Nat


/-- A response includes an actual visit along the execution, and counts the
halting instruction. The next key is unavailable until this response ends. -/
def Responds {w e : Nat} (p : Protocol w e) (s : State w e) (key : BitVec w)
    (t : State w e) (time : Nat) : Prop :=
  p.code[s.pc]? = some .halt ∧
  Cslib.PointerMachine.Executes p.code (accept p.entry key s) t time ∧
  ∃ u a b, Cslib.PointerMachine.Runs p.code (accept p.entry key s) u a ∧
    Cslib.PointerMachine.Runs p.code u t b ∧ (∃ record, u.deref 0 = some record ∧ record.data 0 = key) ∧ time = a + b + 1

/-- Histories are proof objects; they are not passed to the machine. -/
inductive Execution {w e : Nat} (p : Protocol w e) :
    State w e → List (BitVec w) → State w e → Nat → Prop where
  | nil (s) : Execution p s [] s 0
  | cons {s t u key rest a b} : Responds p s key t a →
      Execution p t rest u b → Execution p s (key :: rest) u (a + b)

/-- Downward navigation is exactly one pointer load. -/
def down {w e : Nat} (side : Fin 2) : Instruction w e := .loadPtr 0 side 0

/-- Root right rotation: load the left child and its right subtree, rewire
both child links, then put the new root in the cursor. No allocation. -/
def rotateRight {w e : Nat} : List (Instruction w e) :=
  [.loadPtr 1 0 0, .loadPtr 2 1 1, .storePtr 0 0 2, .storePtr 1 1 0, .movePtr 0 1]

/-- Straight-line effects, used only to name the endpoints of these programs.
The execution theorem separately establishes the actual charged `Cslib.PointerMachine.Runs`. -/
def effects {w e : Nat} : List (Instruction w e) → State w e → State w e
  | [], s => s
  | i :: rest, s => effects rest { i.effect s with pc := s.pc + 1 }

end RotationBST.RealWorld.PointerMachine
