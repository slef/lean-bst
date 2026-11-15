module

public import RotationBST.Models.Labelled.Cursor.Abstract
public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section
namespace RotationBST.RealWorld

/-- Immutable key plus a fixed number of mutable words. -/
structure Node (width fields : Nat) where
  key : BitVec width
  data : Fin fields → BitVec width

/-- Finite code, independent of tree size and word width. No instruction
contains a Lean function for computing its result. Arithmetic is modular. -/
inductive Instruction (fields registers labels : Nat) where
  | literal (dst : Fin registers) (value : Nat) (next : Fin labels)
  | copy (dst src : Fin registers) (next : Fin labels)
  | add (dst a b : Fin registers) (next : Fin labels)
  | sub (dst a b : Fin registers) (next : Fin labels)
  | branch (a b : Fin registers) (yes no : Fin labels)
  | load (dst : Fin registers) (field : Fin fields) (next : Fin labels)
  | store (field : Fin fields) (src : Fin registers) (next : Fin labels)
  | key (dst : Fin registers) (next : Fin labels)
  | query (dst : Fin registers) (next : Fin labels)
  | bst (op : Multifinger.Opcode) (next : Fin labels)
  | mark (next : Fin labels)
  | finish

structure Machine (fields registers labels : Nat) where
  code : Fin labels → Instruction fields registers labels
  entry : Fin labels

/-- A semantic presentation of a linked tree and one persistent finger.
The zipper describes the finger; it is not an additional runtime stack.
Node links and the finger are represented by addresses in a concrete lowering.
There is no request history, pending output list, or arbitrary private state. -/
structure State (width fields registers labels : Nat) where
  cursor : LabelledCursor.Config (Node width fields)
  regs : Fin registers → BitVec width
  request : BitVec width
  seen : Bool
  pc : Option (Fin labels)

/-- Scalar instructions and local metadata operations are charged even though
they emit no BST opcode. A request can finish only after an explicit visit. -/
def eval {w f r l : Nat} (i : Instruction f r l) (s : State w f r l) :
    Option (State w f r l × Option Multifinger.Opcode) := do
  match i with
  | .literal dst value next =>
      return ({ s with regs := Function.update s.regs dst (BitVec.ofNat w value), pc := some next }, none)
  | .copy dst src next =>
      return ({ s with regs := Function.update s.regs dst (s.regs src), pc := some next }, none)
  | .add dst a b next =>
      return ({ s with regs := Function.update s.regs dst (s.regs a + s.regs b), pc := some next }, none)
  | .sub dst a b next =>
      return ({ s with regs := Function.update s.regs dst (s.regs a - s.regs b), pc := some next }, none)
  | .branch a b yes no =>
      return ({ s with pc := some (if (s.regs a).toNat < (s.regs b).toNat then yes else no) }, none)
  | .load dst field next =>
      let node ← s.cursor.read
      return ({ s with regs := Function.update s.regs dst (node.data field), pc := some next }, none)
  | .store field src next =>
      let node ← s.cursor.read
      let cursor ← s.cursor.write { node with data := Function.update node.data field (s.regs src) }
      return ({ s with cursor, pc := some next }, none)
  | .key dst next =>
      let node ← s.cursor.read
      return ({ s with regs := Function.update s.regs dst node.key, pc := some next }, none)
  | .query dst next =>
      return ({ s with regs := Function.update s.regs dst s.request, pc := some next }, none)
  | .bst op next =>
      let cursor ← LabelledCursor.perform op s.cursor
      return ({ s with cursor, pc := some next }, some op)
  | .mark next =>
      let node ← s.cursor.read
      if node.key = s.request then return ({ s with seen := true, pc := some next }, none)
      else none
  | .finish =>
      if s.seen then return ({ s with pc := none }, none) else none

def tick {w f r l : Nat} (p : Machine f r l) (s : State w f r l) :=
  s.pc.bind fun pc => eval (p.code pc) s

/-- Input is available only at a response boundary, one key at a time. -/
def accept {w f r l : Nat} (p : Machine f r l) (x : BitVec w) (s : State w f r l) :
    Option (State w f r l) :=
  if s.pc = none then some { s with request := x, seen := false, pc := some p.entry } else none

inductive Event (width : Nat) where
  | input (key : BitVec width)
  | compute (output : Option Multifinger.Opcode)

/-- CSLib supplies the transition-system vocabulary, not the instruction set. -/
def lts {w f r l : Nat} (p : Machine f r l) : Cslib.LTS (State w f r l) (Event w) where
  Tr s event t := match event with
    | .input x => accept p x s = some t
    | .compute out => tick p s = some (t, out)

/-- Proof-only execution log. Each constructor charges one machine instruction;
only emitted pointer instructions contribute to BST cost. -/
inductive Run {w f r l : Nat} (p : Machine f r l) :
    State w f r l → State w f r l → Nat → Nat → Prop where
  | nil {s} : Run p s s 0 0
  | cons {s t u time cost out} : tick p s = some (t, out) →
      Run p t u time cost → Run p s u (time + 1) (cost + out.toList.length)

/-- One completed request. The initial state is a boundary state. -/
def Responds {w f r l : Nat} (p : Machine f r l) (s : State w f r l)
    (x : BitVec w) (t : State w f r l) (time cost : Nat) : Prop :=
  ∃ start, accept p x s = some start ∧ Run p start t time cost ∧ t.pc = none

/-- Completed online accesses. The request list is specification data; it is
never passed to an instruction or stored in a machine state. -/
inductive Execution {w f r l : Nat} (p : Machine f r l) :
    State w f r l → List (BitVec w) → State w f r l → Nat → Nat → Prop where
  | nil {s} : Execution p s [] s 0 0
  | cons {s t u x xs time cost moreTime moreCost} : Responds p s x t time cost →
      Execution p t xs u moreTime moreCost →
      Execution p s (x :: xs) u (time + moreTime) (cost + moreCost)

/-- Total service is a separate obligation: finite code may otherwise fail or
loop. Quantification is over every completed history and every existing key.
`initial` is supplied separately; this does not give initialization free runtime. -/
def Total {w f r l : Nat} (p : Machine f r l) (initial : State w f r l) (nodes : Nat) : Prop :=
  ∀ (xs : List (BitVec w)) (s : State w f r l) (time cost : Nat),
    Execution p initial xs s time cost → ∀ x : BitVec w, x.toNat < nodes →
      ∃ t moreTime moreCost, Responds p s x t moreTime moreCost

/-- Additional efficiency obligation, not a consequence of bounded storage.
The additive request unit handles accesses already at the finger. -/
def ProportionalTime {f r l : Nat} (p : Machine f r l) (constant : Nat) : Prop :=
  ∀ (w : Nat) (s t : State w f r l) (x : BitVec w) (time cost : Nat),
    Responds p s x t time cost → time ≤ constant * (cost + 1)

/-- Word-size discipline for a uniform family. Enough bits for addresses and
keys; at most logarithmically many bits. Constants do not depend on n. -/
def WordSize (width : Nat → Nat) (constant : Nat) : Prop :=
  ∀ n, n < 2 ^ width n ∧ width n ≤ constant * (Nat.log2 (n + 1) + 1)

/-- Ordered immutable keys 0,...,n-1 at initialization. The addressability
condition in `WordSize` prevents truncation of these keys. -/
def Initial {w f r l : Nat} (s : State w f r l) (n : Nat) : Prop :=
  s.pc = none ∧ s.cursor.context = [] ∧
    s.cursor.tree.inorder.map Node.key = List.ofFn (fun i : Fin n => BitVec.ofNat w i.val)

/-- Runtime bound restricted to reachable response boundaries. -/
def EfficientFrom {w f r l : Nat} (p : Machine f r l) (initial : State w f r l)
    (constant : Nat) : Prop :=
  ∀ (xs : List (BitVec w)) (s t : State w f r l) (a b time cost : Nat) (x : BitVec w),
    Execution p initial xs s a b → Responds p s x t time cost →
      time ≤ constant * (cost + 1)

/-- Uniform implementation contract. Fixed code and register/field counts are
outside the size quantifier. Initialization is a specification, not free
executable preprocessing; a construction must separately account for setup. -/
structure Implementation (fields registers labels : Nat) where
  machine : Machine fields registers labels
  width : Nat → Nat
  wordConstant : Nat
  wordSize : WordSize width wordConstant
  initial : (n : Nat) → State (width n) fields registers labels
  initialized : ∀ n, Initial (initial n) n
  total : ∀ n, Total machine (initial n) n
  timeConstant : Nat
  efficient : ∀ n, EfficientFrom machine (initial n) timeConstant

/-- Three links, one immutable key, and f metadata words per node; r scalar
registers, root/finger/query registers and a flag. Finite control is separate. -/
def storageWords (fields registers nodes : Nat) : Nat :=
  (fields + 4) * nodes + registers + 4

end RotationBST.RealWorld
