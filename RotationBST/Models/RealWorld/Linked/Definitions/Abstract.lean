module

public import RotationBST.Models.RealWorld.PointerMachine.Definitions.Abstract

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Pointer)

/-- Cursor, root, parent, grandparent, middle subtree, null and comparison
register; a fixed scalar register file; left, right and parent fields. -/
abbrev layout (extra regs : Nat) : Cslib.PointerMachine.Layout := ⟨7, regs, 3, extra + 1⟩
abbrev State (w e regs : Nat) := Cslib.PointerMachine.State (PointerMachine.words w) (layout e regs)
abbrev Record (w e regs : Nat) := Cslib.PointerMachine.Record (PointerMachine.words w) (layout e regs)
abbrev Instruction (w e regs : Nat) := Cslib.PointerMachine.Instr (PointerMachine.words w) (layout e regs)
/-- Ghost labels retain every data field, so representation preservation also
preserves metadata. The address is not available to scalar instructions. -/
abbrev Label (w e : Nat) := Nat × (Fin (e + 1) → BitVec w)
abbrev Tree (w e : Nat) := LabelledTree (Label w e)
abbrev Cursor (w e : Nat) := LabelledCursor.Config (Label w e)

variable {regs : Nat}

def root {w e : Nat} : Tree w e → Pointer
  | .nil => none
  | .node _ x _ => some x.1

def parent {w e : Nat} : List (LabelledCursor.Frame (Label w e)) → Pointer
  | [] => none
  | .left x _ :: _ | .right _ x :: _ => some x.1

def node {w e : Nat} (l r p : Pointer) (x : Label w e) : Record w e regs :=
  ⟨fun i => if i = 0 then l else if i = 1 then r else p, x.2⟩

def Represents {w e : Nat} (h : List (Record w e regs)) : Pointer → Tree w e → Prop
  | _, .nil => True
  | p, .node l x r => h[x.1]? = some (node (root l) (root r) p x) ∧
      Represents h (some x.1) l ∧ Represents h (some x.1) r

/-- Representation of ancestors and siblings, parameterized by the link to
the focused subtree. This is a proof-only zipper, not a stored stack. -/
def Context {w e : Nat} (h : List (Record w e regs)) :
    Pointer → List (LabelledCursor.Frame (Label w e)) → Prop
  | _, [] => True
  | p, .left x r :: cs =>
      h[x.1]? = some (node p (root r) (parent cs) x) ∧
      Represents h (some x.1) r ∧ Context h (some x.1) cs
  | p, .right l x :: cs =>
      h[x.1]? = some (node (root l) p (parent cs) x) ∧
      Represents h (some x.1) l ∧ Context h (some x.1) cs

def keys {w e : Nat} : Tree w e → LabelledTree Nat
  | .nil => .nil
  | .node l x r => .node (keys l) (x.2 0).toNat (keys r)

def addresses {w e : Nat} (t : Tree w e) := t.inorder.map Prod.fst

/-- A complete representation at any nonempty cursor, with no extra records. -/
structure Realizes {w e : Nat} (s : State w e regs) (c : Cursor w e) : Prop where
  valid : s.Valid
  focus : Represents s.heap (parent c.context) c.focus
  context : Context s.heap (root c.focus) c.context
  distinct : (addresses c.tree).Nodup
  covers : ∀ a, a < s.heap.length ↔ a ∈ addresses c.tree
  ordered : (keys c.tree).Ordered
  cursor : s.ptr 0 = root c.focus
  rootReg : s.ptr 1 = root c.tree
  nonempty : c.focus ≠ .nil

/-- Both upward opcodes follow the same parent field. Their side conditions
are supplied by the legal abstract step. -/
def move {w e : Nat} (field : Fin 3) : List (Instruction w e regs) :=
  [.loadPtr 0 field 0, .halt]

/-- Promote the cursor above its parent. `side` is the cursor's side in its
parent and `other` its opposite. Branches inspect the grandparent to repair
the appropriate link, or update the root register when the parent was root.
Null middle subtrees require no special branch: stores through null are no-ops. -/
def rotate {w e : Nat} (side other : Fin 3) : List (Instruction w e regs) :=
  [ .loadPtr 2 2 0,       -- 0: parent
    .loadPtr 3 2 2,       -- 1: grandparent
    .loadPtr 4 other 0,   -- 2: middle subtree
    .storePtr side 2 4,   -- 3: parent's child = middle
    .storePtr 2 4 2,      -- 4: middle's parent = parent
    .storePtr other 0 2,  -- 5: cursor's child = parent
    .storePtr 2 2 0,      -- 6: parent's parent = cursor
    .storePtr 2 0 3,      -- 7: cursor's parent = grandparent
    .null 5,             -- 8
    .ifPtrEq 3 5 16,     -- 9: root case
    .loadPtr 6 0 3,      -- 10
    .ifPtrEq 6 2 14,     -- 11: parent was grandparent's left child
    .storePtr 1 3 0,     -- 12: right link
    .goto 17,            -- 13
    .storePtr 0 3 0,     -- 14: left link
    .goto 17,            -- 15
    .movePtr 1 0,        -- 16: root register
    .halt ]             -- 17

def program {w e : Nat} : Multifinger.Opcode → List (Instruction w e regs)
  | .downLeft => move 0
  | .downRight => move 1
  | .upLeft | .upRight => move 2
  | .rotateLeftChild => rotate 0 1
  | .rotateRightChild => rotate 1 0

/-- Each invocation starts at its entry. Registers and heap persist. -/
def start {w e : Nat} (s : State w e regs) : State w e regs := { s with pc := 0 }

/-- A finite evaluator used to name endpoints, not an extra machine primitive. -/
def run {w e : Nat} (code : List (Instruction w e regs)) : Nat → State w e regs → State w e regs
  | 0, s => s
  | n + 1, s => match Cslib.PointerMachine.step code s with
    | none => s
    | some t => run code n t

end RotationBST.RealWorld.Linked
