module

public import RotationBST.Models.RealWorld.Linked.Abstract
public import RotationBST.Models.RealWorld.Definitions.Abstract

@[expose] public section
namespace RotationBST.RealWorld.Compiler

abbrev Target (w f r : Nat) := Linked.State w f (r + 4)
abbrev Opcode (w f r : Nat) := Linked.Instruction w f (r + 4)

/-- User registers occupy an initial segment; four private scalar registers
hold the current request, visited flag, key temporary and zero temporary. -/
def userReg {r : Nat} (i : Fin r) : Fin (r + 4) := ⟨i, by omega⟩
def queryReg (r : Nat) : Fin (r + 4) := ⟨r, by omega⟩
def seenReg (r : Nat) : Fin (r + 4) := ⟨r + 1, by omega⟩
def tempReg (r : Nat) : Fin (r + 4) := ⟨r + 2, by omega⟩
def zeroReg (r : Nat) : Fin (r + 4) := ⟨r + 3, by omega⟩

def field {f : Nat} (i : Fin f) : Fin (f + 1) := ⟨i + 1, by omega⟩

def stride : Nat := 24
def address {l : Nat} (pc : Fin l) : Nat := stride * pc.val
def boundary (l : Nat) : Nat := stride * l
def trap (l : Nat) : Nat := boundary l + 1
def entry (l : Nat) : Nat := boundary l + 2

/-- Relocate a primitive into a block and replace its halt by a charged
continuation jump. There is only one actual halt in the compiled program. -/
def relocate {w f r : Nat} (base exit : Nat) : Opcode w f r → Opcode w f r
  | .goto k => .goto (base + k)
  | .ifPtrEq a b k => .ifPtrEq a b (base + k)
  | .ifTest p a b k => .ifTest p a b (base + k)
  | .halt => .goto exit
  | i => i

/-- Machine code for each semantic instruction. All bookkeeping is charged. -/
def block {w f r l : Nat} (base : Nat) : Instruction f r l → List (Opcode w f r)
  | .literal dst value next =>
      [.op (.literal value) (userReg dst) (zeroReg r) (zeroReg r), .goto (address next)]
  | .copy dst src next => [.moveData (userReg dst) (userReg src), .goto (address next)]
  | .add dst a b next => [.op .add (userReg dst) (userReg a) (userReg b), .goto (address next)]
  | .sub dst a b next => [.op .sub (userReg dst) (userReg a) (userReg b), .goto (address next)]
  | .branch a b yes no => [.ifTest .lt (userReg a) (userReg b) (address yes), .goto (address no)]
  | .load dst i next => [.loadData (userReg dst) (field i) 0, .goto (address next)]
  | .store i src next => [.storeData (field i) 0 (userReg src), .goto (address next)]
  | .key dst next => [.loadData (userReg dst) 0 0, .goto (address next)]
  | .query dst next => [.moveData (userReg dst) (queryReg r), .goto (address next)]
  | .bst op next => (Linked.program op).map (relocate base (address next))
  | .mark next =>
      [.loadData (tempReg r) 0 0, .ifTest .eq (tempReg r) (queryReg r) (base + 3),
       .goto (trap l), .op (.literal 1) (seenReg r) (zeroReg r) (zeroReg r),
       .goto (address next)]
  | .finish =>
      [.op (.literal 0) (zeroReg r) (zeroReg r) (zeroReg r),
       .ifTest .eq (seenReg r) (zeroReg r) (trap l), .goto (boundary l)]

/-- The whole controller is one finite program. Padding and failed checks go
to a nonhalting trap. Entry resets the visited flag using a machine instruction. -/
def compile {w f r l : Nat} (p : Machine f r l) : List (Opcode w f r) :=
  List.ofFn fun i : Fin (boundary l + 4) =>
    if h : i.val < boundary l then
      let pc : Fin l := ⟨i.val / stride, (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
        simpa [boundary, Nat.mul_comm] using h)⟩
      ((block (address pc) (p.code pc))[i.val % stride]?).getD (.goto (trap l))
    else if i.val = boundary l then .halt
    else if i.val = entry l then .op (.literal 0) (seenReg r) (zeroReg r) (zeroReg r)
    else if i.val = entry l + 1 then .goto (address p.entry)
    else .goto (trap l)

/-- Supplying a request is permitted only at the unique successful halt.
It preserves the heap and all registers except the designated input register.
Resetting the visited flag and jumping to source entry are charged code. -/
def accept {w f r l : Nat} (key : BitVec w) (s : Target w f r) : Option (Target w f r) :=
  if s.pc = boundary l then some { s.setData (queryReg r) key with pc := entry l } else none

variable {w f r l : Nat}

def decode (x : Linked.Label w f) : Node w f :=
  ⟨x.2 0, fun i => x.2 (field i)⟩

def flag (w : Nat) (seen : Bool) : BitVec w := BitVec.ofNat w (if seen then 1 else 0)

def location {l : Nat} : Option (Fin l) → Nat
  | none => boundary l
  | some pc => address pc

/-- The full compiler invariant: linked representation, user registers,
current input, visited flag and control label. The address-labelled cursor
is ghost state; only the fixed-size machine state is available at runtime. -/
def Image (s : State w f r l) (t : Target w f r) : Prop :=
  ∃ c, Linked.Realizes t c ∧ s.cursor = c.map decode ∧
    (∀ i, t.data (userReg i) = s.regs i) ∧
    t.data (queryReg r) = s.request ∧ t.data (seenReg r) = flag w s.seen ∧
    t.pc = location s.pc


/-- A completed request in the one compiled program, including its halt. -/
def Responds {w f r l : Nat} (p : Machine f r l) (s : Target w f r)
    (key : BitVec w) (t : Target w f r) (time : Nat) : Prop :=
  ∃ input, accept (l := l) key s = some input ∧
    Cslib.PointerMachine.Executes (compile p) input t time

/-- The same code is reused for the whole request sequence. -/
inductive Execution {w f r l : Nat} (p : Machine f r l) :
    Target w f r → List (BitVec w) → Target w f r → Nat → Prop where
  | nil (s) : Execution p s [] s 0
  | cons {s t u key rest a b} : Responds p s key t a →
      Execution p t rest u b → Execution p s (key :: rest) u (a + b)

end RotationBST.RealWorld.Compiler
