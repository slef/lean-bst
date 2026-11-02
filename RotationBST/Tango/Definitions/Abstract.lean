module

public import RotationBST.Model.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- The reference-tree convention of Demaine–Harmon–Iacono–Pătraşcu:
the node itself belongs to its left region. `true` denotes that region. -/
def regions (leftSize size : Nat) (xs : List Nat) : List Bool :=
  (xs.filter (· < size)).map (· ≤ leftSize)

def leftRequests (leftSize : Nat) (xs : List Nat) : List Nat :=
  xs.filter (· < leftSize)

def rightRequests (leftSize : Nat) (xs : List Nat) : List Nat :=
  (xs.filter (leftSize < ·)).map (· - leftSize - 1)

/-- Number of switches between consecutive nonempty region observations. -/
def alternations : List Bool → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) + alternations (b :: xs)

/-- Wilber's interleave quantity for an arbitrary fixed unlabelled reference
BST. This definition alone does not assert the BST lower-bound theorem. -/
def interleave : Tree → List Nat → Nat
  | .nil, _ => 0
  | .node l r, xs => alternations (regions l.size (l.size + 1 + r.size) xs) +
      interleave l (leftRequests l.size xs) + interleave r (rightRequests l.size xs)

/-- A first observation initializes a preference, and does not count as a switch. -/
def switch (past : List Bool) (next : Bool) : Nat :=
  match past.getLast? with
  | none => 0
  | some previous => if previous = next then 0 else 1

/-- Actual preference switches on the reference search path for one request. -/
def changes : Tree → List Nat → Nat → Nat
  | .nil, _, _ => 0
  | .node l r, past, x =>
      if x < l.size + 1 + r.size then
        switch (regions l.size (l.size + 1 + r.size) past) (x ≤ l.size) +
        if x < l.size then changes l (leftRequests l.size past) x
        else if x = l.size then 0
        else changes r (rightRequests l.size past) (x - l.size - 1)
      else 0

/-- Total changes made while processing a sequence online. -/
def changeCost (t : Tree) : List Nat → List Nat → Nat
  | _, [] => 0
  | past, x :: xs => changes t past x + changeCost t (past ++ [x]) xs

/-- Height bounds the number of keys in any preferred path, independently of
how that path is represented as an auxiliary balanced search tree. -/
def height : Tree → Nat
  | .nil => 0
  | .node l r => 1 + max (height l) (height r)

/-- A perfect reference tree, useful when the key count is `2^h - 1`. -/
def perfect : Nat → Tree
  | 0 => .nil
  | h + 1 => .node (perfect h) (perfect h)

/-- A preferred path is an ordinary downward path in the reference tree. -/
inductive DownwardPath : Tree → List Bool → Prop
  | stop (l r : Tree) : DownwardPath (.node l r) []
  | left {l r : Tree} {path : List Bool} :
      DownwardPath l path → DownwardPath (.node l r) (true :: path)
  | right {l r : Tree} {path : List Bool} :
      DownwardPath r path → DownwardPath (.node l r) (false :: path)

end RotationBST.Tango
