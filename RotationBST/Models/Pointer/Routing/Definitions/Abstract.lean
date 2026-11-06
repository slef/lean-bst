module

public import RotationBST.Models.Pointer.Walk.Definitions.Abstract

@[expose] public section
namespace RotationBST.Pointer.Routing

/-- Three bounded integers read at the current node: its key and the
half-open interval of keys in its subtree. -/
structure View where
  low : Nat
  key : Nat
  high : Nat
  deriving DecidableEq

/-- Semantic correctness of the locally stored interval. Computing offsets
and subtree sizes here is specification only; `choose` reads the three fields. -/
def View.Valid (v : View) (cursor : Config) : Prop :=
  v.low = offset cursor.context ∧ cursor.key? = some v.key ∧ v.high = v.low + cursor.focus.size

inductive Direction where
  | left | right | parent
  deriving DecidableEq

/-- Local comparisons select the unique edge toward an existing target. -/
def choose (v : View) (target : Nat) : Option Direction :=
  if target = v.key then none
  else if v.low ≤ target ∧ target < v.high then
    some (if target < v.key then .left else .right)
  else some .parent

/-- Follow one child or parent pointer. Pattern matching inspects only the
current node, whether the selected child exists, and the parent link. -/
def perform : Direction → Config → Option Config
  | .left, ⟨.node (.node a b) r, cs⟩ => some ⟨.node a b, .left r :: cs⟩
  | .right, ⟨.node l (.node a b), cs⟩ => some ⟨.node a b, .right l :: cs⟩
  | .parent, ⟨.node a b, .left r :: cs⟩ => some ⟨.node (.node a b) r, cs⟩
  | .parent, ⟨.node a b, .right l :: cs⟩ => some ⟨.node l (.node a b), cs⟩
  | _, _ => none

def next (v : View) (cursor : Config) (target : Nat) : Option Config :=
  (choose v target).bind fun direction => perform direction cursor

end RotationBST.Pointer.Routing
