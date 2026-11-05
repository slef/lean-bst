module

public import RotationBST.Models.Pointer.Machine.Abstract
public import Mathlib.Logic.Function.Basic

@[expose] public section
namespace RotationBST.Multifinger

/-- Several persistent fingers into one BST. Inorder ranks name physical keys,
so rotations preserve the identities of all inactive fingers. -/
structure State (fingers : Nat) where
  tree : Tree
  position : Fin fingers → Nat

def State.Valid {fingers : Nat} (s : State fingers) : Prop :=
  ∀ i, s.position i < s.tree.size

/-- All fingers initially point to the root; nonempty trees give valid states. -/
def initial (fingers : Nat) (t : Tree) : State fingers :=
  ⟨t, fun _ => match t with | .nil => 0 | .node l _ => l.size⟩

/-- Perform one legal existing pointer-machine instruction at the selected
finger. Every other finger retains its key, even when the shared tree rotates.
No finger teleportation or implicit resetting is included. -/
inductive Step {fingers : Nat} : State fingers → Fin fingers → State fingers → Prop where
  | execute {s : State fingers} {i : Fin fingers} {a b : Pointer.Config} {x : Nat}
      (tree : a.tree = s.tree) (key : a.key? = some (s.position i))
      (instruction : Pointer.Step a b) (touched : b.key? = some x) :
      Step s i ⟨b.tree, Function.update s.position i x⟩

/-- A trace records the touched key after each charged instruction. Its length
is the exact instruction count; the fingers persist between instructions. -/
inductive Trace {fingers : Nat} : State fingers → List Nat → State fingers → Prop where
  | refl {s : State fingers} : Trace s [] s
  | step {s t u : State fingers} {i : Fin fingers} {touches : List Nat} :
      Step s i t → Trace t touches u → Trace s (t.position i :: touches) u

/-- A request is served by visiting its key at any finger. Before/after work is
charged and fingers remain where the execution leaves them. -/
def Serves {fingers : Nat} (s t : State fingers) (x cost : Nat) : Prop :=
  ∃ visited before after i,
    Trace s before visited ∧ visited.position i = x ∧ Trace visited after t ∧
      cost = 1 + before.length + after.length

inductive Execution {fingers : Nat} : State fingers → List Nat → State fingers → Nat → Prop where
  | nil {s : State fingers} : Execution s [] s 0
  | cons {s t u : State fingers} {x k : Nat} {xs : List Nat} {m : Nat} :
      Serves s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)

end RotationBST.Multifinger
