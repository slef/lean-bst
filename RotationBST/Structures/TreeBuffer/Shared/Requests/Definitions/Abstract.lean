module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Shared.Requests

/-- A requested key occurs at a real persistent finger between two parts of
the same shared-node trace. Work after the visit is retained and charged. -/
def Visit {α : Type} {fingers : Nat} (s t : State α fingers) (x : Nat)
    (events : List (Cells.Event α)) (cost : Nat) : Prop :=
  ∃ visited before after first last i,
    Trace s visited before first ∧ visited.position i = x ∧ Trace visited t after last ∧
      events = before ++ after ∧ cost = first + last

/-- A shared-node request sequence includes one explicit request charge as
well as all pointer, cell, routing, and maintenance work. -/
inductive Execution {α : Type} {fingers : Nat} : State α fingers → List Nat → State α fingers →
    List (Cells.Event α) → Nat → Prop where
  | nil {s : State α fingers} : Execution s [] s [] 0
  | cons {s t u : State α fingers} {x cost rest : Nat} {xs : List Nat} {first last : List (Cells.Event α)} :
      Visit s t x first cost → Execution t xs u last rest → Execution s (x :: xs) u (first ++ last) (1 + cost + rest)

end RotationBST.TreeBuffer.Shared.Requests
