module

public import RotationBST.Models.Pointer.Lazy.Online.Existence

@[expose] public section

namespace RotationBST.Pointer.Lazy.Online

/-- Every valid current request has a certified simulation step. -/
theorem advance_exists (a : Algorithm) (past : List Nat) (s : State) (x : Nat)
    (valid : x < s.virtual.size) : ∃ result, Transition a past s x result :=
  transition_exists a past s x valid

/-- Choose a certified implementation using only the current request, past and
simulation state. Classical choice fixes this rule once, independently of future
requests. Planning is uncharged, as in the underlying abstract BST models. -/
noncomputable def advance (a : Algorithm) (past : List Nat) (s : State) (x : Nat) : State × Nat :=
  if valid : x < s.virtual.size then Classical.choose (advance_exists a past s x valid)
  else (s, 0)

noncomputable def run (a : Algorithm) (past : List Nat) (s : State) : List Nat → State × Nat
  | [] => (s, 0)
  | x :: xs =>
      let next := advance a past s x
      let rest := run a (past ++ [x]) next.1 xs
      (rest.1, next.2 + rest.2)

end RotationBST.Pointer.Lazy.Online
