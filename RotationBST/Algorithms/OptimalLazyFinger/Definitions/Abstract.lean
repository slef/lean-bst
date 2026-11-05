module

public import RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract
public import RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Definitions.Abstract
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace RotationBST.OptimalLazyFinger

/-- A constructed shape paired with its boundary-toll cost. -/
abbrev Entry := Tree × Nat

/-- Keep the cheaper candidate, breaking ties in favor of the first. -/
def choose (a b : Entry) : Entry := if a.2 ≤ b.2 then a else b

/-- Fold a finite family of candidates with a supplied initial candidate. -/
def minimum (initial : Entry) (candidates : List Entry) : Entry :=
  candidates.foldr choose initial

/-- Bellman's interval recurrence with reconstruction of a minimizing shape.
This direct evaluator recomputes shared subproblems; tabulation is needed for
the paper's cubic running time. `n` is the interval length, `lo` its first key. -/
def solve (w : Nat → Nat → Nat) : (n lo : Nat) → Entry
  | 0, _ => (.nil, 0)
  | n + 1, lo =>
      let candidate (k : Fin (n + 1)) : Entry :=
        let l := solve w k.val lo
        let r := solve w (n - k.val) (lo + k.val + 1)
        (.node l.1 r.1, w lo (lo + n + 1) + l.2 + r.2)
      minimum (candidate ⟨0, Nat.zero_lt_succ n⟩) ((List.finRange (n + 1)).map candidate)
termination_by n => n
decreasing_by all_goals omega

/-- Total table lookup; correctness uses only entries within the built rows. -/
def lookup (table : Array (Array Entry)) (n lo : Nat) : Entry :=
  (table[n]?.getD #[])[lo]?.getD (.nil, 0)

/-- One row for each interval length, evaluated from shorter intervals upward.
The universe size fixes the row width. Invalid intervals are unused. -/
def tabulate (w : Nat → Nat → Nat) (univSize : Nat) : Nat → Array (Array Entry)
  | 0 => #[Array.replicate (univSize + 1) (.nil, 0)]
  | n + 1 =>
      let previous := tabulate w univSize n
      previous.push (Array.ofFn fun lo : Fin (univSize + 1) =>
        if lo.val + n + 1 ≤ univSize then
          let candidate (k : Fin (n + 1)) : Entry :=
            let l := lookup previous k.val lo.val
            let r := lookup previous (n - k.val) (lo.val + k.val + 1)
            (.node l.1 r.1, w lo.val (lo.val + n + 1) + l.2 + r.2)
          minimum (candidate ⟨0, Nat.zero_lt_succ n⟩) ((List.finRange (n + 1)).map candidate)
        else (.nil, 0))

/-- Table-based interval optimization, returning the shape and its cost. -/
def optimize (w : Nat → Nat → Nat) (n : Nat) : Entry :=
  lookup (tabulate w n n) n 0

/-- Optimal tree for a given initial key and sequence, obtained from its
preprocessed interval boundary-crossing counts. The extra rank permits the
virtual initial key used by the root-start variant. -/
def treeFrom (n p : Nat) (xs : List Nat) : Tree :=
  let prepared := Preprocessing.prepare (n + 1) p xs
  (optimize (Preprocessing.toll prepared (n + 1)) n).1

/-- Root-start variant. The virtual key `n` makes the initialization penalty
independent of the candidate tree's root. -/
def tree (n : Nat) (xs : List Nat) : Tree := treeFrom n n xs

end RotationBST.OptimalLazyFinger
