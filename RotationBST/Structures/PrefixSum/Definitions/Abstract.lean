module

public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace RotationBST.PrefixSum

/-- Dense natural-number matrix, with zero outside its stored rectangle. -/
abbrev Table := Array (Array Nat)

def get (t : Table) (a b : Nat) : Nat := (t[a]?.getD #[])[b]?.getD 0

/-- Mathematical prefix sum over a half-open rectangle from the origin. -/
def sumPrefix (f : Nat → Nat → Nat) (a b : Nat) : Nat :=
  ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f i j

/-- Prefix sums of a single row, including the empty prefix. -/
def row (f : Nat → Nat) : Nat → Array Nat
  | 0 => #[0]
  | n + 1 => let previous := row f n; previous.push (previous[n]?.getD 0 + f n)

/-- Build two-dimensional prefixes by adding each row's horizontal prefixes to
those of all preceding rows. Width is fixed; the final argument is row count. -/
def build (f : Nat → Nat → Nat) (width : Nat) : Nat → Table
  | 0 => #[Array.replicate (width + 1) 0]
  | height + 1 =>
      let previous := build f width height
      let horizontal := row (f height) width
      previous.push (Array.ofFn fun b : Fin (width + 1) =>
        get previous height b.val + horizontal[b.val]?.getD 0)

/-- Four cached prefix values answer a half-open rectangular sum query. The
positive terms are added before subtracting, avoiding truncated intermediates. -/
def rectangle (t : Table) (a b c d : Nat) : Nat :=
  get t b d + get t a c - (get t a d + get t b c)

end RotationBST.PrefixSum
