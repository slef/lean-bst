module

public import RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

theorem decode_top (stack : Layer) :
    stack.decode = stack.topTail.elim stack.top (WeightedTree.node stack.top) := by
  cases stack with
  | last rs icing => cases rs <;> rfl
  | next rs child icing => cases rs <;> rfl

theorem replaceTop_decode (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode = stack.topTail.elim new (WeightedTree.node new) := by
  cases stack with
  | last rs icing => cases rs <;> rfl
  | next rs child icing => cases rs <;> rfl

theorem replaceTop_top (stack : Layer) (new : WeightedTree) : (stack.replaceTop new).top = new := by
  cases stack with
  | last rs icing => cases rs <;> rfl
  | next rs child icing => cases rs <;> rfl

theorem replaceTop_tail (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).topTail = stack.topTail := by
  cases stack with
  | last rs icing => cases rs <;> rfl
  | next rs child icing => cases rs <;> rfl

theorem top_valid {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    Perfect level stack.top ∧ stack.top.Nonnegative := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero =>
      obtain ⟨crumb, rfl⟩ := valid.2.2 rfl
      exact valid.2.1
    | one a => exact valid.1
    | two a b => exact valid.1.1
    | three a b c => exact valid.1.1
  | next rs child icing =>
    cases rs with
    | zero => exact False.elim (valid.2.2.2.1 rfl)
    | one a => exact valid.1
    | two a b => exact valid.1.1
    | three a b c => exact valid.1.1

theorem replaceTop_valid {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {new : WeightedTree} (perfect : Perfect level new) (nonnegative : new.Nonnegative) :
    (stack.replaceTop new).Valid level := by
  have replacement := And.intro perfect nonnegative
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => exact ⟨trivial, replacement, fun _ => ⟨_, rfl⟩⟩
    | one a => exact ⟨replacement, valid.2.1, by intro h; cases h⟩
    | two a b => exact ⟨⟨replacement, valid.1.2⟩, valid.2.1, by intro h; cases h⟩
    | three a b c => exact ⟨⟨replacement, valid.1.2⟩, valid.2.1, by intro h; cases h⟩
  | next rs child icing =>
    cases rs with
    | zero => exact False.elim (valid.2.2.2.1 rfl)
    | one a => exact ⟨replacement, valid.2.1, valid.2.2.1, (by intro h; cases h), valid.2.2.2.2⟩
    | two a b => exact ⟨⟨replacement, valid.1.2⟩, valid.2.1, valid.2.2.1, (by intro h; cases h), valid.2.2.2.2⟩
    | three a b c => exact ⟨⟨replacement, valid.1.2⟩, valid.2.1, valid.2.2.1, (by intro h; cases h), valid.2.2.2.2⟩

/-- The replaced crumb is outside all frozen metadata and icing comparisons. -/
theorem replaceTop_potential {stack : Layer} {level : Nat} (valid : stack.Valid level) (new : WeightedTree) :
    (stack.replaceTop new).potential = stack.potential := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => obtain ⟨crumb, rfl⟩ := valid.2.2 rfl; rfl
    | one a => rfl
    | two a b => rfl
    | three a b c => rfl
  | next rs child icing =>
    cases rs with
    | zero => exact False.elim (valid.2.2.2.1 rfl)
    | one a => rfl
    | two a b => rfl
    | three a b c => rfl

theorem replaceTop_mass (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode.mass + stack.top.mass = stack.decode.mass + new.mass := by
  rw [replaceTop_decode, decode_top stack]
  cases stack.topTail <;> simp only [Option.elim, WeightedTree.mass] <;> ring

theorem replaceTop_size (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode.tree.size + stack.top.tree.size = stack.decode.tree.size + new.tree.size := by
  rw [replaceTop_decode, decode_top stack]
  cases stack.topTail <;> simp only [Option.elim, WeightedTree.tree, WeightedTree.skeleton,
    Pointer.Lazy.Skeleton.tree, Tree.size] <;> omega

/-- A supplied physical payload transformation lifts to the whole stack with
at most one downward and one upward move. Replacement itself is not a trace. -/
theorem replaceTop_lift (stack : Layer) (new : WeightedTree) {cost : Nat}
    (oldNonempty : stack.top.tree ≠ .nil) (newNonempty : new.tree ≠ .nil)
    (trace : Pointer.Trace ⟨stack.top.tree, []⟩ ⟨new.tree, []⟩ cost) :
    ∃ total, total ≤ cost + 2 ∧
      Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨(stack.replaceTop new).decode.tree, []⟩ total := by
  rw [decode_top stack, replaceTop_decode]
  cases tail : stack.topTail with
  | none => exact ⟨cost, by omega, trace⟩
  | some suffix =>
    have lifted := trace.inContext oldNonempty newNonempty [.left suffix.tree]
    refine ⟨cost + 2, le_rfl, ?_⟩
    simpa [Pointer.plug, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted

/-- Two or more fringe entries force a real separator at level zero. -/
theorem hasTop_of_fringe {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {suffix : List (Tree × ℝ)}
    (fringe : stack.decode.fringe = (subtree, weight) :: suffix) (nonempty : suffix ≠ []) :
    stack.HasTop := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero =>
      obtain ⟨crumb, rfl⟩ := valid.2.2 rfl
      have perfect := valid.2.1.1
      cases perfect with
      | leaf t w =>
        change [(t, w)] = (subtree, weight) :: suffix at fringe
        have tail := (List.cons.inj fringe).2
        exact False.elim (nonempty tail.symm)
    | one | two | three => trivial
  | next rs child icing =>
    cases rs with
    | zero => exact False.elim (valid.2.2.2.1 rfl)
    | one | two | three => trivial

/-- Pop the specified first occurrence, retaining the exact remaining fringe. -/
theorem pop_front {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {suffix : List (Tree × ℝ)}
    (fringe : stack.decode.fringe = (subtree, weight) :: suffix) (nonempty : suffix ≠ []) :
    ∃ rest, stack.pop = some (.leaf subtree weight, rest) ∧ rest.Valid 0 ∧
      rest.decode.fringe = suffix ∧ stack.decode.mass = weight + rest.decode.mass ∧
      stack.popCost + rest.potential ≤ 20 + stack.potential := by
  obtain ⟨crumb, rest, popped, perfect, _, restValid, remaining, mass, _, bound⟩ :=
    Chocolate.Results.pop valid (hasTop_of_fringe valid fringe nonempty) []
  cases perfect with
  | leaf t w =>
    rw [fringe] at remaining
    change (subtree, weight) :: suffix = (t, w) :: rest.decode.fringe at remaining
    obtain ⟨head, tail⟩ := List.cons.inj remaining
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj head
    exact ⟨rest, popped, restValid, tail.symm, mass, bound⟩

/-- Successive top replacements retain the same suffix metadata. -/
theorem replaceTop_replaceTop (stack : Layer) (first second : WeightedTree) :
    (stack.replaceTop first).replaceTop second = stack.replaceTop second := by
  cases stack with
  | last rs icing => cases rs <;> rfl
  | next rs child icing => cases rs <;> rfl

end RotationBST.PopTart.Chocolate
