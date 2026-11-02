module

public import RotationBST.Tango.State.Nesting.Matching

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private def annotate (lo : Nat) : List MarkedTree → List (Nat × MarkedTree)
  | [] => []
  | s :: ss => (lo, s) :: annotate (lo + s.tree.size + 1) ss

private theorem annotate_append (xs ys : List MarkedTree) (lo : Nat) :
    annotate lo (xs ++ ys) = annotate lo xs ++
      annotate (lo + (xs.map fun s => s.tree.size + 1).sum) ys := by
  induction xs generalizing lo with
  | nil => simp [annotate]
  | cons s ss ih => simp [annotate, ih, Nat.add_assoc]

theorem fringe_span (s : MarkedTree) :
    (s.fringe.map fun t => t.tree.size + 1).sum = s.tree.size + 1 := by
  have h := ComponentNesting.fringe_span s.nesting
  rw [nesting_fringe, List.map_map] at h
  simpa only [Function.comp_def, nesting_span] using h

private theorem fringeAt_annotate (s : MarkedTree) (lo : Nat) :
    s.fringeAt lo = annotate lo s.fringe := by
  induction s generalizing lo with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp only [fringeAt, fringe, Bool.false_eq_true, ite_false, ite_true, annotate_append,
        fringe_span, il, ir, annotate,
        Nat.add_assoc, List.singleton_append]

private theorem annotate_matching {xs ys : List MarkedTree}
    (matching : List.Forall₂ (fun a b : MarkedTree => a.nesting = b.nesting) xs ys) (lo : Nat) :
    List.Forall₂ (fun a b : Nat × MarkedTree => a.1 = b.1 ∧ a.2.nesting = b.2.nesting)
      (annotate lo xs) (annotate lo ys) := by
  induction matching generalizing lo with
  | nil => exact .nil
  | @cons a b xs ys h hs ih =>
    have sizes := nesting_size_eq h
    simp only [annotate]
    exact .cons ⟨rfl, h⟩ (sizes ▸ ih (lo + a.tree.size + 1))

/-- Matching nesting identifies the corresponding attached component at the
same absolute inorder offset, even after auxiliary shapes have changed. -/
theorem fringeAt_matching {s t : MarkedTree} (same : s.nesting = t.nesting) (lo : Nat) :
    List.Forall₂ (fun a b : Nat × MarkedTree => a.1 = b.1 ∧ a.2.nesting = b.2.nesting)
      (s.fringeAt lo) (t.fringeAt lo) := by
  rw [fringeAt_annotate, fringeAt_annotate]
  exact annotate_matching (nesting_fringe_matching same) lo

end RotationBST.Tango.MarkedTree
