module

public import RotationBST.Models.Labelled.Search.Labelling
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LabelledTree

/-- The executable lookup follows the counted child-pointer search semantics. -/
theorem lookup_search (t : LabelledTree Nat) (x : Nat) : Search t x (lookup t x).1 (lookup t x).2 := by
  induction t with
  | nil => exact .empty x
  | node l key r il ir =>
    unfold lookup
    split
    · exact .left ‹_› il
    · split
      · rename_i equal
        subst x
        exact .found l r key
      · exact .right (by omega) ir

/-- On a BST, the search succeeds precisely for keys actually stored. This
includes unsuccessful searches between sparse keys and beyond either endpoint. -/
theorem lookup_correct (t : LabelledTree Nat) (ordered : t.Ordered) (x : Nat) :
    (lookup t x).1 = true ↔ x ∈ t.inorder := by
  induction t with
  | nil => simp [lookup, inorder]
  | node l key r il ir =>
    rcases ordered with ⟨ol, or, left, right⟩
    by_cases low : x < key
    · have unequal : x ≠ key := by omega
      have notRight : x ∉ r.inorder := by intro member; have := right x member; omega
      simp only [lookup, low, ↓reduceIte, inorder, List.mem_append, List.mem_cons,
        il ol, notRight, unequal, or_false]
    · by_cases equal : x = key
      · subst x
        simp [lookup, inorder]
      · have notLeft : x ∉ l.inorder := by intro member; have := left x member; omega
        simp only [lookup, low, equal, ↓reduceIte, inorder, List.mem_append,
          List.mem_cons, ir or, notLeft, false_or]

theorem lookup_labelWith (t : Tree) (keys : List Nat) (same : keys.length = t.size)
    (ordered : keys.Pairwise (· < ·)) (x : Nat) :
    (lookup (t.labelWith keys) x).1 = true ↔ x ∈ keys := by
  rw [lookup_correct _ (t.labelWith_ordered keys same ordered), t.labelWith_inorder keys same]

end RotationBST.LabelledTree
