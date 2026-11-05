module

public import RotationBST.Models.LinkedSearch.Definitions.Abstract
public import RotationBST.Models.Labelled.Search.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LinkedSearch

theorem attach_erase {ι : Type} (target : Nat → ι) (t : LabelledTree Nat) :
    (attach target t).erase = t.erase := by
  induction t with
  | nil => rfl
  | node l key r il ir => simp only [attach, LabelledTree.erase, il, ir]

/-- Attaching links changes neither comparisons nor the number of visited nodes. -/
theorem attach_lookup {ι : Type} (target : Nat → ι) (t : LabelledTree Nat) (x : Nat) :
    lookup (attach target t) x =
      (if (LabelledTree.lookup t x).1 then some (target x) else none, (LabelledTree.lookup t x).2) := by
  induction t with
  | nil => rfl
  | node l key r il ir =>
    by_cases low : x < key
    · simp [attach, lookup, LabelledTree.lookup, low, il]
    · by_cases equal : x = key
      · subst x; simp [attach, lookup, LabelledTree.lookup]
      · simp [attach, lookup, LabelledTree.lookup, low, equal, ir]

theorem lookup_search {ι : Type} (t : LabelledTree (Entry ι)) (x : Nat) :
    Search t x (lookup t x).1 (lookup t x).2 := by
  induction t with
  | nil => exact .empty x
  | node l entry r il ir =>
    by_cases low : x < entry.key
    · simpa only [lookup, low, ↓reduceIte] using Search.left low il
    · by_cases equal : x = entry.key
      · subst x
        simpa only [lookup, Nat.lt_irrefl, ↓reduceIte] using Search.found l r entry
      · have high : entry.key < x := by omega
        simpa only [lookup, low, equal, ↓reduceIte] using Search.right high ir

/-- Every successful executable query has a legal linked-pointer execution
with exactly its computed cost and returned root pointer. -/
theorem request_correct {ι : Type} (s : Store ι) (current next : ι) (x : Nat)
    (success : (request s current x).1 = some next) :
    Request s current x next (request s current x).2 := by
  have first := lookup_search (s.roots current) x
  cases result : (lookup (s.roots current) x).1 with
  | some q =>
    have same : q = next := by simpa only [request, result, Option.some.injEq] using success
    subst q
    rw [result] at first
    simpa only [request, result] using Request.hit first
  | none =>
    have last := lookup_search s.fallback x
    have found : (lookup s.fallback x).1 = some next := by simpa only [request, result] using success
    rw [result] at first
    rw [found] at last
    simpa only [request, result] using Request.miss first last

end RotationBST.LinkedSearch
