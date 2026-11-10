module

public import RotationBST.Models.Dictionary.Abstract
public import RotationBST.Algorithms.Splay.Updates.Dictionary.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.Dictionary
open RotationBST.Dictionary

private def one : Tree := .node .nil .nil
private def three : Tree := .node one one

-- Two children: only the root of `three`.
example : three.TwoChildren 1 ∧ ¬ three.TwoChildren 0 ∧ ¬ three.TwoChildren 2 := by decide

-- A leaf insertion at gap 0 of `three` with no rebalancing: the new node is at
-- depth 2, so the main cost is 3; one datum (a rank, say) is then edited.
private def ranked : LabelledTree Nat := .node (.node .nil 0 .nil) 1 (.node .nil 0 .nil)
private def grown : LabelledTree Nat := .node (.node (.node .nil 0 .nil) 0 .nil) 1 (.node .nil 0 .nil)
private def promoted : LabelledTree Nat := .node (.node (.node .nil 0 .nil) 1 .nil) 1 (.node .nil 0 .nil)

example : Step ranked (.insert 0) promoted 3 1 := by
  have sp : Splice grown 0 ranked := .inLeft (.inLeft .noLeft)
  have ed : Moves grown promoted 0 1 := .edit (.inLeft .here) .refl
  have := Step.insert (s := ranked) (k := 0) (by decide) .refl sp ed
  simpa [grown, LabelledTree.erase, Tree.depth, Tree.size] using this

-- Deleting the root of `three`, which has two children, by splicing its
-- successor (rank 2): the root keeps its own datum.
example : Step ranked (.delete 1) (.node (.node .nil 0 .nil) 1 .nil) 2 0 := by
  have sp : Splice ranked 2 (.node (.node .nil 0 .nil) 1 .nil) := by
    have := Splice.inRight (l := .node .nil 0 .nil) (d := 1) (Splice.noLeft (d := 0) (r := .nil))
    simpa [ranked, LabelledTree.erase, Tree.size] using this
  have := Step.delete (s := ranked) (x := 1) (y := 2) (by decide)
    (Or.inr ⟨by decide, Or.inr rfl⟩) .refl sp .refl
  simpa [ranked, LabelledTree.erase, Tree.depth, Tree.size] using this

-- Static searches cost `∑ (1 + depth)`.
example : Dictionary.Execution three.unit ([0, 1, 2].map .access) three.unit 5 0 := by
  have := Results.static_execution three.unit [0, 1, 2] (by decide)
  simpa [three, one, Tree.unit, LabelledTree.erase, Tree.depth, Tree.size] using this

-- The rotation model embeds with main cost at most `m + 2R`.
example {s t : Tree} {xs : List Nat} {k : Nat} (h : RotationBST.Execution s xs t k) :
    ∃ c, Dictionary.Execution s.unit (xs.map .access) t.unit c 0 ∧ c ≤ xs.length + 2 * k :=
  Results.of_execution h

-- Splay updates are dictionary steps within a factor of three.
example : ∃ c, Step three.unit (.insert 3) (Splay.Updates.insert three 3).1.unit c 0 ∧
    c ≤ 3 * ((Splay.Updates.insert three 3).2 + 1) :=
  Splay.Updates.Results.dictionary_insert three 3 (by decide)
example : ∃ c, Step three.unit (.delete 1) (Splay.Updates.delete three 1).1.unit c 0 ∧
    c ≤ 2 * ((Splay.Updates.delete three 1).2 + 1) :=
  Splay.Updates.Results.dictionary_delete three 1 (by decide)

end RotationBST.Tests.Dictionary
