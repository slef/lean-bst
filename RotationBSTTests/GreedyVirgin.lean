module

public import RotationBST.Algorithms.GreedyASS.Virgin.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.GreedyVirgin
open Geometric Geometric.GreedyASS.Reference Geometric.GreedyASS.Virgin

private def pair : Tree := .node .nil .nil
private def four : Tree := .node pair pair
private def leftRoot : Component := ⟨0, pair⟩
private def middleRoot : Component := ⟨2, .nil⟩
private def rightRoot : Component := ⟨3, .nil⟩

-- The old status is obtained from the exact lifetime recurrence, not assumed
-- as a separate classification of roots. Two roots are old and one is virgin.
private theorem old_iff (c : Component) :
    NonVirgin four 0 [0, 3] 2 c ↔ c = leftRoot ∨ c = rightRoot := by
  have first := Results.lifetime four 0 [] 0 3 c
  have second := Results.lifetime four 0 [0] 3 2 c
  have row0 : keys [] 0 = {0} := by decide
  have row1 : keys [0] 3 = {0, 3} := by decide
  have forest0 : forest four 0 0 = [⟨0, .nil⟩, ⟨1, .nil⟩, ⟨2, pair⟩] := by decide
  have forest2 : forest four 0 2 = [leftRoot, middleRoot, rightRoot] := by decide
  have forest3 : forest four 0 3 = [leftRoot, middleRoot, rightRoot] := by decide
  simp only [List.nil_append] at first
  simp only [List.cons_append, List.nil_append] at second
  rw [second, first]
  simp only [Results.initial, false_or, row0, row1, forest0, forest2, forest3,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨hc, h⟩
    rcases hc with rfl | rfl | rfl
    · exact Or.inl rfl
    · simp [middleRoot, leftRoot, rightRoot, pair, Component.Contains, Component.last, leaves] at h
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;>
      simp [leftRoot, rightRoot, middleRoot, pair, Component.Contains, Component.last, leaves]

private theorem touched_eq : touched four 0 [0, 3] 2 = {leftRoot, middleRoot, rightRoot} := by
  classical
  have row2 : keys [0, 3] 2 = {0, 2, 3} := by decide
  have fs : forest four 0 2 = [leftRoot, middleRoot, rightRoot] := by decide
  ext c
  simp only [touched, fs, List.toFinset_cons, List.toFinset_nil, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false, row2]
  constructor
  · exact fun h => h.1
  · intro hc
    refine ⟨hc, ?_⟩
    rcases hc with rfl | rfl | rfl <;>
      simp [leftRoot, middleRoot, rightRoot, pair, Component.Contains, Component.last, leaves]

private theorem old_eq : oldTouched four 0 [0, 3] 2 = {leftRoot, rightRoot} := by
  classical
  ext c
  simp only [oldTouched, touched_eq, Finset.mem_filter, old_iff,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem virgins_eq : roots four 0 [0, 3] 2 = {middleRoot} := by
  classical
  have fs : forest four 0 2 = [leftRoot, middleRoot, rightRoot] := by decide
  ext c
  simp only [roots, fs, Finset.mem_filter, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false, old_iff, Finset.mem_singleton]
  constructor
  · tauto
  · rintro rfl
    simp [middleRoot, leftRoot, rightRoot, pair]

-- Both counting and potential-drop constants are attained in this execution:
-- the new row touches three roots, of which exactly two were already used.
example : (oldTouched four 0 [0, 3] 2).card = 2 := by rw [old_eq]; decide
example : (touched four 0 [0, 3] 2).card = 3 := by rw [touched_eq]; decide
example : before four 0 [0, 3] 2 = 12 ∧ after four 0 [0, 3] 2 = 0 := by
  rw [before, after, virgins_eq, touched_eq]
  decide

-- A root which disappears loses the prior lifetime, even if it later returns.
example : ¬ NonVirgin four 0 [0, 3] 0 ⟨0, .nil⟩ := by
  have recurrence := Results.lifetime four 0 [0] 3 0 (⟨0, .nil⟩ : Component)
  simp only [List.cons_append, List.nil_append] at recurrence
  rw [recurrence]
  intro h
  rcases h.2 with old | touched
  · have member := old_member old
    exact (by decide : (⟨0, .nil⟩ : Component) ∉ forest four 0 3) member
  · exact (by decide : (⟨0, .nil⟩ : Component) ∉ forest four 0 3) touched.1

-- A singleton searched repeatedly is genuinely non-virgin, rather than
-- excluded from the count to avoid the reference-forest boundary case.
example : NonVirgin .nil 0 [0] 0 ⟨0, .nil⟩ := by
  have recurrence := Results.lifetime .nil 0 [] 0 0 (⟨0, .nil⟩ : Component)
  simp only [List.nil_append] at recurrence
  rw [recurrence]
  simp [forest, Results.initial, keys, points, fill, greedySweep, Component.Contains,
    Component.last, leaves, Visible]

example (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t) :
    after t lo history request + 12 * (touched t lo history request).card ≤
      before t lo history request + 24 := Results.decrease t lo history request valid

end RotationBST.Tests.GreedyVirgin
