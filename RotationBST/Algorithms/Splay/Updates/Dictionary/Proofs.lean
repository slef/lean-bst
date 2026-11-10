module

public import RotationBST.Algorithms.Splay.Updates.Basic
public import RotationBST.Models.Dictionary.Basic
import Mathlib.Tactic

@[expose] public section

/-! The splay updates are dictionary steps on trees without data. The main
cost of each is at most three times splay's own charge (one unit plus its
rotations): splaying a node walks its search path by rotating it. -/
namespace RotationBST.Splay.Updates
open Dictionary
open _root_.RotationBST.Tree (depth_left depth_root depth_right)

theorem dictionary_access (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ c, Dictionary.Step t.unit (.access x) (run t x).1.unit c 0 ∧ c ≤ 2 * ((run t x).2 + 1) := by
  have ha := (run_correct t x hx).1
  have hd := access_depth_le ha
  refine ⟨_, Step.access (by simpa using hx) (moves_of_rotations (rotations_unit ha.1)), ?_⟩
  simp only [unit_erase]; omega

theorem dictionary_insert (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    ∃ c, Dictionary.Step t.unit (.insert k) (insert t k).1.unit c 0 ∧
      c ≤ 3 * ((insert t k).2 + 1) := by
  by_cases h0 : k = 0
  · subst h0
    have hi : insert t 0 = (.node .nil t, 0) := by simp [insert, split]
    rw [hi]
    have sp : Splice (Tree.node .nil t).unit 0 t.unit := .noLeft
    refine ⟨_, Step.insert (by simp) .refl sp .refl, ?_⟩
    simp [Tree.unit, LabelledTree.erase, Tree.depth, Tree.size]
  · obtain ⟨l, r, c, ha, hs⟩ := split_spec t k hk (Nat.pos_of_ne_zero h0)
    have hl : l.size = k - 1 := ha.2
    have hi : insert t k = (.node (.node l .nil) r, c) := by simp [insert, hs]
    rw [hi]
    -- Insert the new node above `r`, then rotate it to the root.
    have sp : Splice (.node l.unit () (.node .nil () r.unit)) k (Tree.node l r).unit := by
      have := Splice.inRight (l := l.unit) (d := ()) (Splice.noLeft (d := ()) (r := r.unit))
      simp only [unit_erase, hl, Nat.add_zero] at this
      rwa [show k - 1 + 1 = k by omega] at this
    have rot : Moves (.node l.unit () (.node .nil () r.unit)) (Tree.node (.node l .nil) r).unit 1 0 :=
      .rotate .left .refl
    refine ⟨_, Step.insert (by simpa using hk) (moves_of_rotations (rotations_unit ha.1)) sp rot, ?_⟩
    have hdepth : (LabelledTree.erase (.node l.unit () (.node .nil () r.unit))).depth k = 1 := by
      simp only [LabelledTree.erase, unit_erase]
      rw [depth_right (by omega), show k - l.size - 1 = (Tree.nil).size by simp [Tree.size]; omega,
        depth_root rfl]
    rw [hdepth]; omega

theorem dictionary_delete (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ c, Dictionary.Step t.unit (.delete x) (delete t x).1.unit c 0 ∧
      c ≤ 2 * ((delete t x).2 + 1) := by
  have ha := (run_correct t x hx).1
  rcases he : run t x with ⟨u, c⟩
  rw [he] at ha
  cases u with
  | nil => exact ha.2.elim
  | node l r =>
    have hl : l.size = x := ha.2
    have m₁ := moves_of_rotations (rotations_unit ha.1)
    cases l with
    | nil =>
      have hd : delete t x = (r, c) := by simp [delete, he, join]
      rw [hd]
      have hx0 : x = 0 := by simp [Tree.size] at hl; omega
      subst hx0
      have sp : Splice (Tree.node .nil r).unit 0 r.unit := .noLeft
      refine ⟨_, Step.delete (by simpa using hx) (Or.inl rfl) m₁ sp .refl, ?_⟩
      simp [Tree.unit, LabelledTree.erase, Tree.depth, Tree.size]; omega
    | node a₀ b₀ =>
      obtain ⟨a, d, hm, hma⟩ := run_max (.node a₀ b₀) (by simp)
      have hd : delete t x = (.node a r, c + d) := by simp [delete, he, join, hm]
      rw [hd]
      have hsa : a.size + 1 = x := by
        have := hma.1.size_eq; simp only [Tree.size] at this hl; omega
      have m₂ : Moves (Tree.node (.node a₀ b₀) r).unit (Tree.node (.node a .nil) r).unit d 0 :=
        moves_of_rotations (rotations_unit (Rotations.inLeft hma.1))
      have m := m₁.append m₂
      by_cases hr : r = .nil
      · subst hr
        have sp : Splice (Tree.node (.node a .nil) .nil).unit x (Tree.node a .nil).unit := by
          have := Splice.noRight (l := (Tree.node a .nil).unit) (d := ())
          simp only [unit_erase, Tree.size] at this
          rwa [show a.size + 1 + 0 = x by omega] at this
        refine ⟨_, Step.delete (by simpa using hx) (Or.inl rfl) m sp .refl, ?_⟩
        simp only [unit_erase]
        rw [depth_root (by simp [Tree.size]; omega)]; omega
      · have sp : Splice (Tree.node (.node a .nil) r).unit (x - 1) (Tree.node a r).unit := by
          have := Splice.inLeft (d := ()) (r := r.unit)
            (Splice.noRight (l := a.unit) (d := ()))
          simp only [unit_erase] at this
          rwa [show a.size = x - 1 by omega] at this
        have two : (Tree.node (.node a .nil) r).TwoChildren x := by
          simp [Tree.TwoChildren, Tree.size, hr, show a.size + 1 = x from hsa]
        refine ⟨_, Step.delete (by simpa using hx) (Or.inr ⟨by simpa using two, Or.inl (by omega)⟩)
          m sp .refl, ?_⟩
        simp only [unit_erase]
        rw [depth_left (by simp [Tree.size]; omega), depth_root (by omega)]; omega

end RotationBST.Splay.Updates
