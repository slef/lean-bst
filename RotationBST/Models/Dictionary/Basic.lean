module

public import RotationBST.Models.Dictionary.Definitions.Abstract
public import RotationBST.Models.Rotation.Rotations
public import RotationBST.Models.Rotation.Shapes
public import RotationBST.Models.Labelled.ArbitraryKeys
import Mathlib.Tactic

@[expose] public section

/-! Sizes, erasure of node data, and depth under rotations. -/
namespace RotationBST.Dictionary
open Representation.Bridge

variable {α : Type}

/-! ### Trees without data -/

@[simp] theorem unit_erase (t : Tree) : t.unit.erase = t := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [Tree.unit, LabelledTree.erase, il, ir]

@[simp] theorem erase_unit (t : LabelledTree Unit) : t.erase.unit = t := by
  induction t with
  | nil => rfl
  | node l x r il ir => simp [Tree.unit, LabelledTree.erase, il, ir]

/-! ### Inserting a leaf -/

theorem insertAt_size (t : Tree) (g : Nat) : (t.insertAt g).size = t.size + 1 := by
  induction t generalizing g with
  | nil => simp [Tree.insertAt, Tree.size]
  | node l r il ir =>
    simp only [Tree.insertAt]; split
    · simp only [Tree.size, il]; omega
    · simp only [Tree.size, ir]; omega

theorem erase_insertAt (t : LabelledTree α) (g : Nat) (a : α) :
    (t.insertAt g a).erase = t.erase.insertAt g := by
  induction t generalizing g with
  | nil => rfl
  | node l x r il ir =>
    simp only [LabelledTree.insertAt, LabelledTree.erase, Tree.insertAt]; split
    · simp [LabelledTree.erase, il]
    · simp [LabelledTree.erase, ir]

theorem insertAt_erase_size (t : LabelledTree α) (g : Nat) (a : α) :
    (t.insertAt g a).erase.size = t.erase.size + 1 := by
  rw [erase_insertAt, insertAt_size]

theorem unit_insertAt (t : Tree) (g : Nat) : (t.insertAt g).unit = t.unit.insertAt g () := by
  induction t generalizing g with
  | nil => rfl
  | node l r il ir =>
    simp only [Tree.insertAt, Tree.unit, LabelledTree.insertAt, unit_erase]; split
    · simp [Tree.unit, il]
    · simp [Tree.unit, ir]

/-- Inserting a leaf at gap `g` is the reverse of splicing out rank `g`. -/
theorem insertAt_splice (t : LabelledTree α) (g : Nat) (a : α) (hg : g ≤ t.erase.size) :
    Splice (t.insertAt g a) g t := by
  induction t generalizing g with
  | nil =>
    have : g = 0 := by simp [LabelledTree.erase, Tree.size] at hg; omega
    subst this; exact .noLeft
  | node l x r il ir =>
    simp only [LabelledTree.insertAt]; split
    · exact .inLeft (il g (by assumption))
    · rename_i h
      have := Splice.inRight (l := l) (d := x)
        (ir (g - l.erase.size - 1) (by simp [LabelledTree.erase, Tree.size] at hg; omega))
      rwa [show l.erase.size + 1 + (g - l.erase.size - 1) = g by omega] at this

theorem unit_insertAt_splice (t : Tree) (g : Nat) (hg : g ≤ t.size) :
    Splice (t.insertAt g).unit g t.unit := by
  rw [unit_insertAt]; exact insertAt_splice _ g () (by simpa using hg)

theorem rotations_unit {a b : Tree} {k : Nat} (h : Rotations a b k) :
    LabelledTree.Rotations a.unit b.unit k := by
  obtain ⟨t, ht, he⟩ := lift_rotations h a.unit (unit_erase a)
  rwa [show t = b.unit by rw [← he, erase_unit]] at ht

theorem moves_of_rotations {s t : LabelledTree α} {k : Nat} (h : LabelledTree.Rotations s t k) :
    Moves s t k 0 := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .rotate h ih

/-! ### Deciding two children -/

/-- `Tree.TwoChildren` as a Boolean. -/
def twoChildren : Tree → Nat → Bool
  | .nil, _ => false
  | .node l r, x =>
      if x < l.size then twoChildren l x
      else if x = l.size then l != .nil && r != .nil
      else twoChildren r (x - l.size - 1)

theorem twoChildren_iff (t : Tree) (x : Nat) : twoChildren t x = true ↔ t.TwoChildren x := by
  induction t generalizing x with
  | nil => simp [twoChildren, Tree.TwoChildren]
  | node l r il ir =>
      simp only [twoChildren, Tree.TwoChildren]
      split
      · exact il x
      · split
        · simp
        · exact ir _

instance (t : Tree) (x : Nat) : Decidable (t.TwoChildren x) :=
  decidable_of_iff _ (twoChildren_iff t x)

/-! ### Moves -/

theorem Edit.erase {s t : LabelledTree α} (h : Edit s t) : s.erase = t.erase := by
  induction h with
  | here => rfl
  | inLeft _ ih => simp [LabelledTree.erase, ih]
  | inRight _ ih => simp [LabelledTree.erase, ih]

theorem Moves.erase {s t : LabelledTree α} {a e : Nat} (h : Moves s t a e) :
    Rotations s.erase t.erase a := by
  induction h with
  | refl => exact .refl
  | rotate h _ ih => exact .step (erase_rotate h) ih
  | edit h _ ih => rwa [h.erase]

theorem Moves.size {s t : LabelledTree α} {a e : Nat} (h : Moves s t a e) :
    s.erase.size = t.erase.size :=
  h.erase.size_eq

theorem Moves.append {s t u : LabelledTree α} {a e a' e' : Nat} (h : Moves s t a e)
    (g : Moves t u a' e') : Moves s u (a + a') (e + e') := by
  induction h with
  | refl => simpa using g
  | rotate h _ ih => simpa [Nat.add_right_comm] using Moves.rotate h (ih g)
  | edit h _ ih => simpa [Nat.add_right_comm] using Moves.edit h (ih g)

theorem Moves.inLeft {a b : LabelledTree α} {x y : Nat} (h : Moves a b x y) (d : α) (c : LabelledTree α) :
    Moves (.node a d c) (.node b d c) x y := by
  induction h with
  | refl => exact .refl
  | rotate h _ ih => exact .rotate (.inLeft h) ih
  | edit h _ ih => exact .edit (.inLeft h) ih

theorem Moves.inRight {a b : LabelledTree α} {x y : Nat} (h : Moves a b x y) (c : LabelledTree α) (d : α) :
    Moves (.node c d a) (.node c d b) x y := by
  induction h with
  | refl => exact .refl
  | rotate h _ ih => exact .rotate (.inRight h) ih
  | edit h _ ih => exact .edit (.inRight h) ih

theorem Moves.unit {s t : LabelledTree α} {a e : Nat} (h : Moves s t a e) :
    Moves s.erase.unit t.erase.unit a 0 :=
  moves_of_rotations (rotations_unit h.erase)

/-! ### Splices -/

theorem Splice.size {t u : LabelledTree α} {x : Nat} (h : Splice t x u) :
    t.erase.size = u.erase.size + 1 ∧ x < t.erase.size := by
  induction h with
  | noLeft => simp [LabelledTree.erase, Tree.size]; omega
  | noRight => simp [LabelledTree.erase, Tree.size]
  | inLeft _ ih => simp only [LabelledTree.erase, Tree.size]; omega
  | inRight _ ih => simp only [LabelledTree.erase, Tree.size]; omega

theorem Splice.unit {t u : LabelledTree α} {x : Nat} (h : Splice t x u) :
    Splice t.erase.unit x u.erase.unit := by
  induction h with
  | noLeft => exact .noLeft
  | noRight =>
      rename_i l _
      have := @Splice.noRight Unit l.erase.unit ()
      simpa [LabelledTree.erase, Tree.unit] using this
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih =>
      rename_i l _ _ _ _ _
      have := Splice.inRight (l := l.erase.unit) (d := ()) ih
      simpa [LabelledTree.erase, Tree.unit] using this

/-! ### Steps and executions -/

theorem Step.size {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    t.erase.size = op.resize s.erase.size := by
  cases h with
  | access _ m => exact m.size.symm
  | insert _ m₁ sp m₂ =>
      have := sp.size; have := m₁.size; have := m₂.size
      simp only [Op.resize]; omega
  | delete _ _ m₁ sp m₂ =>
      have := sp.size; have := m₁.size; have := m₂.size
      simp only [Op.resize]; omega

theorem Step.valid {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    op.Valid s.erase.size := by
  cases h with
  | access v _ => exact v
  | insert v _ _ _ => exact v
  | delete v _ _ _ _ => exact v

/-- Node data do not affect the main cost. -/
theorem Step.unit {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    Step s.erase.unit op t.erase.unit c 0 := by
  cases h with
  | access v m =>
      have := Step.access (s := s.erase.unit) (by simpa using v) m.unit
      simpa using this
  | insert v m₁ sp m₂ =>
      have := Step.insert (s := s.erase.unit) (by simpa using v) m₁.unit sp.unit m₂.unit
      simpa using this
  | delete v tg m₁ sp m₂ =>
      have := Step.delete (s := s.erase.unit) (by simpa using v) (by simpa using tg)
        m₁.unit sp.unit m₂.unit
      simpa using this

theorem Execution.unit {s t : LabelledTree α} {ops : List Op} {c e : Nat}
    (h : Execution s ops t c e) : Execution s.erase.unit ops t.erase.unit c 0 := by
  induction h with
  | nil => exact .nil
  | cons st _ ih => simpa using Execution.cons st.unit ih

theorem Execution.validSeq {s t : LabelledTree α} {ops : List Op} {c e : Nat}
    (h : Execution s ops t c e) : Op.ValidSeq s.erase.size ops := by
  induction h with
  | nil => trivial
  | cons st _ ih => exact ⟨st.valid, by rw [← st.size]; exact ih⟩

theorem Algorithm.runFrom_execution (A : Algorithm α) (past : List Op) (t : LabelledTree α)
    (ops : List Op) (valid : Op.ValidSeq t.erase.size ops) :
    Execution t ops (A.runFrom past t ops).1 (A.runFrom past t ops).2.1
      (A.runFrom past t ops).2.2 := by
  induction ops generalizing past t with
  | nil => exact .nil
  | cons op ops ih =>
      have hs := A.correct past t op valid.1
      exact .cons hs (ih (past ++ [op]) _ (by rw [hs.size]; exact valid.2))

/-- An access by `k` rotations brings a node at depth at most `k` to the root. -/
theorem access_depth_le {s t : Tree} {x k : Nat} (h : Access s t x k) : s.depth x ≤ k := by
  obtain ⟨hr, hroot⟩ := h
  have := hr.depth_le_reverse x
  cases t with
  | nil => exact hroot.elim
  | node l r =>
      simp only at hroot
      simp only [Tree.depth, hroot, lt_irrefl, ↓reduceIte] at this
      omega

/-- A rotation-model execution is a dictionary execution of accesses whose
main cost is at most `m + 2R`. -/
theorem of_execution {s t : Tree} {xs : List Nat} {k : Nat} (h : RotationBST.Execution s xs t k) :
    ∃ c, Execution s.unit (xs.map .access) t.unit c 0 ∧ c ≤ xs.length + 2 * k := by
  induction h with
  | nil => exact ⟨0, .nil, by omega⟩
  | @cons s₀ t₀ x k₀ xs₀ u m acc _ ih =>
      obtain ⟨c, hc, hle⟩ := ih
      have hd := access_depth_le acc
      have st : Step s₀.unit (.access x) t₀.unit (s₀.depth x + 1 + k₀) 0 := by
        have := Step.access (s := s₀.unit) (x := x) (by simpa using acc.in_range)
          (moves_of_rotations (rotations_unit acc.1))
        simpa using this
      refine ⟨_, by simpa using Execution.cons st hc, ?_⟩
      simp only [List.length_cons]
      omega

/-- Searching without moving costs the static search cost `∑ (1 + depth x)`. -/
theorem static_execution (s : LabelledTree α) (xs : List Nat) (valid : ∀ x ∈ xs, x < s.erase.size) :
    Execution s (xs.map .access) s ((xs.map fun x => s.erase.depth x + 1).sum) 0 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      have st : Step s (.access x) s (s.erase.depth x + 1 + 0) 0 :=
        .access (valid x (by simp)) .refl
      simpa using Execution.cons st (ih fun y hy => valid y (by simp [hy]))

end RotationBST.Dictionary
