module

public import RotationBST.Models.Dictionary.Definitions.Abstract
public import RotationBST.Models.Rotation.Rotations
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

/-! ### Depth under rotations -/

theorem depth_left {l r : Tree} {x : Nat} (h : x < l.size) :
    (Tree.node l r).depth x = l.depth x + 1 := by
  simp [Tree.depth, h]

theorem depth_root {l r : Tree} {x : Nat} (h : x = l.size) : (Tree.node l r).depth x = 0 := by
  subst h; simp [Tree.depth]

theorem depth_right {l r : Tree} {x : Nat} (h : l.size < x) :
    (Tree.node l r).depth x = r.depth (x - l.size - 1) + 1 := by
  simp [Tree.depth, show ¬ x < l.size by omega, show x ≠ l.size by omega]

theorem depth_le_rotate {s t : Tree} (h : Rotate s t) (x : Nat) : s.depth x ≤ t.depth x + 1 := by
  induction h generalizing x with
  | right =>
      rename_i a b c
      have hab : (Tree.node a b).size = a.size + 1 + b.size := rfl
      by_cases h1 : x < a.size
      · rw [depth_left (l := .node a b) (r := c) (by rw [hab]; omega), depth_left (l := a) (r := b) h1,
          depth_left (l := a) (r := .node b c) h1]
      by_cases h2 : x = a.size
      · rw [depth_left (l := .node a b) (r := c) (by rw [hab]; omega), depth_root (l := a) (r := b) h2,
          depth_root (l := a) (r := .node b c) h2]
      by_cases h3 : x < a.size + 1 + b.size
      · rw [depth_left (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_right (l := a) (r := b) (by omega), depth_right (l := a) (r := .node b c) (by omega),
          depth_left (l := b) (r := c) (by omega)]; try omega
      by_cases h4 : x = a.size + 1 + b.size
      · rw [depth_root (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_right (l := a) (r := .node b c) (by omega), depth_root (l := b) (r := c) (by omega)]
        try omega
      · rw [depth_right (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_right (l := a) (r := .node b c) (by omega), depth_right (l := b) (r := c) (by omega), hab,
          show x - (a.size + 1 + b.size) - 1 = x - a.size - 1 - b.size - 1 by omega]; try omega
  | left =>
      rename_i a b c
      have hab : (Tree.node a b).size = a.size + 1 + b.size := rfl
      by_cases h1 : x < a.size
      · rw [depth_left (l := a) (r := .node b c) h1, depth_left (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_left (l := a) (r := b) h1]; try omega
      by_cases h2 : x = a.size
      · rw [depth_root (l := a) (r := .node b c) h2, depth_left (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_root (l := a) (r := b) h2]; try omega
      by_cases h3 : x < a.size + 1 + b.size
      · rw [depth_right (l := a) (r := .node b c) (by omega), depth_left (l := b) (r := c) (by omega),
          depth_left (l := .node a b) (r := c) (by rw [hab]; omega),
          depth_right (l := a) (r := b) (by omega)]; try omega
      by_cases h4 : x = a.size + 1 + b.size
      · rw [depth_right (l := a) (r := .node b c) (by omega), depth_root (l := b) (r := c) (by omega),
          depth_root (l := .node a b) (r := c) (by rw [hab]; omega)]
      · rw [depth_right (l := a) (r := .node b c) (by omega), depth_right (l := b) (r := c) (by omega),
          depth_right (l := .node a b) (r := c) (by rw [hab]; omega), hab,
          show x - a.size - 1 - b.size - 1 = x - (a.size + 1 + b.size) - 1 by omega]
  | inLeft h ih =>
      rename_i a b c
      have hs := h.size_eq
      by_cases h1 : x < a.size
      · rw [depth_left (l := a) (r := c) h1, depth_left (l := b) (r := c) (by omega)]; have := ih x; omega
      by_cases h2 : x = a.size
      · rw [depth_root (l := a) (r := c) h2, depth_root (l := b) (r := c) (by omega)]; try omega
      · rw [depth_right (l := a) (r := c) (by omega), depth_right (l := b) (r := c) (by omega), hs]
        try omega
  | inRight h ih =>
      rename_i a b c
      by_cases h1 : x < c.size
      · rw [depth_left (l := c) (r := a) h1, depth_left (l := c) (r := b) h1]; try omega
      by_cases h2 : x = c.size
      · rw [depth_root (l := c) (r := a) h2, depth_root (l := c) (r := b) h2]; try omega
      · rw [depth_right (l := c) (r := a) (by omega), depth_right (l := c) (r := b) (by omega)]
        have := ih (x - c.size - 1); omega

theorem depth_le_rotations {s t : Tree} {k : Nat} (h : Rotations s t k) (x : Nat) :
    s.depth x ≤ t.depth x + k := by
  induction h with
  | refl => omega
  | step h _ ih => have := depth_le_rotate h x; omega

/-- An access by `k` rotations brings a node at depth at most `k` to the root. -/
theorem access_depth_le {s t : Tree} {x k : Nat} (h : Access s t x k) : s.depth x ≤ k := by
  obtain ⟨hr, hroot⟩ := h
  have := depth_le_rotations hr x
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
