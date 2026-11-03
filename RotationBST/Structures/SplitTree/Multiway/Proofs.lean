module

public import RotationBST.Structures.SplitTree.Multiway.Defs
public import RotationBST.Models.Rotation.Rotations
import Mathlib.Data.Nat.Basic

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway

@[simp] theorem binary_size (t : Multiway) : t.binary.size = t.size := by
  induction t <;> simp_all only [binary, size, Tree.size] <;> omega

/-- Every balanced height-`h` tree contains between `2^h - 1` and `4^h - 1` keys. -/
theorem size_bounds {h : Nat} {t : Multiway} (balanced : Balanced h t) :
    2 ^ h ≤ t.size + 1 ∧ t.size + 1 ≤ 4 ^ h := by
  induction balanced with
  | nil => decide
  | two ha hb ia ib => simp only [size, Nat.pow_succ]; constructor <;> omega
  | three ha hb hc ia ib ic => simp only [size, Nat.pow_succ]; constructor <;> omega
  | four ha hb hc hd ia ib ic id => simp only [size, Nat.pow_succ]; constructor <;> omega

/-- Sibling repair is implemented by at most three actual binary rotations. -/
theorem prepareLeft_rotations (t : Multiway) :
    Rotations t.binary (t.prepareLeft).1.binary (t.prepareLeft).2 := by
  cases t with
  | nil => exact .refl
  | three a b c => exact .refl
  | four a b c d => exact .refl
  | two left right =>
    cases left with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases right with
      | nil => exact .refl
      | two c d => exact .refl
      | three c d e => exact .step .left (.step (.inLeft .right) .refl)
      | four c d e f => exact .step (.inRight .right) (.step .left (.step (.inLeft .right) .refl))

/-- Right sibling repair also has a constant binary rotation cost. -/
theorem prepareRight_rotations (t : Multiway) :
    Rotations t.binary (t.prepareRight).1.binary (t.prepareRight).2 := by
  cases t with
  | nil => exact .refl
  | three a b c => exact .refl
  | four a b c d => exact .refl
  | two left right =>
    cases right with
    | nil => cases left <;> exact .refl
    | three a b c => cases left <;> exact .refl
    | four a b c d => cases left <;> exact .refl
    | two c d =>
      cases left with
      | nil => exact .refl
      | two a b => exact .refl
      | three a b c => exact .step (.inLeft .left) (.step .right .refl)
      | four a b c d => exact .step .right (.step (.inRight .right) (.step .left (.step (.inLeft .right) .refl)))


/-- Borrowing preserves height; merging at the root reduces it by exactly one. -/
theorem Balanced.prepareLeft {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Balanced h (t.prepareLeft).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.prepareLeft).1 := by
  cases valid with
  | nil => exact Or.inl .nil
  | three ha hb hc => exact Or.inl (.three ha hb hc)
  | four ha hb hc hd => exact Or.inl (.four ha hb hc hd)
  | two hl hr =>
    cases hl with
    | nil => cases hr; exact Or.inl (.two .nil .nil)
    | three ha hb hc => exact Or.inl (.two (.three ha hb hc) hr)
    | four ha hb hc hd => exact Or.inl (.two (.four ha hb hc hd) hr)
    | two ha hb =>
      cases hr with
      | two hc hd => exact Or.inr ⟨_, rfl, .four ha hb hc hd⟩
      | three hc hd he => exact Or.inl (.two (.three ha hb hc) (.two hd he))
      | four hc hd he hf => exact Or.inl (.two (.three ha hb hc) (.three hd he hf))

theorem Balanced.prepareRight {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Balanced h (t.prepareRight).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.prepareRight).1 := by
  cases valid with
  | nil => exact Or.inl .nil
  | three ha hb hc => exact Or.inl (.three ha hb hc)
  | four ha hb hc hd => exact Or.inl (.four ha hb hc hd)
  | two hl hr =>
    cases hl with
    | nil => cases hr; exact Or.inl (.two .nil .nil)
    | two ha hb =>
      cases hr with
      | two hc hd => exact Or.inr ⟨_, rfl, .four ha hb hc hd⟩
      | three hc hd he => exact Or.inl (.two (.two ha hb) (.three hc hd he))
      | four hc hd he hf => exact Or.inl (.two (.two ha hb) (.four hc hd he hf))
    | three ha hb hc =>
      cases hr with
      | two hd he => exact Or.inl (.two (.two ha hb) (.three hc hd he))
      | three hd he hf => exact Or.inl (.two (.three ha hb hc) (.three hd he hf))
      | four hd he hf hg => exact Or.inl (.two (.three ha hb hc) (.four hd he hf hg))
    | four ha hb hc hd =>
      cases hr with
      | two he hf => exact Or.inl (.two (.three ha hb hc) (.three hd he hf))
      | three he hf hg => exact Or.inl (.two (.four ha hb hc hd) (.three he hf hg))
      | four he hf hg hh => exact Or.inl (.two (.four ha hb hc hd) (.four he hf hg hh))

/-- There are no more multiway nodes than keys to pay for their merges. -/
theorem nodes_le_size (t : Multiway) : t.nodes ≤ t.size := by
  induction t <;> simp_all only [nodes, size] <;> omega

theorem prepareLeft_cost (t : Multiway) : (t.prepareLeft).2 ≤ 3 := by
  cases t with
  | nil => simp [prepareLeft]
  | three a b c => simp [prepareLeft]
  | four a b c d => simp [prepareLeft]
  | two left right => cases left <;> cases right <;> simp [prepareLeft]

theorem prepareRight_cost (t : Multiway) : (t.prepareRight).2 ≤ 4 := by
  cases t with
  | nil => simp [prepareRight]
  | three a b c => simp [prepareRight]
  | four a b c d => simp [prepareRight]
  | two left right => cases left <;> cases right <;> simp [prepareRight]

/-- Borrowing never creates multiway nodes; a root merge removes two. -/
theorem prepareLeft_nodes (t : Multiway) : (t.prepareLeft).1.nodes ≤ t.nodes := by
  cases t with
  | nil => exact Nat.le_refl _
  | three a b c => exact Nat.le_refl _
  | four a b c d => exact Nat.le_refl _
  | two left right => cases left <;> cases right <;> simp only [prepareLeft, nodes] <;> omega

theorem prepareRight_nodes (t : Multiway) : (t.prepareRight).1.nodes ≤ t.nodes := by
  cases t with
  | nil => exact Nat.le_refl _
  | three a b c => exact Nat.le_refl _
  | four a b c d => exact Nat.le_refl _
  | two left right => cases left <;> cases right <;> simp only [prepareRight, nodes] <;> omega

/-- Root merging removes the parent and combines its children, consuming two nodes. -/
theorem merge_nodes (a b c d : Multiway) :
    (.four a b c d : Multiway).nodes + 2 = (.two (.two a b) (.two c d) : Multiway).nodes := by
  simp only [nodes]
  omega

end RotationBST.Arboral.Split.Multiway
