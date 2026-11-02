module

public import RotationBST.Pointer.Lazy.Rotations.Abstract

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {x y u v : α} {s t z : LabelledTree α}

theorem RotateAt.forget (h : RotateAt x y s t) : LabelledTree.Rotate s t := by
  induction h with
  | right => exact .right
  | left => exact .left
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

theorem endpoints (h : LabelledTree.Rotate s t) : ∃ x y, RotateAt x y s t := by
  induction h with
  | right => exact ⟨_, _, .right⟩
  | left => exact ⟨_, _, .left⟩
  | inLeft _ ih => obtain ⟨x, y, h⟩ := ih; exact ⟨x, y, .inLeft h⟩
  | inRight _ ih => obtain ⟨x, y, h⟩ := ih; exact ⟨x, y, .inRight h⟩

/-- Rotations with disjoint endpoint keys commute, even when one lies inside a
subtree of the other. The lazy simulation uses this exchange to postpone independent components. -/
theorem commute (h : RotateAt x y s t) (g : RotateAt u v t z)
    (disjoint : DisjointPairs x y u v) :
    ∃ q, RotateAt u v s q ∧ RotateAt x y q z := by
  induction h generalizing z with
  | right =>
      cases g with
      | right => simp_all [DisjointPairs]
      | left => simp_all [DisjointPairs]
      | inLeft g => exact ⟨_, .inLeft (.inLeft g), .right⟩
      | inRight g =>
          cases g with
          | right => simp_all [DisjointPairs]
          | left => simp_all [DisjointPairs]
          | inLeft g => exact ⟨_, .inLeft (.inRight g), .right⟩
          | inRight g => exact ⟨_, .inRight g, .right⟩
  | left =>
      cases g with
      | right => simp_all [DisjointPairs]
      | left => simp_all [DisjointPairs]
      | inLeft g =>
          cases g with
          | right => simp_all [DisjointPairs]
          | left => simp_all [DisjointPairs]
          | inLeft g => exact ⟨_, .inLeft g, .left⟩
          | inRight g => exact ⟨_, .inRight (.inLeft g), .left⟩
      | inRight g => exact ⟨_, .inRight (.inRight g), .left⟩
  | inLeft h ih =>
      cases g with
      | right =>
          cases h with
          | right => simp_all [DisjointPairs]
          | left => simp_all [DisjointPairs]
          | inLeft h => exact ⟨_, .right, .inLeft h⟩
          | inRight h => exact ⟨_, .right, .inRight (.inLeft h)⟩
      | left => exact ⟨_, .left, .inLeft (.inLeft h)⟩
      | inLeft g =>
          obtain ⟨q, hg, hh⟩ := ih g disjoint
          exact ⟨_, .inLeft hg, .inLeft hh⟩
      | inRight g => exact ⟨_, .inRight g, .inLeft h⟩
  | inRight h ih =>
      cases g with
      | right => exact ⟨_, .right, .inRight (.inRight h)⟩
      | left =>
          cases h with
          | right => simp_all [DisjointPairs]
          | left => simp_all [DisjointPairs]
          | inLeft h => exact ⟨_, .left, .inLeft (.inRight h)⟩
          | inRight h => exact ⟨_, .left, .inRight h⟩
      | inLeft g => exact ⟨_, .inLeft g, .inRight h⟩
      | inRight g =>
          obtain ⟨q, hg, hh⟩ := ih g disjoint
          exact ⟨_, .inRight hg, .inRight hh⟩

end RotationBST.Pointer.Lazy
