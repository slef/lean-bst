module

public import RotationBST.Models.Rotation.Rotations
public import RotationBST.Models.Online.Abstract

@[expose] public section

namespace RotationBST

/-- Recursively expose x in its child subtree, then rotate it one level up.
Out-of-range inputs have arbitrary behavior; correctness is required only in range. -/
def moveToRoot : Tree → Nat → Tree × Nat
  | .nil, _ => (.nil, 0)
  | .node l r, x =>
      if x < l.size then
        let (u, k) := moveToRoot l x
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node a (.node b r), k + 1)
      else if x = l.size then (.node l r, 0)
      else
        let (u, k) := moveToRoot r (x - l.size - 1)
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node (.node l a) b, k + 1)

theorem moveToRoot_correct (t : Tree) (x : Nat) (hx : x < t.size) :
    Access t (moveToRoot t x).1 x (moveToRoot t x).2 ∧ (moveToRoot t x).2 < t.size := by
  induction t generalizing x with
  | nil => simp only [Tree.size] at hx; omega
  | node l r il ir =>
      by_cases hl : x < l.size
      · obtain ⟨ha, hk⟩ := il x hl
        rcases he : moveToRoot l x with ⟨u, k⟩
        rw [he] at ha hk
        cases u with
        | nil => exact ha.2.elim
        | node a b =>
            have hrun : Rotations (.node l r) (.node a (.node b r)) (k + 1) :=
              ha.1.inLeft.append (.step .right .refl)
            simp only [moveToRoot, ite_eq_left hl, he]
            exact ⟨⟨hrun, ha.2⟩, by simp only [Tree.size]; omega⟩
      · by_cases heq : x = l.size
        · simp only [moveToRoot, ite_eq_right hl, ite_eq_left heq]
          exact ⟨⟨.refl, heq.symm⟩, by simp only [Tree.size]; omega⟩
        · have hr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
          obtain ⟨ha, hk⟩ := ir (x - l.size - 1) hr
          rcases he : moveToRoot r (x - l.size - 1) with ⟨u, k⟩
          rw [he] at ha hk
          cases u with
          | nil => exact ha.2.elim
          | node a b =>
              have hrun : Rotations (.node l r) (.node (.node l a) b) (k + 1) :=
                ha.1.inRight.append (.step .left .refl)
              simp only [moveToRoot, ite_eq_right hl, ite_eq_right heq, he]
              refine ⟨⟨hrun, ?_⟩, ?_⟩
              · have hf : a.size = x - l.size - 1 := ha.2
                simp only [Tree.size]
                omega
              · simp only [Tree.size]; omega

/-- A baseline algorithm, not splaying: single rotations move the request upward. -/
def moveToRootAlgorithm : Algorithm where
  step _ t x := moveToRoot t x
  correct _ t x hx := (moveToRoot_correct t x hx).1

end RotationBST
