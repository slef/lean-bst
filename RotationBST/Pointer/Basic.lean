module

public import RotationBST.Pointer.Model
public import RotationBST.Geometry.AbstractBridge

@[expose] public section

namespace RotationBST.Pointer

variable {s t : Tree} {a b : Config} {x k : Nat}

theorem Rotate.plug (h : Rotate s t) (cs : List Frame) : Rotate (plug cs s) (plug cs t) := by
  induction cs generalizing s t with
  | nil => exact h
  | cons c cs ih =>
      cases c with
      | left r => exact ih (.inLeft h)
      | right l => exact ih (.inRight h)

theorem Rotations.plug (h : Rotations s t k) (cs : List Frame) :
    Rotations (plug cs s) (plug cs t) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (Rotate.plug h cs) ih

theorem Step.rotations (h : Step a b) :
    ∃ k, k ≤ 1 ∧ Rotations a.tree b.tree k := by
  cases h with
  | downLeft => exact ⟨0, by omega, .refl⟩
  | downRight => exact ⟨0, by omega, .refl⟩
  | upLeft => exact ⟨0, by omega, .refl⟩
  | upRight => exact ⟨0, by omega, .refl⟩
  | rotateLeftChild => exact ⟨1, by omega, .step (Rotate.plug .right _) .refl⟩
  | rotateRightChild => exact ⟨1, by omega, .step (Rotate.plug .left _) .refl⟩

theorem Step.depth_le (h : Step a b) : b.context.length ≤ a.context.length + 1 := by
  cases h <;> simp <;> omega

theorem Trace.rotations (h : Trace a b k) :
    ∃ j, j ≤ k ∧ Rotations a.tree b.tree j := by
  induction h with
  | refl => exact ⟨0, by omega, .refl⟩
  | step h _ ih =>
      obtain ⟨i, hi, hr⟩ := h.rotations
      obtain ⟨j, hj, hs⟩ := ih
      exact ⟨i + j, by omega, hr.append hs⟩

theorem Trace.depth_le (h : Trace a b k) :
    b.context.length ≤ a.context.length + k := by
  induction h with
  | refl => omega
  | step h _ ih => have := h.depth_le; omega

/-- Bring the cursor to the root in exactly one rotation per ancestor. -/
theorem expose (cs : List Frame) (l r : Tree) :
    ∃ u, Access (plug cs (.node l r)) u (offset cs + l.size) cs.length := by
  induction cs generalizing l r with
  | nil => exact ⟨_, .refl, by simp [offset, plug]⟩
  | cons c cs ih =>
      cases c with
      | left b =>
          obtain ⟨u, hu⟩ := ih l (.node r b)
          refine ⟨u, .step (Rotate.plug .right cs) hu.1, ?_⟩
          exact hu.2
      | right a =>
          obtain ⟨u, hu⟩ := ih (.node a l) r
          refine ⟨u, .step (Rotate.plug .left cs) hu.1, ?_⟩
          simpa only [offset, Tree.size, Nat.add_assoc] using hu.2

/-- One conventional search can be split at a root access, with a trailing
rotation trace. Keeping that suffix explicit avoids a false endpoint claim. -/
theorem serves_split (h : Serves s t x k) :
    ∃ u p q, Access s u x p ∧ Rotations u t q ∧ 1 + p + q ≤ 3 * k := by
  obtain ⟨v, f, i, j, hv, hx, hf, ht, hk⟩ := h
  obtain ⟨a, ha, hra⟩ := hv.rotations
  obtain ⟨b, hb, hrb⟩ := hf.rotations
  have hd := hv.depth_le
  rcases v with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.key?] at hx
  | node l r =>
      obtain ⟨u, hu⟩ := expose cs l r
      have hx' : offset cs + l.size = x := Option.some.inj hx
      rw [hx'] at hu
      have hout : Rotations u t (cs.length + b) := by
        rw [← ht]
        exact hu.1.symm.append hrb
      refine ⟨u, a + cs.length, cs.length + b,
        ⟨hra.append hu.1, hu.2⟩, hout, ?_⟩
      simp only [List.length_nil, Nat.zero_add] at hd
      omega

end RotationBST.Pointer
