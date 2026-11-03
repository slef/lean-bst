module

public import RotationBST.Algorithms.Splay.Potential

@[expose] public section

namespace RotationBST.Splay

variable {s t : Tree}
open Pointer

theorem mass_plug (w : Nat → ℝ) (hs : s.size = t.size)
    (hm : ∀ lo, mass w s lo = mass w t lo) (cs : List Frame) (lo : Nat) :
    mass w (plug cs s) lo = mass w (plug cs t) lo := by
  induction cs generalizing s t with
  | nil => exact hm lo
  | cons c cs ih =>
      cases c with
      | left b =>
          apply ih (by simp only [Tree.size, hs])
          intro i
          simp only [mass, hm, hs]
      | right a =>
          apply ih (by simp only [Tree.size, hs])
          intro i
          simp only [mass, hm]

/-- A local rotation leaves the potential of every strict ancestor unchanged. -/
theorem potential_plug_diff (w : Nat → ℝ) (hs : s.size = t.size)
    (hm : ∀ lo, mass w s lo = mass w t lo) (cs : List Frame) (lo : Nat) :
    potential w (plug cs t) lo - potential w (plug cs s) lo =
      potential w t (lo + offset cs) - potential w s (lo + offset cs) := by
  induction cs generalizing s t with
  | nil => simp [plug, offset]
  | cons c cs ih =>
      cases c with
      | left b =>
          have hn : ∀ i, mass w (.node s b) i = mass w (.node t b) i := by
            intro i; simp only [mass, hm, hs]
          have h := ih (s := .node s b) (t := .node t b)
            (by simp only [Tree.size, hs]) hn
          simp only [plug, offset]
          rw [h]
          simp only [potential, hn, hs]
          ring
      | right a =>
          have hn : ∀ i, mass w (.node a s) i = mass w (.node a t) i := by
            intro i; simp only [mass, hm]
          have h := ih (s := .node a s) (t := .node a t)
            (by simp only [Tree.size, hs]) hn
          simp only [plug, offset]
          rw [h]
          simp only [potential, hn, Nat.add_assoc]
          ring

/-- Combine one double splay step with the inductive amortized bound above it. -/
theorem compose_access (w : Nat → ℝ) (before after result : Tree) (cs : List Frame)
    (lo : Nat) (xmass : ℝ) (hr : Rotations before after 2)
    (localBound : 2 + potential w after (lo + offset cs) - potential w before (lo + offset cs) ≤
      3 * (Real.logb 2 (mass w before (lo + offset cs)) - Real.logb 2 xmass))
    (restBound : (cs.length : ℝ) + potential w result lo - potential w (plug cs after) lo ≤
      3 * (Real.logb 2 (mass w (plug cs after) lo) -
        Real.logb 2 (mass w after (lo + offset cs))) + 1) :
    (cs.length : ℝ) + 2 + potential w result lo - potential w (plug cs before) lo ≤
      3 * (Real.logb 2 (mass w (plug cs before) lo) - Real.logb 2 xmass) + 1 := by
  have hm := mass_rotations w hr
  have hp := potential_plug_diff w hr.size_eq hm cs lo
  have hg := mass_plug w hr.size_eq hm cs lo
  rw [hm] at localBound
  rw [hg]
  linarith

end RotationBST.Splay
