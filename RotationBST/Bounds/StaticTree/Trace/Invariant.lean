module

public import RotationBST.Bounds.StaticTree.Trace.Depth
public import RotationBST.Models.Pointer.Invariant.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.StaticTree.Trace
open _root_.RotationBST.Tree (depth)

/-- A bounded physical trace supplies an invariant at every step, allowing
short local repairs to compose with structurally bounded recursive repairs. -/
theorem within_size_depth {a b : Pointer.Config} {cost : Nat} (trace : Pointer.Trace a b cost) :
    Pointer.TraceWithin (fun t => t.size = a.tree.size ∧ ∀ x, depth t x ≤ depth a.tree x + cost) a b cost := by
  induction trace with
  | refl => exact .refl ⟨rfl, by intro x; omega⟩
  | @step a b c cost step rest ih =>
    refine .step ⟨rfl, by intro x; omega⟩ step (ih.weaken ?_)
    intro t bound
    obtain ⟨_, _, rotation⟩ := step.rotations
    refine ⟨bound.1.trans rotation.size_eq.symm, ?_⟩
    intro x
    have first := trace_depth (Pointer.Trace.step step .refl) x
    have later := bound.2 x
    omega

/-- A size-preserving pointwise bound lifts through untouched enclosing nodes. -/
theorem plug_bound (cs : List Pointer.Frame) {s t : Tree} {factor constant : Nat}
    (factorPositive : 1 ≤ factor) (size : t.size = s.size)
    (bound : ∀ x, depth t x ≤ factor * depth s x + constant) :
    ∀ x, depth (Pointer.plug cs t) x ≤ factor * depth (Pointer.plug cs s) x + constant := by
  induction cs generalizing s t with
  | nil => exact bound
  | cons frame cs ih =>
    cases frame with
    | left b =>
      apply ih (by simp only [Tree.size, size])
      intro x
      have localBound := bound x
      simp only [depth, size]
      split_ifs <;> nlinarith
    | right a =>
      apply ih (by simp only [Tree.size, size])
      intro x
      have localBound := bound (x - a.size - 1)
      simp only [depth]
      split_ifs <;> nlinarith

/-- Embed a certified root-to-root repair, charging descent and ascent and
preserving its depth constants in the entire surrounding tree. -/
theorem within_embed {s t : Tree} {cost factor constant : Nat} (cs : List Pointer.Frame)
    (factorPositive : 1 ≤ factor)
    (h : Pointer.TraceWithin (fun u => u.size = s.size ∧
      ∀ x, depth u x ≤ factor * depth s x + constant) ⟨s, []⟩ ⟨t, []⟩ cost)
    (liveS : s ≠ .nil) (liveT : t ≠ .nil) :
    Pointer.TraceWithin (fun u => u.size = (Pointer.plug cs s).size ∧
      ∀ x, depth u x ≤ factor * depth (Pointer.plug cs s) x + constant)
      ⟨Pointer.plug cs s, []⟩ ⟨Pointer.plug cs t, []⟩ (cs.length + cost + cs.length) := by
  apply Pointer.TraceWithin.inContext cs _ liveS liveT
  apply h.weaken
  intro u bound
  exact ⟨Pointer.plug_size_congr cs bound.1, plug_bound cs factorPositive bound.1 bound.2⟩

/-- Compose structural prefix certificates without charging the length of the
first trace to the depth bound of the second. -/
theorem within_append {a b c : Pointer.Config} {firstCost lastCost f g u v : Nat}
    (positive : 1 ≤ g)
    (first : Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ f * depth a.tree x + u) a b firstCost)
    (last : Pointer.TraceWithin (fun t => t.size = b.tree.size ∧
      ∀ x, depth t x ≤ g * depth b.tree x + v) b c lastCost) :
    Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ (g * f) * depth a.tree x + (g * u + v)) a c (firstCost + lastCost) := by
  apply Pointer.TraceWithin.append (b := b)
  · apply first.weaken
    intro t bound
    refine ⟨bound.1, ?_⟩
    intro x
    have grow := Nat.mul_le_mul_right (f * depth a.tree x + u) positive
    have initial := bound.2 x
    nlinarith
  · apply last.weaken
    intro t bound
    refine ⟨bound.1.trans first.finish.1, ?_⟩
    intro x
    have intermediate := Nat.mul_le_mul_left g (first.finish.2 x)
    have final := bound.2 x
    nlinarith

end RotationBST.StaticTree.Trace
