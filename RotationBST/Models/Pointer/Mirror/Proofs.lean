module

public import RotationBST.Models.Pointer.Mirror.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST

@[simp] theorem Tree.mirror_mirror (t : Tree) : t.mirror.mirror = t := by
  induction t <;> simp_all [Tree.mirror]

@[simp] theorem Tree.mirror_size (t : Tree) : t.mirror.size = t.size := by
  induction t <;> simp_all [Tree.mirror, Tree.size, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

namespace Pointer

@[simp] theorem Frame.mirror_mirror (f : Frame) : f.mirror.mirror = f := by
  cases f <;> simp [Frame.mirror]

@[simp] theorem Config.mirror_mirror (c : Config) : c.mirror.mirror = c := by
  cases c
  simp [Config.mirror, List.map_map, Function.comp_def]

theorem mirror_plug (cs : List Frame) (t : Tree) :
    (plug cs t).mirror = plug (cs.map Frame.mirror) t.mirror := by
  induction cs generalizing t with
  | nil => rfl
  | cons f cs ih => cases f <;> simp only [plug, ih, List.map_cons, Frame.mirror, Tree.mirror]

theorem Config.mirror_tree (c : Config) : c.mirror.tree = c.tree.mirror :=
  (mirror_plug c.context c.focus).symm

theorem Step.mirror {a b : Config} (step : Step a b) : Step a.mirror b.mirror := by
  cases step
  · exact .downRight
  · exact .downLeft
  · exact .upRight
  · exact .upLeft
  · exact .rotateRightChild
  · exact .rotateLeftChild

/-- Reflect every instruction, preserving the exact cost and the focused node. -/
theorem Trace.mirror {a b : Config} {k : Nat} (trace : Trace a b k) :
    Trace a.mirror b.mirror k := by
  induction trace with
  | refl => exact .refl
  | step first later ih => exact .step first.mirror ih

end Pointer
end RotationBST
