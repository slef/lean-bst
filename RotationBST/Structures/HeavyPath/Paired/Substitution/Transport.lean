module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open LabelledCursor

theorem buildWith_erase {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks) :
    Stacks.buildWith weight LabelledTree.erase cs p = Stacks.build weight cs p := by
  induction cs generalizing p with
  | nil => rfl
  | cons frame cs ih =>
    rw [Stacks.buildWith, Stacks.build, ih]
    cases frame <;> rfl

theorem pushWith_congr {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks)
    {first second : LabelledTree α → Tree}
    (same : first (framePayload frame) = second (framePayload frame)) :
    p.pushWith weight first frame = p.pushWith weight second frame := by
  cases frame <;> simp only [framePayload] at same <;> simp only [Stacks.pushWith, same]

theorem buildWith_congr {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks)
    {first second : LabelledTree α → Tree}
    (same : ∀ frame ∈ cs, first (framePayload frame) = second (framePayload frame)) :
    Stacks.buildWith weight first cs p = Stacks.buildWith weight second cs p := by
  induction cs generalizing p with
  | nil => rfl
  | cons frame cs ih =>
    rw [Stacks.buildWith, Stacks.buildWith,
      pushWith_congr weight frame p (same frame (by simp))]
    exact ih _ (by intro f hf; exact same f (by simp [hf]))

/-- Substitution changes no node count when each replacement has the original
payload's size. This concerns actual shapes, not their analysis masses. -/
theorem replaced_plug_size {α : Type} (payload : LabelledTree α → Tree) (cs : List (Frame α))
    (t : LabelledTree α) (focus : Tree) (focusSize : focus.size = t.erase.size)
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    (Pointer.plug (cs.map (replaceFrame payload)) focus).size = (plug cs t).erase.size := by
  induction cs generalizing t focus with
  | nil => exact focusSize
  | cons frame cs ih =>
    have head := same frame (by simp)
    have tail : ∀ f ∈ cs, (payload (framePayload f)).size = (framePayload f).erase.size := by
      intro f hf; exact same f (by simp [hf])
    cases frame with
    | left x r =>
      apply ih (.node t x r) (.node focus (payload r)) _ tail
      simp only [framePayload] at head
      simp only [Tree.size, LabelledTree.erase, focusSize, head]
    | right l x =>
      apply ih (.node l x t) (.node (payload l) focus) _ tail
      simp only [framePayload] at head
      simp only [Tree.size, LabelledTree.erase, focusSize, head]

theorem replaced_offset {α : Type} (payload : LabelledTree α → Tree) (cs : List (Frame α))
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    Pointer.offset (cs.map (replaceFrame payload)) = Pointer.offset (cs.map Frame.erase) := by
  induction cs with
  | nil => rfl
  | cons frame cs ih =>
    have head := same frame (by simp)
    have tail := ih (by intro f hf; exact same f (by simp [hf]))
    cases frame <;> simp only [framePayload] at head <;>
      simp only [List.map_cons, replaceFrame, Frame.erase, Pointer.offset, head, tail]

theorem buildWith_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) (p : Stacks) (t : LabelledTree α) (focusSize : p.tree.size = t.erase.size)
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    (Stacks.buildWith weight payload cs p).tree.size = (plug cs t).erase.size := by
  obtain ⟨_, _, rotations⟩ := (buildWith_trace weight payload cs p []).rotations
  have size := rotations.size_eq.symm
  simp only [Pointer.Config.tree, List.append_nil, Pointer.plug] at size
  exact size.trans (replaced_plug_size payload cs t p.tree focusSize same)

end RotationBST.HeavyPath.Paired
