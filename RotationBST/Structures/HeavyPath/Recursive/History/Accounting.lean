module

public import RotationBST.Structures.HeavyPath.Recursive.History.Preservation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor

/-- The source context partitions nodes into its separators, off-path
payload occurrences, and the focused subtree. -/
theorem context_size (α : Type) (cs : List (Frame α)) (t : LabelledTree α) :
    (plug cs t).erase.size = t.erase.size + cs.length +
      (cs.map (fun f => (framePayload f).erase.size)).sum := by
  induction cs generalizing t with
  | nil => simp [plug]
  | cons f cs ih =>
    cases f <;> simp only [plug, ih, LabelledTree.erase, Tree.size, framePayload,
      List.length_cons, List.map_cons, List.sum_cons] <;> omega

theorem sum_credits_bound {α : Type} (cs : List (Frame α)) (credits : Frame α → Nat) (factor : Nat)
    (bounds : ∀ f ∈ cs, credits f ≤ factor * (framePayload f).erase.size) :
    (cs.map credits).sum ≤ factor * (cs.map (fun f => (framePayload f).erase.size)).sum := by
  induction cs with
  | nil => simp
  | cons f cs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (bounds f (by simp)) (ih (fun g hg => bounds g (by simp [hg])))

end RotationBST.HeavyPath.Recursive.History
