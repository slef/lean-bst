module

public import RotationBST.Structures.HeavyPath.Recursive.History.Entries
public import RotationBST.Structures.HeavyPath.Paired.Substitution.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Interruption.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor

private theorem lower_append {α : Type} (es ds : List (Entry α)) : lower (es ++ ds) = lower ds ++ lower es := by
  induction es with
  | nil => simp [lower]
  | cons e es ih => cases source : e.source <;> simp [lower, source, ih, List.append_assoc]

private theorem upper_append {α : Type} (es ds : List (Entry α)) : upper (es ++ ds) = upper es ++ upper ds := by
  induction es with
  | nil => simp [upper]
  | cons e es ih => cases source : e.source <;> simp [upper, source, ih]

/-- Attach a source separator with its own physical payload occurrence. -/
theorem push_path {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) (e : Entry α) (nonnegative : 0 ≤ frameMass weight e.source) :
    PathValid weight (es ++ [e]) (p.pushWith weight (fun _ => e.shape) e.source) ∧
      Pointer.Trace ⟨e.wrap p.tree, []⟩ ⟨(p.pushWith weight (fun _ => e.shape) e.source).tree, []⟩
        (p.pushCost e.source + 1) ∧
      p.pushCost e.source + 1 + (p.pushWith weight (fun _ => e.shape) e.source).potential ≤ 24 + p.potential := by
  have fringe := Paired.Substitution.Results.buildWith_fringe (weight := weight) (fun _ => e.shape) [e.source] valid.pair
    (by intro f hf; rcases List.mem_singleton.mp hf with rfl; exact nonnegative)
  change (p.pushWith weight (fun _ => e.shape) e.source).lower.decode.fringe = _ ∧
    (p.pushWith weight (fun _ => e.shape) e.source).upper.decode.mirror.fringe = _ at fringe
  have trace := (Pointer.moveDown (replaceFrame (fun _ => e.shape) e.source) []
    (by intro h; cases h)).append
      (Paired.Substitution.Results.pushWith_trace weight (fun _ => e.shape) e.source p [])
  have bound := Paired.Substitution.Results.pushWith_amortized (fun _ => e.shape) valid.pair nonnegative
  refine ⟨⟨Paired.Substitution.Results.pushWith_valid _ valid.pair nonnegative, ?_, ?_⟩, ?_, by omega⟩
  · rw [fringe.1, valid.lower, lower_append]
    cases source : e.source <;>
      simp [lowerSlotsWith, lower, source, Entry.slot, frameMass]
  · rw [fringe.2, valid.upper, upper_append]
    cases source : e.source <;>
      simp [upperSlotsWith, upper, source, Entry.slot, frameMass]
  · cases source : e.source <;>
      simpa only [Entry.wrap, source, replaceFrame, Pointer.plug, Nat.add_comm] using trace

theorem push_path_within {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) (e : Entry α) (nonnegative : 0 ≤ frameMass weight e.source) :
    PathValid weight (es ++ [e]) (p.pushWith weight (fun _ => e.shape) e.source) ∧
      Pointer.TraceWithin (fun t => t.size = (e.wrap p.tree).size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth (e.wrap p.tree) x + 16) ⟨e.wrap p.tree, []⟩ ⟨(p.pushWith weight (fun _ => e.shape) e.source).tree, []⟩
        (p.pushCost e.source + 1) ∧
      p.pushCost e.source + 1 + (p.pushWith weight (fun _ => e.shape) e.source).potential ≤ 24 + p.potential := by
  obtain ⟨preserved, _, bound⟩ := push_path valid e nonnegative
  refine ⟨preserved, ?_, bound⟩
  have trace := Paired.Interruption.Results.push_frame weight (fun _ => e.shape) e.source p
  cases source : e.source <;>
    simpa only [Entry.wrap, source, replaceFrame, Pointer.plug] using trace

end RotationBST.HeavyPath.Recursive.History
