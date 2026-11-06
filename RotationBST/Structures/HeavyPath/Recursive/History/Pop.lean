module

public import RotationBST.Structures.HeavyPath.Recursive.History.Entries
public import RotationBST.Structures.HeavyPath.Paired.Exposure.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Interruption.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate

private theorem lower_append {α : Type} (es ds : List (Entry α)) : lower (es ++ ds) = lower ds ++ lower es := by
  induction es with
  | nil => simp [lower]
  | cons e es ih => cases h : e.source <;> simp [lower, h, ih, List.append_assoc]

private theorem upper_append {α : Type} (es ds : List (Entry α)) : upper (es ++ ds) = upper es ++ upper ds := by
  induction es with
  | nil => simp [upper]
  | cons e es ih => cases h : e.source <;> simp [upper, h, ih]

private theorem upper_raw {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) :
    p.upper.decode.fringe = ((upper es).map (fun e => (e.shape.mirror, frameMass weight e.source))).reverse ++ [(.nil, 0)] := by
  have raw := mirror_fringe p.upper.decode.mirror
  rw [mirror_mirror, valid.upper] at raw
  simpa only [List.map_append, List.reverse_append, List.map_map, Function.comp_def,
    Entry.slot, List.map_cons, List.map_nil, List.reverse_singleton, Tree.mirror] using raw

private theorem upper_of_raw {α : Type} {weight : α → ℝ} {es : List (Entry α)} {stack : Layer}
    (raw : stack.decode.fringe = ((upper es).map (fun e => (e.shape.mirror, frameMass weight e.source))).reverse ++ [(.nil, 0)]) :
    stack.decode.mirror.fringe = [(.nil, 0)] ++ (upper es).map (Entry.slot weight) := by
  change stack.decode.mirror.fringe = [(.nil, 0)] ++
    (upper es).map (fun e => (e.shape, frameMass weight e.source))
  rw [mirror_fringe, raw]
  simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse,
    List.map_map, Function.comp_def, Tree.mirror_mirror, List.map_cons, List.map_nil,
    List.reverse_singleton, Tree.mirror]

/-- Pop precisely the outermost occurrence. The untouched payload entries
and their credits remain available to the recursive invariant. -/
theorem pop_path_within {α : Type} {weight : α → ℝ} {es : List (Entry α)} {e : Entry α} {p : Stacks}
    (valid : PathValid weight (es ++ [e]) p) :
    ∃ rest : Stacks, PathValid weight es rest ∧
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 10) ⟨p.tree, []⟩ ⟨e.wrap rest.tree, []⟩ (p.exposeCost e.source) ∧
      p.exposeCost e.source + rest.potential ≤ 24 + p.potential := by
  cases source : e.source with
  | right l x =>
    have front : p.lower.decode.fringe = (e.shape, frameMass weight e.source) ::
        ((lower es).map (Entry.slot weight) ++ [(.nil, 0)]) := by
      simpa [lower_append, lower, source, Entry.slot] using valid.lower
    obtain ⟨rest, popped, restValid, fringe, _, bound⟩ :=
      Chocolate.Top.Results.pop_front valid.pair.1 front (by simp)
    refine ⟨⟨rest, p.upper⟩, ⟨⟨restValid, valid.pair.2⟩, fringe, ?_⟩, ?_, ?_⟩
    · simpa [upper_append, upper, source] using valid.upper
    · simpa only [Entry.wrap, source, Stacks.exposeCost, WeightedTree.tree, WeightedTree.skeleton,
        Pointer.Lazy.Skeleton.tree] using Paired.Interruption.Results.lower_pop popped
    · change p.lower.popCost + 4 + (rest.potential + p.upper.potential) ≤
        24 + (p.lower.potential + p.upper.potential)
      omega
  | left x r =>
    have front : p.upper.decode.fringe = (e.shape.mirror, frameMass weight e.source) ::
        (((upper es).map (fun f => (f.shape.mirror, frameMass weight f.source))).reverse ++ [(.nil, 0)]) := by
      simpa [upper_append, upper, source] using upper_raw valid
    obtain ⟨rest, popped, restValid, fringe, _, bound⟩ :=
      Chocolate.Top.Results.pop_front valid.pair.2 front (by simp)
    refine ⟨⟨p.lower, rest⟩, ⟨⟨valid.pair.1, restValid⟩, ?_, upper_of_raw fringe⟩, ?_, ?_⟩
    · simpa [lower_append, lower, source] using valid.lower
    · simpa only [Entry.wrap, source, Stacks.exposeCost, WeightedTree.tree, WeightedTree.skeleton,
        Pointer.Lazy.Skeleton.tree, Tree.mirror_mirror] using Paired.Interruption.Results.upper_pop popped
    · change p.upper.popCost + 4 + (p.lower.potential + rest.potential) ≤
        24 + (p.lower.potential + p.upper.potential)
      omega

theorem pop_path {α : Type} {weight : α → ℝ} {es : List (Entry α)} {e : Entry α} {p : Stacks}
    (valid : PathValid weight (es ++ [e]) p) :
    ∃ rest : Stacks, PathValid weight es rest ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨e.wrap rest.tree, []⟩ (p.exposeCost e.source) ∧
      p.exposeCost e.source + rest.potential ≤ 24 + p.potential := by
  obtain ⟨rest, preserved, trace, bound⟩ := pop_path_within valid
  exact ⟨rest, preserved, trace.trace, bound⟩

end RotationBST.HeavyPath.Recursive.History
