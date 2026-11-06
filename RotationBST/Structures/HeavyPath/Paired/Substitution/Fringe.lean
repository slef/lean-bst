module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Build
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

/-- The two physical fringes retain the original off-path subtrees in inorder
order. In particular, reflection never leaks into a retained upper payload. -/
theorem buildWith_fringe {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).lower.decode.fringe =
      (lowerSlotsWith weight payload cs).reverse ++ p.lower.decode.fringe ∧
    (Stacks.buildWith weight payload cs p).upper.decode.mirror.fringe =
      p.upper.decode.mirror.fringe ++ upperSlotsWith weight payload cs := by
  induction cs generalizing p with
  | nil => simp [Stacks.buildWith, lowerSlotsWith, upperSlotsWith]
  | cons frame cs ih =>
    have firstNonnegative := nonnegative frame (by simp)
    obtain ⟨lower, upper⟩ := ih (pushWith_valid payload valid firstNonnegative)
      (by intro f hf; exact nonnegative f (by simp [hf]))
    cases frame with
    | left x r =>
      have pushed := (Chocolate.Results.push valid.2 (.leaf (payload r).mirror _) firstNonnegative []).2.1
      simp only [frameMass] at pushed
      refine ⟨lower, ?_⟩
      change (Stacks.buildWith weight payload cs (p.pushWith weight payload (.left x r))).upper.decode.mirror.fringe = _
      rw [upper]
      simp only [Stacks.pushWith, WeightedTree.mirror_fringe, pushed, WeightedTree.fringe,
        List.map_cons, List.reverse_cons, Tree.mirror_mirror, upperSlotsWith, List.append_assoc,
        List.singleton_append]
    | right l x =>
      have pushed := (Chocolate.Results.push valid.1 (.leaf (payload l) _) firstNonnegative []).2.1
      simp only [frameMass] at pushed
      refine ⟨?_, upper⟩
      change (Stacks.buildWith weight payload cs (p.pushWith weight payload (.right l x))).lower.decode.fringe = _
      rw [lower]
      simp only [Stacks.pushWith, pushed, WeightedTree.fringe, lowerSlotsWith, List.reverse_cons,
        List.append_assoc, List.singleton_append]

end RotationBST.HeavyPath.Paired
