module

public import RotationBST.Structures.HeavyPath.Paired.Build
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

/-- The two physical fringes retain the original off-path subtrees in inorder
order. In particular, reflection never leaks into a retained upper payload. -/
theorem build_fringe {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).lower.decode.fringe =
      (lowerSlots weight cs).reverse ++ p.lower.decode.fringe ∧
    (Stacks.build weight cs p).upper.decode.mirror.fringe =
      p.upper.decode.mirror.fringe ++ upperSlots weight cs := by
  induction cs generalizing p with
  | nil => simp [Stacks.build, lowerSlots, upperSlots]
  | cons frame cs ih =>
    have firstNonnegative := nonnegative frame (by simp)
    obtain ⟨lower, upper⟩ := ih (push_valid valid firstNonnegative)
      (by intro f hf; exact nonnegative f (by simp [hf]))
    cases frame with
    | left x r =>
      have pushed := (Chocolate.Results.push valid.2 (.leaf r.erase.mirror _) firstNonnegative []).2.1
      simp only [frameMass] at pushed
      refine ⟨lower, ?_⟩
      change (Stacks.build weight cs (p.push weight (.left x r))).upper.decode.mirror.fringe = _
      rw [upper]
      simp only [Stacks.push, WeightedTree.mirror_fringe, pushed, WeightedTree.fringe,
        List.map_cons, List.reverse_cons, Tree.mirror_mirror, upperSlots, List.append_assoc,
        List.singleton_append]
    | right l x =>
      have pushed := (Chocolate.Results.push valid.1 (.leaf l.erase _) firstNonnegative []).2.1
      simp only [frameMass] at pushed
      refine ⟨?_, upper⟩
      change (Stacks.build weight cs (p.push weight (.right l x))).lower.decode.fringe = _
      rw [lower]
      simp only [Stacks.push, pushed, WeightedTree.fringe, lowerSlots, List.reverse_cons,
        List.append_assoc, List.singleton_append]

theorem empty_build_fringe {α : Type} {weight : α → ℝ} (cs : List (Frame α))
    (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs Stacks.empty).lower.decode.fringe =
      (lowerSlots weight cs).reverse ++ [(.nil, 0)] ∧
    (Stacks.build weight cs Stacks.empty).upper.decode.mirror.fringe =
      [(.nil, 0)] ++ upperSlots weight cs :=
  build_fringe cs empty_valid nonnegative

end RotationBST.HeavyPath.Paired
