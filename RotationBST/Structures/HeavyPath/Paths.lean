module

public import RotationBST.Structures.HeavyPath.Extraction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

/-- Every labelled occurrence has a path with the canonical light-edge count. -/
theorem path_exists {α : Type} (weight : α → ℝ) {t : LabelledTree α} {x : α}
    (mem : x ∈ t.inorder) : ∃ lights depth, Path weight t x lights depth := by
  classical
  induction t with
  | nil => cases mem
  | node l y r ihL ihR =>
    simp only [LabelledTree.inorder, List.mem_append, List.mem_cons] at mem
    rcases mem with mem | rfl | mem
    · obtain ⟨lights, depth, found⟩ := ihL mem
      by_cases heavy : LeftHeavy weight l r
      · exact ⟨_, _, .leftSolid found heavy⟩
      · exact ⟨_, _, .leftLight found heavy⟩
    · exact ⟨0, 0, .root l r x⟩
    · obtain ⟨lights, depth, found⟩ := ihR mem
      by_cases heavy : LeftHeavy weight l r
      · exact ⟨_, _, .rightLight found heavy⟩
      · exact ⟨_, _, .rightSolid found heavy⟩

theorem lights_le_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) : lights ≤ depth := by
  induction path <;> omega

/-- Dotted edges halve the remaining subtree mass; solid edges only need
nonnegativity. This counts actual path edges rather than chosen weight ratios. -/
theorem path_mass {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) :
    (2 : ℝ) ^ lights * weight x ≤ mass weight t := by
  induction path with
  | root l r x =>
    have left := mass_nonnegative nonnegative.1
    have right := mass_nonnegative nonnegative.2.2
    simp only [pow_zero, one_mul, mass]
    linarith only [left, right]
  | leftSolid found heavy ih =>
    have bound := ih nonnegative.1
    have right := mass_nonnegative nonnegative.2.2
    simp only [mass]
    linarith only [bound, right, nonnegative.2.1]
  | leftLight found heavy ih =>
    have bound := ih nonnegative.1
    have half := left_light_half nonnegative heavy
    simp only [pow_succ]
    nlinarith only [bound, half]
  | rightSolid found heavy ih =>
    have bound := ih nonnegative.2.2
    have left := mass_nonnegative nonnegative.1
    simp only [mass]
    linarith only [bound, left, nonnegative.2.1]
  | rightLight found heavy ih =>
    have bound := ih nonnegative.2.2
    have half := right_light_half nonnegative heavy
    simp only [pow_succ]
    nlinarith only [bound, half]

/-- Theorem 5's heavy-path count: a positive-weight node is reached after at
most `log₂(W/w)` dotted edges. Its original total depth may be much larger. -/
theorem light_bound {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) (positive : 0 < weight x) :
    (lights : ℝ) ≤ Real.logb 2 (mass weight t / weight x) := by
  have ratio : (2 : ℝ) ^ lights ≤ mass weight t / weight x :=
    (le_div_iff₀ positive).mpr (path_mass path nonnegative)
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

/-- A path identifies the exact original labelled node and pointer context. -/
theorem path_context {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) :
    ∃ l r cs, plug cs (.node l x r) = t ∧ cs.length = depth := by
  induction path with
  | root l r x => exact ⟨l, r, [], rfl, rfl⟩
  | @leftSolid l r x y lights depth found heavy ih
  | @leftLight l r x y lights depth found heavy ih =>
    obtain ⟨a, b, cs, whole, length⟩ := ih
    refine ⟨a, b, cs ++ [.left x r], ?_, ?_⟩
    · rw [plug_append, whole]; rfl
    · simp [length]
  | @rightSolid l r x y lights depth found heavy ih
  | @rightLight l r x y lights depth found heavy ih =>
    obtain ⟨a, b, cs, whole, length⟩ := ih
    refine ⟨a, b, cs ++ [.right l x], ?_, ?_⟩
    · rw [plug_append, whole]; rfl
    · simp [length]

/-- Original-tree pointer access and the light-edge estimate refer to the
same labelled occurrence. Only the dotted-edge count is logarithmic here. -/
theorem path_access {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) (positive : 0 < weight x) :
    ∃ l r cs, plug cs (.node l x r) = t ∧ cs.length = depth ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨.node l.erase r.erase, cs.map Frame.erase⟩ depth ∧
      (lights : ℝ) ≤ Real.logb 2 (mass weight t / weight x) := by
  obtain ⟨l, r, cs, whole, length⟩ := path_context path
  have trace := cursor_trace (⟨.node l x r, cs⟩ : Config α) (by intro h; cases h)
  change Pointer.Trace ⟨(plug cs (.node l x r)).erase, []⟩
    ⟨.node l.erase r.erase, cs.map Frame.erase⟩ cs.length at trace
  rw [whole, length] at trace
  exact ⟨l, r, cs, whole, length, trace, light_bound path nonnegative positive⟩

theorem unit_light_bound {α : Type} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path (fun _ => 1) t x lights depth) : (lights : ℝ) ≤ Real.logb 2 t.erase.size := by
  simpa only [unit_mass, div_one] using light_bound path (positive_nonnegative (unit_positive t)) (by norm_num)

/-- Extending through a solid context adds physical depth but no dotted edges. -/
theorem solid_extend_path {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α}
    {lights depth : Nat} (path : Path weight t x lights depth) {cs : List (Frame α)}
    (solid : SolidContext weight t cs) : Path weight (plug cs t) x lights (depth + cs.length) := by
  induction cs generalizing t depth with
  | nil => simpa only [List.length_nil, Nat.add_zero, plug] using path
  | cons frame cs ih =>
    cases frame with
    | left y r =>
      have extended := ih (.leftSolid path solid.1) solid.2
      simpa only [List.length_cons, plug, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended
    | right l y =>
      have extended := ih (.rightSolid path solid.1) solid.2
      simpa only [List.length_cons, plug, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended

theorem extract_path {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil ∧
      Path weight t x 0 (extract weight t).context.length := by
  obtain ⟨x, focus⟩ := extract_terminal positive nonempty
  have solid := extract_solid weight t
  rw [focus] at solid
  have path := solid_extend_path (Path.root (weight := weight) .nil .nil x) solid
  have whole : plug (extract weight t).context (.node .nil x .nil) = t := by
    rw [← focus]
    exact extract_tree weight t
  rw [whole] at path
  exact ⟨x, focus, by simpa only [Nat.zero_add] using path⟩

end RotationBST.HeavyPath
