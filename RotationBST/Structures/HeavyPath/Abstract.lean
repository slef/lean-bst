module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Results
open LabelledCursor

theorem mass_nonnegative {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (nonnegative : Nonnegative weight t) : 0 ≤ mass weight t :=
  RotationBST.HeavyPath.mass_nonnegative nonnegative

theorem mass_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) : 0 < mass weight t :=
  RotationBST.HeavyPath.mass_positive positive nonempty

theorem right_light_half {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (nonnegative : Nonnegative weight (.node l x r)) (heavy : LeftHeavy weight l r) :
    2 * mass weight r ≤ mass weight (.node l x r) :=
  RotationBST.HeavyPath.right_light_half nonnegative heavy

theorem left_light_half {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (nonnegative : Nonnegative weight (.node l x r)) (heavy : ¬ LeftHeavy weight l r) :
    2 * mass weight l ≤ mass weight (.node l x r) :=
  RotationBST.HeavyPath.left_light_half nonnegative heavy

theorem unit_positive {α : Type} (t : LabelledTree α) : Positive (fun _ => 1) t :=
  RotationBST.HeavyPath.unit_positive t

theorem unit_mass {α : Type} (t : LabelledTree α) : mass (fun _ => 1) t = (t.erase.size : ℝ) :=
  RotationBST.HeavyPath.unit_mass t

theorem decomposition {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil ∧ (extract weight t).tree = t ∧
      SolidContext weight (extract weight t).focus (extract weight t).context ∧
      mass weight t = weight x + ((extract weight t).context.map (frameMass weight)).sum ∧
      Path weight t x 0 (extract weight t).context.length ∧
      Pointer.Trace ⟨t.erase, []⟩ (extract weight t).erase (extract weight t).context.length :=
  RotationBST.HeavyPath.decomposition positive nonempty

theorem extract_tree {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    (extract weight t).tree = t :=
  RotationBST.HeavyPath.extract_tree weight t

theorem extract_nonempty {α : Type} (weight : α → ℝ) {t : LabelledTree α} (nonempty : t ≠ .nil) :
    (extract weight t).focus ≠ .nil :=
  RotationBST.HeavyPath.extract_nonempty weight nonempty

theorem extract_solid {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    SolidContext weight (extract weight t).focus (extract weight t).context :=
  RotationBST.HeavyPath.extract_solid weight t

theorem extract_terminal {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil :=
  RotationBST.HeavyPath.extract_terminal positive nonempty

theorem extract_mass {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    mass weight t = mass weight (extract weight t).focus +
      ((extract weight t).context.map (frameMass weight)).sum :=
  RotationBST.HeavyPath.extract_mass weight t

theorem extract_trace {α : Type} (weight : α → ℝ) {t : LabelledTree α} (nonempty : t ≠ .nil) :
    Pointer.Trace ⟨t.erase, []⟩ (extract weight t).erase (extract weight t).context.length :=
  RotationBST.HeavyPath.extract_trace weight nonempty

theorem extract_order {α : Type} [LT α] (weight : α → ℝ) {t : LabelledTree α} (ordered : t.Ordered) :
    (lowerKeys (extract weight t).context).Pairwise (fun a b => b < a) ∧
      (upperKeys (extract weight t).context).Pairwise (fun a b => a < b) ∧
      ∀ y ∈ (extract weight t).focus.inorder,
        (∀ x ∈ lowerKeys (extract weight t).context, x < y) ∧
        (∀ x ∈ upperKeys (extract weight t).context, y < x) :=
  RotationBST.HeavyPath.extract_order weight ordered

theorem extract_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    Positive weight (extract weight t).focus ∧
      ∀ frame ∈ (extract weight t).context, 0 < frameMass weight frame :=
  RotationBST.HeavyPath.extract_positive positive

theorem path_exists {α : Type} (weight : α → ℝ) {t : LabelledTree α} {x : α}
    (mem : x ∈ t.inorder) : ∃ lights depth, Path weight t x lights depth :=
  RotationBST.HeavyPath.path_exists weight mem

theorem lights_le_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) : lights ≤ depth :=
  RotationBST.HeavyPath.lights_le_depth path

theorem path_mass {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) :
    (2 : ℝ) ^ lights * weight x ≤ mass weight t :=
  RotationBST.HeavyPath.path_mass path nonnegative

theorem light_bound {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) (positive : 0 < weight x) :
    (lights : ℝ) ≤ Real.logb 2 (mass weight t / weight x) :=
  RotationBST.HeavyPath.light_bound path nonnegative positive

theorem path_context {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) :
    ∃ l r cs, plug cs (.node l x r) = t ∧ cs.length = depth :=
  RotationBST.HeavyPath.path_context path

theorem path_access {α : Type} {weight : α → ℝ} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path weight t x lights depth) (nonnegative : Nonnegative weight t) (positive : 0 < weight x) :
    ∃ l r cs, plug cs (.node l x r) = t ∧ cs.length = depth ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨.node l.erase r.erase, cs.map Frame.erase⟩ depth ∧
      (lights : ℝ) ≤ Real.logb 2 (mass weight t / weight x) :=
  RotationBST.HeavyPath.path_access path nonnegative positive

theorem unit_light_bound {α : Type} {t : LabelledTree α} {x : α} {lights depth : Nat}
    (path : Path (fun _ => 1) t x lights depth) : (lights : ℝ) ≤ Real.logb 2 t.erase.size :=
  RotationBST.HeavyPath.unit_light_bound path

theorem extract_path {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil ∧
      Path weight t x 0 (extract weight t).context.length :=
  RotationBST.HeavyPath.extract_path positive nonempty

end RotationBST.HeavyPath.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Results`: 23 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract]
