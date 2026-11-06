module

public import RotationBST.Structures.HeavyPath.Paths
public import RotationBST.Structures.HeavyPath.Ordering
public import RotationBST.Structures.HeavyPath.Charges
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath

/-- A maximal positive-weight heavy path retains every node and off-path
subtree, partitions mass, and has an actual pointer descent to its endpoint. -/
theorem decomposition {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil ∧ (extract weight t).tree = t ∧
      SolidContext weight (extract weight t).focus (extract weight t).context ∧
      mass weight t = weight x + ((extract weight t).context.map (frameMass weight)).sum ∧
      Path weight t x 0 (extract weight t).context.length ∧
      Pointer.Trace ⟨t.erase, []⟩ (extract weight t).erase (extract weight t).context.length := by
  obtain ⟨x, focus, path⟩ := extract_path positive nonempty
  have massEq := extract_mass weight t
  rw [focus] at massEq
  simp only [mass, zero_add, add_zero] at massEq
  exact ⟨x, focus, extract_tree weight t, extract_solid weight t, massEq, path, extract_trace weight nonempty⟩

end RotationBST.HeavyPath
