module

public import RotationBST.Tango.Paths.Geometry.Proofs
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace RotationBST.Tango

/-- A nonempty interval can be selected using its two extreme keys. -/
theorem keyInterval_window {inside outside : List Nat} (interval : KeyInterval inside outside)
    (subset : ∀ x ∈ inside, x ∈ outside) (nonempty : inside ≠ []) :
    ∃ low high : Nat, low ≤ high ∧
      inside.toFinset = outside.toFinset.filter (fun x => low ≤ x ∧ x ≤ high) := by
  have hn : inside.toFinset.Nonempty := by
    cases inside with
    | nil => contradiction
    | cons a as => exact ⟨a, by simp⟩
  let low := inside.toFinset.min' hn
  let high := inside.toFinset.max' hn
  have hl : low ∈ inside := List.mem_toFinset.mp (Finset.min'_mem _ hn)
  have hh : high ∈ inside := List.mem_toFinset.mp (Finset.max'_mem _ hn)
  refine ⟨low, high, Finset.min'_le_max' _ hn, ?_⟩
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · intro hx
    exact ⟨subset x hx, Finset.min'_le _ x (List.mem_toFinset.mpr hx),
      Finset.le_max' _ x (List.mem_toFinset.mpr hx)⟩
  · rintro ⟨hx, hlx, hxh⟩
    exact interval low hl high hh x hx hlx hxh

/-- Every nonempty depth suffix of a preferred path has two key boundaries. -/
theorem preferred_suffix_window (reference : Tree) (past : List Nat) {path : List Nat}
    (member : path ∈ preferredPaths reference past) (k : Nat) (nonempty : path.drop k ≠ []) :
    ∃ low high : Nat, low ≤ high ∧
      (path.drop k).toFinset = path.toFinset.filter (fun x => low ≤ x ∧ x ≤ high) := by
  apply keyInterval_window
    (referencePath_suffix_interval (decompose_referencePaths reference 0 past path member) k)
  · intro x hx; exact List.mem_of_mem_drop hx
  · exact nonempty

end RotationBST.Tango
