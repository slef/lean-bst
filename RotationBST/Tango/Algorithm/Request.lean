module

public import RotationBST.Tango.State.Preferences.Correctness
public import RotationBST.Tango.State.Nesting.Partition
public import RotationBST.Tango.Paths.Update
public import RotationBST.Tango.Algorithm.Request.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Update preferences and then access the requested key in the root component.
This serves a complete request and preserves the full next-history invariant. -/
theorem serve_spec (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    Access s.tree (s.serve reference past x).1.tree x (s.serve reference past x).2 ∧
      Maintains (s.serve reference past x).1 reference (past ++ [x]) ∧
      ((s.serve reference past x).2 : ℝ) + (s.serve reference past x).1.potential - s.potential ≤
        (preferenceUpdates reference 0 past x).length * (14 * Real.logb 2 (height reference) + 4) +
          (3 * Real.logb 2 (height reference) + 1) := by
  let updated := (s.updatePreferences (canonical reference 0 past) (preferenceUpdates reference 0 past x)).1
  obtain ⟨nesting, rotations, ba⟩ :=
    updatePreferences_spec s (canonical reference 0 past) (preferenceUpdates reference 0 past x)
      maintained.2 (canonical_pathMarked reference 0 past)
      (by
        intro e he
        simpa only [canonical_tree, Nat.zero_add] using (preferenceUpdates_bounds reference 0 past x e he).2)
  rw [preferenceUpdates_canonical reference past x history valid] at nesting
  have updatedInvariant := maintains_of_nesting updated reference (past ++ [x]) nesting
  have onPath : x ∈ updated.region.keys 0 := by
    rw [updatedInvariant.1.2.2]
    exact List.mem_toFinset.mpr (request_on_root_path reference 0 past x (Nat.zero_le _) (by simpa using valid))
  obtain ⟨served, invariant, bb⟩ :=
    maintained_splayRoot updated reference (past ++ [x]) updatedInvariant x onPath
  refine ⟨⟨rotations.append served.1, served.2⟩, invariant, ?_⟩
  simp only [canonical_tree] at ba
  simp only [serve, Nat.cast_add]
  dsimp only [updated] at bb
  linarith

/-- Every valid request has the computed realization `serve`. -/
theorem serve_request (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      Access s.tree result.tree x cost ∧ Maintains result reference (past ++ [x]) ∧
      (cost : ℝ) + result.potential - s.potential ≤
        (preferenceUpdates reference 0 past x).length * (14 * Real.logb 2 (height reference) + 4) +
          (3 * Real.logb 2 (height reference) + 1) := by
  exact ⟨_, _, serve_spec s reference past x maintained history valid⟩

end RotationBST.Tango.MarkedTree
