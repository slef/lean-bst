module

public import RotationBST.Tango.State.Preferences.Algorithm.Marks
public import RotationBST.Tango.State.Preferences.Lookup.Proofs
public import RotationBST.Tango.State.ComponentPath.Address.Replacement
public import RotationBST.Tango.State.ComponentPath.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Context

/-- One computed reference-key update preserves the exact component nesting and
has a height-dependent amortized bound, independently of actual auxiliary shapes. -/
theorem updatePreference_spec (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : key < reference.tree.size) :
    (s.updatePreference reference key next).1.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree (s.updatePreference reference key next).1.tree
        (s.updatePreference reference key next).2 ∧
      ((s.updatePreference reference key next).2 : ℝ) +
        (s.updatePreference reference key next).1.potential - s.potential ≤
          14 * Real.logb 2 (height reference.tree) + 4 := by
  obtain ⟨fs, l, r, cl, cr, located, source, target⟩ := locateKey_spec reference key next valid
  let inner := (componentAddress fs).2
  let outer := (splitComponent fs).2
  have context : fs = inner ++ outer := by
    simpa only [inner, outer, componentAddress_inner] using (splitComponent_spec fs).1
  have before : reference = plug outer (plug inner (.node l r cl cr)) := by
    rw [source, context, plug_append]
  have after : reference.setPreference key next = plug outer (plug inner (.node l r (!next) next)) := by
    rw [target, context, plug_append]
  have sourcePaths := before ▸ paths
  have targetPaths := after ▸ setPreference_pathMarked reference key next paths
  have beforeBound : (plug inner (.node l r cl cr)).region.size ≤ height reference.tree := by
    rw [before]
    exact (region_size_le_height _ (pathMarked_focus outer _ sourcePaths)).trans (height_le_plug outer _)
  have afterBound : (plug inner (.node l r (!next) next)).region.size ≤ height reference.tree := by
    have h := (region_size_le_height _ (pathMarked_focus outer _ targetPaths)).trans (height_le_plug outer _)
    simpa only [← after, setPreference_tree] using h
  have edge := (pathMarked_focus fs (.node l r cl cr) (source ▸ paths)).2.2
  have found : reference.componentAt (componentAddress fs).1 = some (plug inner (.node l r cl cr)) := by
    rw [source]
    exact componentAddress_spec fs _
  have nonempty : plug inner (.node l r cl cr) ≠ .nil := by
    by_cases empty : inner = []
    · simp [empty, plug]
    · exact plug_nonempty inner _ empty
  have computed := editAt_simulates (componentAddress fs).1 s reference
    (plug inner (.node l r cl cr)) (plug inner (.node l r (!next) next)).nesting
    (14 * Real.logb 2 (height reference.tree) + 4)
    (fun actual => actual.setMarksInPath inner l r cl cr next) same found nonempty
    (fun actual nested => setMarksInPath_spec actual inner (componentAddress_unmarked fs)
      l r cl cr next edge _ nested beforeBound afterBound)
  have replacement : (reference.setPreference key next).nesting =
      reference.nesting.replaceAt (componentAddress fs).1 (plug inner (.node l r (!next) next)).nesting := by
    rw [target, source]
    exact componentAddress_replace fs _ _
  simpa only [updatePreference, located, ← replacement] using computed

end RotationBST.Tango.MarkedTree
