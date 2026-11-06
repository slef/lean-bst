module

public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Marks
public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Update
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Context

/-- A first setting toward an empty child leaves the entire component alone. -/
theorem setMarksInPath_initial_empty (s : MarkedTree) (fs : List Frame)
    (l r : MarkedTree) (next : Bool) (empty : (if next then l else r) = .nil) :
    s.setMarksInPath fs l r true true next = (s, 0) := by
  cases next <;> simp_all [setMarksInPath, unmarkKnownInPath]

/-- Empty first settings have zero potential change as well as zero rotations;
only nonempty joins receive a logarithmic component charge. -/
theorem setMarksInPath_initial_charge (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) (l r : MarkedTree) (next : Bool)
    (same : s.nesting = (plug fs (.node l r true true)).nesting) :
    (s.setMarksInPath fs l r true true next).1.nesting = (plug fs (.node l r (!next) next)).nesting ∧
      Rotations s.tree (s.setMarksInPath fs l r true true next).1.tree
        (s.setMarksInPath fs l r true true next).2 ∧
      ((s.setMarksInPath fs l r true true next).2 : ℝ) +
        (s.setMarksInPath fs l r true true next).1.potential - s.potential ≤
          if (if next then l else r) = .nil then 0
          else 8 * Real.logb 2 (plug fs (.node l r (!next) next)).region.size + 2 := by
  cases next
  · simpa [setMarksInPath, Frame.setMark, Frame.fill, plug] using
      unmarkKnownInPath_spec s fs unmarked (.right l true true) r same
  · simpa [setMarksInPath, Frame.setMark, Frame.fill, plug] using
      unmarkKnownInPath_spec s fs unmarked (.left r true true) l same

/-- Compiling and locating an empty first setting introduces no rotations,
even when the selected component is nested below other components. -/
theorem updatePreference_initial_empty_cost (s reference : MarkedTree) (key : Nat) (next : Bool)
    (l r : MarkedTree) (fs : List Frame)
    (located : reference.locateKey key = some (.node l r true true, fs))
    (empty : (if next then l else r) = .nil) :
    (s.updatePreference reference key next).2 = 0 := by
  simpa only [updatePreference, located] using
    editAt_zero_cost (componentAddress fs).1 s
      (fun actual => actual.setMarksInPath (componentAddress fs).2 l r true true next)
      (fun actual => by rw [setMarksInPath_initial_empty actual _ l r next empty])

/-- A first preference performs only a join. Retain the resulting component's
actual size in its amortized charge, rather than replacing it by the global
reference height. This is the local initialization cost to be summed. -/
theorem setMarksInPath_initial_spec (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) (l r : MarkedTree) (next : Bool)
    (same : s.nesting = (plug fs (.node l r true true)).nesting) :
    (s.setMarksInPath fs l r true true next).1.nesting = (plug fs (.node l r (!next) next)).nesting ∧
      Rotations s.tree (s.setMarksInPath fs l r true true next).1.tree
        (s.setMarksInPath fs l r true true next).2 ∧
      ((s.setMarksInPath fs l r true true next).2 : ℝ) +
        (s.setMarksInPath fs l r true true next).1.potential - s.potential ≤
          8 * Real.logb 2 (plug fs (.node l r (!next) next)).region.size + 2 := by
  cases next
  · simpa [setMarksInPath, Frame.setMark, Frame.fill, plug] using
      unmarkKnownInPath_bound s fs unmarked (.right l true true) r same
  · simpa [setMarksInPath, Frame.setMark, Frame.fill, plug] using
      unmarkKnownInPath_bound s fs unmarked (.left r true true) l same

/-- Lift the sharper first-setting charge through the compiled component
lookup. The credit uses the actual target reference component's size. -/
theorem updatePreference_initial_spec (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked) (valid : key < reference.tree.size)
    (first : ∃ l r fs, reference.locateKey key = some (.node l r true true, fs)) :
    ∃ size : Nat,
      size ≤ height reference.tree ∧
      (s.updatePreference reference key next).1.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree (s.updatePreference reference key next).1.tree
        (s.updatePreference reference key next).2 ∧
      ((s.updatePreference reference key next).2 : ℝ) +
        (s.updatePreference reference key next).1.potential - s.potential ≤ 8 * Real.logb 2 size + 2 := by
  obtain ⟨fs, l, r, cl, cr, located, source, target⟩ := locateKey_spec reference key next valid
  obtain ⟨a, b, gs, first⟩ := first
  have eq := Option.some.inj (located.symm.trans first)
  cases eq
  let inner := (componentAddress fs).2
  let outer := (splitComponent fs).2
  have context : fs = inner ++ outer := by
    simpa only [inner, outer, componentAddress_inner] using (splitComponent_spec fs).1
  have after : reference.setPreference key next = plug outer (plug inner (.node l r (!next) next)) := by
    rw [target, context, plug_append]
  let size := (plug inner (.node l r (!next) next)).region.size
  have found : reference.componentAt (componentAddress fs).1 = some (plug inner (.node l r true true)) := by
    rw [source]
    exact componentAddress_spec fs _
  have nonempty : plug inner (.node l r true true) ≠ .nil := by
    by_cases empty : inner = []
    · simp [empty, plug]
    · exact plug_nonempty inner _ empty
  have computed := editAt_simulates (componentAddress fs).1 s reference
    (plug inner (.node l r true true)) (plug inner (.node l r (!next) next)).nesting
    (8 * Real.logb 2 size + 2)
    (fun actual => actual.setMarksInPath inner l r true true next) same found nonempty
    (fun actual nested => setMarksInPath_initial_spec actual inner (componentAddress_unmarked fs) l r next nested)
  have replacement : (reference.setPreference key next).nesting =
      reference.nesting.replaceAt (componentAddress fs).1 (plug inner (.node l r (!next) next)).nesting := by
    rw [target, source]
    exact componentAddress_replace fs _ _
  refine ⟨size, ?_, ?_⟩
  · have targetPaths := after ▸ setPreference_pathMarked reference key next paths
    have bound := (region_size_le_height _ (pathMarked_focus outer _ targetPaths)).trans (height_le_plug outer _)
    simpa only [← after, setPreference_tree] using bound
  · simpa only [updatePreference, located, ← replacement] using computed

end RotationBST.Tango.MarkedTree
