module

public import RotationBST.Algorithms.Tango.State.ComponentPath.Address.Proofs
public import RotationBST.Algorithms.Tango.State.Nesting.Matching
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Lists
public import RotationBST.Algorithms.Tango.State.Context.Replacement

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Replacing below a reached component is the composition of the two paths. -/
theorem replaceAt_append (s child : MarkedTree) (xs ys : List Nat)
    (target : ComponentNesting) (found : s.componentAt xs = some child) :
    s.nesting.replaceAt (xs ++ ys) target =
      s.nesting.replaceAt xs (child.nesting.replaceAt ys target) := by
  induction xs generalizing s with
  | nil =>
    have equal : s = child := Option.some.inj found
    subst s
    rfl
  | cons i xs ih =>
    cases slot : s.fringe[i]? with
    | none => simp [componentAt, slot] at found
    | some next =>
      have tail : next.componentAt xs = some child := by
        simpa only [componentAt, slot, Option.bind_some] using found
      have nested : s.nesting.fringe[i]? = some next.nesting := by
        rw [nesting_fringe, List.getElem?_map, slot]
        rfl
      simp only [List.cons_append, ComponentNesting.replaceAt, nested]
      rw [ih next tail]

end RotationBST.Tango.MarkedTree

namespace RotationBST.Tango.Context
open MarkedTree

/-- The computed address also specifies the effect of replacing the focused
subtree. Thus it identifies an edit, not just a location in the source tree. -/
theorem componentAddress_replace (fs : List Frame) (source target : MarkedTree) :
    (plug fs target).nesting = (plug fs source).nesting.replaceAt
      (componentAddress fs).1 (plug (componentAddress fs).2 target).nesting := by
  induction fs generalizing source target with
  | nil => rfl
  | cons f fs ih =>
    cases marked : f.marked
    · simpa only [componentAddress, marked, Bool.false_eq_true, ite_false, plug] using
        ih (f.fill source) (f.fill target)
    · have localReplacement :
          (plug (f :: (componentAddress fs).2) target).nesting =
            (plug (f :: (componentAddress fs).2) source).nesting.replaceAt
              [(before (f :: (componentAddress fs).2)).length] target.nesting := by
        have fringe (t : MarkedTree) := boundary_fringe_exact f marked _ (componentAddress_unmarked fs) t
        have slot : (plug (f :: (componentAddress fs).2) source).nesting.fringe[
            (before (f :: (componentAddress fs).2)).length]? = some source.nesting := by
          rw [nesting_fringe, fringe]
          simp [List.map_append, List.append_assoc]
        rw [ComponentNesting.replaceAt, slot]
        rw [nesting_branch _ (plug_nonempty _ _ (by simp))]
        rw [nesting_fringe, nesting_fringe, fringe, fringe]
        simp [List.map_append, List.append_assoc, ComponentNesting.replaceAt]
      simp only [componentAddress, marked, ite_true, plug]
      rw [replaceAt_append _ _ _ _ _ (componentAddress_spec fs (f.fill source))]
      simp only [plug] at localReplacement
      rw [← localReplacement]
      exact ih (f.fill source) (f.fill target)

end RotationBST.Tango.Context
