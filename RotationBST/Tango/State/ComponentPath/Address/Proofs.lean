module

public import RotationBST.Tango.State.ComponentPath.Address.Abstract
public import RotationBST.Tango.State.Context.Fringe.Exact
public import RotationBST.Tango.State.Context.Split.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree

theorem componentAt_append (s : MarkedTree) (xs ys : List Nat) :
    s.componentAt (xs ++ ys) = (s.componentAt xs).bind (fun child => child.componentAt ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.cons_append, componentAt]
    cases s.fringe[i]? <;> simp only [Option.bind_none, Option.bind_some, ih]

end RotationBST.Tango.MarkedTree

namespace RotationBST.Tango.Context
open MarkedTree

theorem componentAddress_unmarked (fs : List Frame) :
    ∀ f ∈ (componentAddress fs).2, f.marked = false := by
  induction fs with
  | nil => simp [componentAddress]
  | cons f fs ih =>
    cases marked : f.marked
    · simp only [componentAddress, marked, Bool.false_eq_true, ite_false]
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact marked
      · exact ih g hg
    · simp [componentAddress, marked]

/-- Address compilation retains exactly the local part of the boundary split. -/
theorem componentAddress_inner (fs : List Frame) :
    (componentAddress fs).2 = (splitComponent fs).1 := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases marked : f.marked <;> simp [componentAddress, splitComponent, marked, ih]

/-- Following the computed component address reaches exactly the subtree
obtained by plugging the focused node into its unmarked inner context. -/
theorem componentAddress_spec (fs : List Frame) (s : MarkedTree) :
    (plug fs s).componentAt (componentAddress fs).1 = some (plug (componentAddress fs).2 s) := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    have reached := ih (f.fill s)
    cases marked : f.marked
    · simpa only [componentAddress, marked, Bool.false_eq_true, ite_false, plug] using reached
    · have slot : (plug (f :: (componentAddress fs).2) s).fringe[
          (before (f :: (componentAddress fs).2)).length]? = some s := by
        rw [boundary_fringe_exact f marked _ (componentAddress_unmarked fs) s]
        simp [List.append_assoc]
      simp only [componentAddress, marked, ite_true, plug, componentAt_append, reached, Option.bind_some]
      change ((plug (f :: (componentAddress fs).2) s).fringe[
        (before (f :: (componentAddress fs).2)).length]?).bind (fun child => some child) = some s
      rw [slot]
      rfl

end RotationBST.Tango.Context
