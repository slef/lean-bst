module

public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Simulation
public import RotationBST.Algorithms.Tango.State.Context.Lifting

@[expose] public section
namespace RotationBST.Tango

/-- A cut inside an unmarked child is still one interval cut of the parent's
component, even when that component has a different binary shape. -/
theorem Context.Frame.transport_cut (f : Context.Frame) (unmarked : f.marked = false)
    {s t : MarkedTree} (cut : ComponentNesting.Cut s.nesting t.nesting) :
    ComponentNesting.Cut (f.fill s).nesting (f.fill t).nesting := by
  generalize hs : s.nesting = sn at cut
  generalize ht : t.nesting = tn at cut
  cases cut with
  | interval a b c nonempty remaining =>
    cases f with
    | left r cl cr =>
      have hc : cl = false := unmarked
      subst cl
      simpa only [Context.Frame.fill, MarkedTree.nesting, Bool.false_eq_true, ite_false,
        hs, ht, ComponentNesting.fringe, List.append_assoc] using
        ComponentNesting.Cut.interval a b (c ++ (if cr then [r.nesting] else r.nesting.fringe))
          nonempty (by simp only [List.length_append]; omega)
    | right l cr cl =>
      have hc : cr = false := unmarked
      subst cr
      simpa only [Context.Frame.fill, MarkedTree.nesting, Bool.false_eq_true, ite_false,
        hs, ht, ComponentNesting.fringe, List.append_assoc] using
        ComponentNesting.Cut.interval ((if cl then [l.nesting] else l.nesting.fringe) ++ a) b c
          nonempty (by simp only [List.length_append]; omega)

/-- All ancestors within an auxiliary component can be crossed without adding
cuts or rotations to the interval-cut description. -/
theorem Context.transport_cut (fs : List Context.Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) {s t : MarkedTree}
    (cut : ComponentNesting.Cut s.nesting t.nesting) :
    ComponentNesting.Cut (Context.plug fs s).nesting (Context.plug fs t).nesting := by
  induction fs generalizing s t with
  | nil => exact cut
  | cons f fs ih =>
    exact ih (fun g hg => unmarked g (List.mem_cons_of_mem _ hg))
      (Context.Frame.transport_cut f (unmarked f (List.mem_cons_self ..)) cut)

end RotationBST.Tango
