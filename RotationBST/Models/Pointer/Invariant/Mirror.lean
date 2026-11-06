module

public import RotationBST.Models.Pointer.Invariant.Proofs
public import RotationBST.Models.Pointer.Mirror.Abstract

@[expose] public section
namespace RotationBST.Pointer.TraceWithin

/-- Reflect each physical step and its invariant, preserving the exact cost. -/
theorem mirror {P : Tree → Prop} {a b : Config} {cost : Nat}
    (h : TraceWithin P a b cost) :
    TraceWithin (fun t => P t.mirror) a.mirror b.mirror cost := by
  induction h with
  | refl holds =>
    apply TraceWithin.refl
    simpa only [Config.mirror_tree, Tree.mirror_mirror] using holds
  | step holds step _ ih =>
    apply TraceWithin.step _ step.mirror ih
    simpa only [Config.mirror_tree, Tree.mirror_mirror] using holds

end RotationBST.Pointer.TraceWithin
