module

public import RotationBST.Tango.State.Context.Abstract
public import RotationBST.Tango.State.Marking
public import RotationBST.Tango.State.Nesting.Proofs

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

private theorem frame_size (f : Frame) (s t : MarkedTree) (same : s.region.size = t.region.size) :
    (f.fill s).region.size = (f.fill t).region.size := by
  cases f with
  | left r cl cr => cases cl <;> cases cr <;> simp [Frame.fill, region, Pointer.Lazy.Skeleton.size, same]
  | right l cr cl => cases cl <;> cases cr <;> simp [Frame.fill, region, Pointer.Lazy.Skeleton.size, same]

private theorem frame_potential (f : Frame) (s t : MarkedTree) (same : s.region.size = t.region.size) :
    (f.fill t).potential - (f.fill s).potential = t.potential - s.potential := by
  have sizes := frame_size f s t same
  cases f <;> simp only [Frame.fill] at sizes ⊢ <;>
    rw [potential_node, potential_node, sizes] <;> ring

theorem plug_size (fs : List Frame) (s t : MarkedTree) (same : s.region.size = t.region.size) :
    (plug fs s).region.size = (plug fs t).region.size := by
  induction fs generalizing s t with
  | nil => exact same
  | cons f fs ih => exact ih _ _ (frame_size f s t same)

theorem plug_potential (fs : List Frame) (s t : MarkedTree) (same : s.region.size = t.region.size) :
    (plug fs t).potential - (plug fs s).potential = t.potential - s.potential := by
  induction fs generalizing s t with
  | nil => rfl
  | cons f fs ih =>
    exact (ih _ _ (frame_size f s t same)).trans (frame_potential f s t same)

/-- At a component boundary, local potential changes transfer exactly to the
whole tree, without any restriction on the new auxiliary component size. -/
theorem boundary_potential (fs : List Frame) (boundary : Boundary fs) (s t : MarkedTree) :
    (plug fs t).potential - (plug fs s).potential = t.potential - s.potential := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    have sizes : (f.fill s).region.size = (f.fill t).region.size := by
      cases f with
      | left r cl cr =>
        have h : cl = true := boundary
        subst cl
        simp [Frame.fill, region, Pointer.Lazy.Skeleton.size]
      | right l cr cl =>
        have h : cr = true := boundary
        subst cr
        simp [Frame.fill, region, Pointer.Lazy.Skeleton.size]
    change (plug fs (f.fill t)).potential - (plug fs (f.fill s)).potential = _
    rw [plug_potential fs _ _ sizes]
    cases f with
    | left r cl cr =>
      have h : cl = true := boundary
      subst cl
      exact replace_marked_left s t r cr
    | right l cr cl =>
      have h : cr = true := boundary
      subst cr
      exact replace_marked_right l s t cl

/-- Every local rotation remains one full-BST rotation at arbitrary depth. -/
theorem plug_rotations (fs : List Frame) {s t : MarkedTree} {cost : Nat}
    (rotations : Rotations s.tree t.tree cost) : Rotations (plug fs s).tree (plug fs t).tree cost := by
  induction fs generalizing s t with
  | nil => exact rotations
  | cons f fs ih =>
    apply ih
    cases f with
    | left r cl cr => exact rotations.inLeft
    | right l cr cl => exact rotations.inRight

theorem plug_nesting (fs : List Frame) {s t : MarkedTree} (same : s.nesting = t.nesting) :
    (plug fs s).nesting = (plug fs t).nesting := by
  induction fs generalizing s t with
  | nil => exact same
  | cons f fs ih =>
    apply ih
    cases f <;> simp [Frame.fill, nesting, same]

end RotationBST.Tango.Context
