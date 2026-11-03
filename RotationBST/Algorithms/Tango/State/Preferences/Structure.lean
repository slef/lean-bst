module

public import RotationBST.Algorithms.Tango.State.Preferences.Defs
public import RotationBST.Algorithms.Tango.State.Context.Lifting

@[expose] public section
namespace RotationBST.Tango.MarkedTree

@[simp] theorem setPreference_tree (s : MarkedTree) (key : Nat) (next : Bool) :
    (s.setPreference key next).tree = s.tree := by
  induction s generalizing key with
  | nil => rfl
  | node l r cl cr il ir =>
    simp only [setPreference]
    split
    · simp only [tree, il]
    · split <;> simp only [tree, ir]

theorem setPreference_pathMarked (s : MarkedTree) (key : Nat) (next : Bool)
    (paths : s.PathMarked) : (s.setPreference key next).PathMarked := by
  induction s generalizing key with
  | nil => trivial
  | node l r cl cr il ir =>
    obtain ⟨hl, hr, edge⟩ := paths
    simp only [setPreference]
    split
    · exact ⟨il _ hl, hr, edge⟩
    · split
      · exact ⟨hl, hr, by cases next <;> simp⟩
      · exact ⟨hl, ir _ hr, edge⟩

theorem canonical_pathMarked (t : Tree) (lo : Nat) (past : List Nat) :
    (canonical t lo past).PathMarked := by
  induction t generalizing lo with
  | nil => trivial
  | node l r il ir =>
    simp only [canonical]
    split
    all_goals exact ⟨il _, ir _, by simp⟩

/-- Every auxiliary component in a reference marking is a downward path, even
at intermediate states of a preference update. -/
theorem region_size_le_height (s : MarkedTree) (paths : s.PathMarked) :
    s.region.size ≤ height s.tree := by
  induction s with
  | nil => exact Nat.le_refl _
  | node l r cl cr il ir =>
    obtain ⟨hl, hr, edge⟩ := paths
    have bl := il hl
    have br := ir hr
    cases cl <;> cases cr <;>
      simp_all [region, tree, height, Pointer.Lazy.Skeleton.size]; omega

end RotationBST.Tango.MarkedTree

namespace RotationBST.Tango.Context
open MarkedTree

theorem pathMarked_focus (fs : List Frame) (s : MarkedTree) (paths : (plug fs s).PathMarked) :
    s.PathMarked := by
  induction fs generalizing s with
  | nil => exact paths
  | cons f fs ih =>
    have h := ih (f.fill s) paths
    cases f with
    | left r cl cr => exact h.1
    | right l cr cl => exact h.2.1

theorem height_le_plug (fs : List Frame) (s : MarkedTree) : height s.tree ≤ height (plug fs s).tree := by
  induction fs generalizing s with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    apply Nat.le_trans (m := height (f.fill s).tree) _ (ih _)
    cases f <;> simp only [Frame.fill, tree, height] <;> omega

end RotationBST.Tango.Context
