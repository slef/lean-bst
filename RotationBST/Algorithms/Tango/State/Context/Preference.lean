module

public import RotationBST.Algorithms.Tango.State.Preferences.Order
public import RotationBST.Algorithms.Tango.State.Context.Position
public import RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- The context's inorder displacement is independent of the base address. -/
theorem offset_add (fs : List Frame) (lo : Nat) : offset fs lo = offset fs 0 + lo := by
  induction fs with
  | nil => simp [offset]
  | cons f fs ih => cases f <;> simp [offset, Frame.offset, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every key in the focused subtree remains valid at its absolute rank. -/
theorem key_in_plug (fs : List Frame) (s : MarkedTree) (key : Nat) (valid : key < s.tree.size) :
    offset fs 0 + key < (plug fs s).tree.size := by
  induction fs generalizing s key with
  | nil => simpa only [offset, plug, Nat.zero_add] using valid
  | cons f fs ih =>
    cases f with
    | left r cl cr =>
      simpa only [plug, Frame.fill, offset, Frame.offset] using
        ih (.node s r cl cr) key (by simp only [tree, Tree.size]; omega)
    | right l cr cl =>
      have bound := ih (.node l s cl cr) (l.tree.size + 1 + key) (by simp only [tree, Tree.size]; omega)
      simpa only [plug, Frame.fill, offset, Frame.offset, Nat.add_assoc] using bound

/-- Looking up an internal rank retains the exact enclosing ancestor frames. -/
theorem locateKey_plug (fs : List Frame) (s : MarkedTree) (key : Nat) (valid : key < s.tree.size) :
    (plug fs s).locateKey (offset fs 0 + key) =
      (s.locateKey key).map (fun p => (p.1, p.2 ++ fs)) := by
  induction fs generalizing s key with
  | nil => simp [plug, offset]
  | cons f fs ih =>
    cases f with
    | left r cl cr =>
      have bound : key < (MarkedTree.node s r cl cr).tree.size := by simp only [tree, Tree.size]; omega
      have found := ih (.node s r cl cr) key bound
      simpa [plug, Frame.fill, offset, Frame.offset, locateKey, valid, Option.map_map, Function.comp_def, List.append_assoc] using found
    | right l cr cl =>
      have bound : l.tree.size + 1 + key < (MarkedTree.node l s cl cr).tree.size := by
        simp only [tree, Tree.size]; omega
      have found := ih (.node l s cl cr) (l.tree.size + 1 + key) bound
      have left : ¬ l.tree.size + 1 + key < l.tree.size := by omega
      have root : ¬ l.tree.size + 1 + key = l.tree.size := by omega
      have sub : l.tree.size + 1 + key - l.tree.size - 1 = key := by omega
      simpa [plug, Frame.fill, offset, Frame.offset, locateKey, left, root, sub,
        Option.map_map, Function.comp_def, List.append_assoc, Nat.add_assoc] using found

/-- A preference assignment inside a subtree changes no enclosing frame. -/
theorem setPreference_plug (fs : List Frame) (s : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < s.tree.size) :
    (plug fs s).setPreference (offset fs 0 + key) next = plug fs (s.setPreference key next) := by
  induction fs generalizing s key with
  | nil => simp [plug, offset]
  | cons f fs ih =>
    cases f with
    | left r cl cr =>
      have computed := ih (.node s r cl cr) key (by simp only [tree, Tree.size]; omega)
      simpa [plug, Frame.fill, offset, Frame.offset, setPreference, valid] using computed
    | right l cr cl =>
      have computed := ih (.node l s cl cr) (l.tree.size + 1 + key) (by simp only [tree, Tree.size]; omega)
      have left : ¬ l.tree.size + 1 + key < l.tree.size := by omega
      have root : ¬ l.tree.size + 1 + key = l.tree.size := by omega
      have sub : l.tree.size + 1 + key - l.tree.size - 1 = key := by omega
      simpa [plug, Frame.fill, offset, Frame.offset, setPreference, left, root, sub, Nat.add_assoc] using computed

/-- Whole-tree execution of an in-subtree log agrees with its local execution,
including the exact unchanged surrounding context. -/
theorem applyPreferences_plug (fs : List Frame) (s : MarkedTree) (updates : List PreferenceUpdate)
    (valid : ∀ u ∈ updates, offset fs 0 ≤ u.key ∧ u.key < offset fs 0 + s.tree.size) :
    (plug fs s).applyPreferences updates = plug fs (s.applyFrom (offset fs 0) updates) := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih =>
    have first := valid u (by simp)
    have key : u.key - offset fs 0 < s.tree.size := by omega
    have eq : u.key = offset fs 0 + (u.key - offset fs 0) := by omega
    simp only [applyPreferences, applyFrom]
    rw [eq, setPreference_plug fs s _ u.next key]
    rw [← eq]
    exact ih _ (by intro v member; simpa only [setPreference_tree] using valid v (by simp [member]))

/-- Reference-local subtree height is unaffected by embedding or address shift. -/
theorem heightAt_plug (fs : List Frame) (s : MarkedTree) (key : Nat) (valid : key < s.tree.size) :
    Initialization.heightAt (plug fs s).tree (offset fs 0 + key) = Initialization.heightAt s.tree key := by
  induction fs generalizing s key with
  | nil => simp [plug, offset]
  | cons f fs ih =>
    cases f with
    | left r cl cr =>
      have value := ih (.node s r cl cr) key (by simp only [tree, Tree.size]; omega)
      simpa [plug, Frame.fill, offset, Frame.offset, tree, Initialization.heightAt, valid] using value
    | right l cr cl =>
      have value := ih (.node l s cl cr) (l.tree.size + 1 + key) (by simp only [tree, Tree.size]; omega)
      have left : ¬ l.tree.size + 1 + key < l.tree.size := by omega
      have root : ¬ l.tree.size + 1 + key = l.tree.size := by omega
      have sub : l.tree.size + 1 + key - l.tree.size - 1 = key := by omega
      simpa [plug, Frame.fill, offset, Frame.offset, tree, Initialization.heightAt, left, root, sub, Nat.add_assoc] using value

end RotationBST.Tango.Context
