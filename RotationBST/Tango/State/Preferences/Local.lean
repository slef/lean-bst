module

public import RotationBST.Tango.State.Preferences.Sequence

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Apply absolute log keys within a subtree whose first key has offset `lo`. -/
def applyFrom : MarkedTree → Nat → List PreferenceUpdate → MarkedTree
  | s, _, [] => s
  | s, lo, update :: rest => applyFrom (s.setPreference (update.key - lo) update.next) lo rest

@[simp] theorem applyFrom_zero (s : MarkedTree) (updates : List PreferenceUpdate) :
    s.applyFrom 0 updates = s.applyPreferences updates := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih => simp only [applyFrom, applyPreferences, Nat.sub_zero, ih]

@[simp] theorem applyFrom_tree (s : MarkedTree) (lo : Nat) (updates : List PreferenceUpdate) :
    (s.applyFrom lo updates).tree = s.tree := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih => simp only [applyFrom, ih, setPreference_tree]

theorem applyFrom_append (s : MarkedTree) (lo : Nat) (xs ys : List PreferenceUpdate) :
    s.applyFrom lo (xs ++ ys) = (s.applyFrom lo xs).applyFrom lo ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons u us ih => exact ih _

theorem applyFrom_left (l r : MarkedTree) (cl cr : Bool) (lo : Nat) (updates : List PreferenceUpdate)
    (bounds : ∀ e ∈ updates, lo ≤ e.key ∧ e.key < lo + l.tree.size) :
    (MarkedTree.node l r cl cr).applyFrom lo updates = .node (l.applyFrom lo updates) r cl cr := by
  induction updates generalizing l with
  | nil => rfl
  | cons u us ih =>
    have hb := bounds u (List.mem_cons_self ..)
    have left : u.key - lo < l.tree.size := by omega
    simp only [applyFrom, setPreference, ite_eq_left left]
    apply ih
    intro e he
    simpa only [setPreference_tree] using bounds e (List.mem_cons_of_mem _ he)

theorem applyFrom_right (l r : MarkedTree) (cl cr : Bool) (lo : Nat) (updates : List PreferenceUpdate)
    (bounds : ∀ e ∈ updates, lo + l.tree.size + 1 ≤ e.key) :
    (MarkedTree.node l r cl cr).applyFrom lo updates =
      .node l (r.applyFrom (lo + l.tree.size + 1) updates) cl cr := by
  induction updates generalizing r with
  | nil => rfl
  | cons u us ih =>
    have hb := bounds u (List.mem_cons_self ..)
    have left : ¬ u.key - lo < l.tree.size := by omega
    have root : u.key - lo ≠ l.tree.size := by omega
    have shift : u.key - lo - l.tree.size - 1 = u.key - (lo + l.tree.size + 1) := by omega
    simp only [applyFrom, setPreference, ite_eq_right left, ite_eq_right root, shift]
    apply ih
    exact fun e he => bounds e (List.mem_cons_of_mem _ he)

end RotationBST.Tango.MarkedTree
