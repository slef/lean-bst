module

public import RotationBST.Tango.Preferences.Updates.Counts

@[expose] public section
namespace RotationBST.Tango

theorem preferenceUpdates_changed (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    ∀ e ∈ preferenceUpdates t lo past x, e.previous ≠ some e.next := by
  induction t generalizing lo past x with
  | nil => simp [preferenceUpdates]
  | node l r il ir =>
    simp only [preferenceUpdates]
    split
    · intro e he
      rcases List.mem_append.mp he with he | he
      · split at he
        · simp at he
        · rename_i different
          have eq := List.mem_singleton.mp he
          subst e
          exact different
      · split at he
        · exact il _ _ _ e he
        · split at he
          · simp at he
          · exact ir _ _ _ e he
    · simp

theorem preferenceUpdates_bounds (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    ∀ e ∈ preferenceUpdates t lo past x, lo ≤ e.key ∧ e.key < lo + t.size := by
  induction t generalizing lo past x with
  | nil => simp [preferenceUpdates]
  | node l r il ir =>
    simp only [preferenceUpdates]
    split
    · intro e he
      rcases List.mem_append.mp he with he | he
      · split at he
        · simp at he
        · have eq := List.mem_singleton.mp he
          subst e
          simp only [Tree.size]; omega
      · split at he
        · have h := il _ _ _ e he
          simp only [Tree.size]; omega
        · split at he
          · simp at he
          · have h := ir _ _ _ e he
            simp only [Tree.size]; omega
    · simp

/-- A request changes each reference node at most once. -/
theorem preferenceUpdates_nodup (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    ((preferenceUpdates t lo past x).map PreferenceUpdate.key).Nodup := by
  induction t generalizing lo past x with
  | nil => simp [preferenceUpdates]
  | node l r il ir =>
    simp only [preferenceUpdates]
    split
    · split
      · simp only [List.nil_append]
        split
        · exact il _ _ _
        · split
          · simp
          · exact ir _ _ _
      · simp only [List.singleton_append, List.map_cons, List.nodup_cons]
        split
        · constructor
          · intro h
            obtain ⟨e, he, key⟩ := List.mem_map.mp h
            have hb := preferenceUpdates_bounds l lo (leftRequests l.size past) x e he
            omega
          · exact il _ _ _
        · split
          · simp
          · constructor
            · intro h
              obtain ⟨e, he, key⟩ := List.mem_map.mp h
              have hb := preferenceUpdates_bounds r (lo + l.size + 1)
                (rightRequests l.size past) (x - l.size - 1) e he
              omega
            · exact ir _ _ _
    · simp

end RotationBST.Tango
