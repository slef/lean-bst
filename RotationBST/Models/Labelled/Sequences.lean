module

public import RotationBST.Models.Labelled.ArbitraryAccess

@[expose] public section

namespace RotationBST.Representation.Bridge

variable {α : Type}

private theorem execution_nil {a b : Tree} {k : Nat} (h : Execution a [] b k) : a = b ∧ k = 0 := by
  cases h
  exact ⟨rfl, rfl⟩

theorem access_on_keys_iff (keys : List α) (distinct : keys.Nodup)
    (s t : LabelledTree α) (hs : s.inorder = keys) (ht : t.inorder = keys)
    (x : Fin keys.length) (k : Nat) :
    Access s.erase t.erase x.val k ↔ LabelledTree.Access s t (keys.get x) k := by
  have hd : s.inorder.Nodup := hs ▸ distinct
  have hx : x.val < s.inorder.length := by rw [hs]; exact x.isLt
  simpa [hs] using arbitrary_access_iff s t (hs.trans ht.symm) hd x.val k hx

/-- Entire search sequences correspond for any fixed distinct key list, with
exactly the same total rotation count and specified final labelled tree. -/
theorem execution_on_keys_iff (keys : List α) (distinct : keys.Nodup)
    (xs : List (Fin keys.length)) (s t : LabelledTree α)
    (hs : s.inorder = keys) (ht : t.inorder = keys) (k : Nat) :
    Execution s.erase (xs.map Fin.val) t.erase k ↔
      LabelledTree.Execution s (xs.map keys.get) t k := by
  induction xs generalizing s t k with
  | nil =>
      constructor
      · intro h
        obtain ⟨he, hk⟩ := execution_nil h
        subst k
        have he := ext s t he (hs.trans ht.symm)
        subst t
        exact .nil
      · intro h; cases h; exact .nil
  | cons x xs ih =>
      constructor
      · intro h
        cases h with
        | @cons _ u _ a _ _ b ha hb =>
            have hlen : keys.length = u.size := by
              rw [← hs, inorder_length]
              exact ha.1.size_eq
            obtain ⟨v, hv, hkeys⟩ := labels_exist u keys hlen
            have hlabel : LabelledTree.Access s v (keys.get x) a := by
              apply (access_on_keys_iff keys distinct s v hs hkeys x a).mp
              simpa only [hv] using ha
            have htail : LabelledTree.Execution v (xs.map keys.get) t b := by
              apply (ih v t hkeys ht b).mp
              simpa only [hv] using hb
            exact .cons hlabel htail
      · intro h
        cases h with
        | @cons _ v _ a _ _ b ha hb =>
            have hkeys : v.inorder = keys := (inorder_rotations ha.1).symm.trans hs
            have hshape := (access_on_keys_iff keys distinct s v hs hkeys x a).mpr ha
            exact .cons hshape ((ih v t hkeys ht b).mpr hb)

end RotationBST.Representation.Bridge
