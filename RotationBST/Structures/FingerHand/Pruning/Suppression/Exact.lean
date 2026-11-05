module

public import RotationBST.Structures.FingerHand.Pruning.Suppression.Shape

@[expose] public section
namespace RotationBST.FingerHand

/-- The old key can be removed without further cleanup in these local shapes.
Distinct labels ensure the deleted mark is absent from all untouched regions. -/
theorem Suppress.reduced {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) (distinct : s.inorder.Nodup) (normal : Reduced (insert x marks) s) :
    Reduced marks t := by
  induction h with
  | unaryLeft ne =>
    obtain ⟨_, _, absent, _, _⟩ := node_distinct distinct
    exact normal.1.without absent
  | unaryRight ne =>
    obtain ⟨_, _, _, absent, _⟩ := node_distinct distinct
    exact normal.2.1.without absent
  | leafLeft marked =>
    obtain ⟨_, _, _, _, apart⟩ := node_distinct distinct
    have absent := apart x (by simp [LabelledTree.inorder])
    exact ⟨trivial, normal.2.1.without absent, Or.inl marked⟩
  | leafRight marked =>
    obtain ⟨_, _, _, _, apart⟩ := node_distinct distinct
    have absent : x ∉ _ := fun hx => apart x hx (by simp [LabelledTree.inorder])
    exact ⟨normal.1.without absent, trivial, Or.inl marked⟩
  | @inLeft a b r y h ih =>
    obtain ⟨dl, _, yl, _, apart⟩ := node_distinct distinct
    have absent := apart x h.contains
    have different : y ≠ x := by intro eq; subst y; exact yl h.contains
    refine ⟨ih dl normal.1, normal.2.1.without absent, ?_⟩
    rcases normal.2.2 with marked | branch
    · exact Or.inl ((Finset.mem_insert.mp marked).resolve_left different)
    · exact Or.inr ⟨h.nonempty.2, branch.2⟩
  | @inRight a b l y h ih =>
    obtain ⟨_, dr, _, yr, apart⟩ := node_distinct distinct
    have absent : x ∉ l.inorder := fun hx => apart x hx h.contains
    have different : y ≠ x := by intro eq; subst y; exact yr h.contains
    refine ⟨normal.1.without absent, ih dr normal.2.1, ?_⟩
    rcases normal.2.2 with marked | branch
    · exact Or.inl ((Finset.mem_insert.mp marked).resolve_left different)
    · exact Or.inr ⟨branch.1, h.nonempty.2⟩

/-- Suppression is exactly pruning away the obsolete mark, rather than merely
producing a smaller skeleton containing the remaining terminals. -/
theorem Suppress.prune_eq {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) (unmarked : x ∉ marks) (distinct : s.inorder.Nodup)
    (normal : Reduced (insert x marks) s) : prune marks s = t := by
  have projected := h.contracts.project marks distinct (by
    intro y hy hm
    exact h.other_keys y hy (fun eq => unmarked (eq ▸ hm)))
  exact projected.symm.trans (h.reduced distinct normal).fixed

end RotationBST.FingerHand
