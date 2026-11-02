module

public import RotationBST.Tango.State.Nesting.Keys

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem fringe_size_le (s : MarkedTree) : ∀ child ∈ s.fringe, child.tree.size ≤ s.tree.size := by
  induction s with
  | nil =>
    intro child member
    have h : child = .nil := by simpa [fringe] using member
    subst child
    exact Nat.le_refl _
  | node l r cl cr il ir =>
    intro child member
    change child ∈ (if cl then [l] else l.fringe) ++ (if cr then [r] else r.fringe) at member
    rcases List.mem_append.mp member with member | member
    · have h : child.tree.size ≤ l.tree.size := by
        cases cl
        · exact il child member
        · have h := List.mem_singleton.mp member; subst child; exact Nat.le_refl _
      simp only [tree, Tree.size]; omega
    · have h : child.tree.size ≤ r.tree.size := by
        cases cr
        · exact ir child member
        · have h := List.mem_singleton.mp member; subst child; exact Nat.le_refl _
      simp only [tree, Tree.size]; omega

theorem fringe_size_lt (s : MarkedTree) (nonempty : s ≠ .nil) (child : MarkedTree)
    (member : child ∈ s.fringe) : child.tree.size < s.tree.size := by
  cases s with
  | nil => contradiction
  | node l r cl cr =>
    change child ∈ (if cl then [l] else l.fringe) ++ (if cr then [r] else r.fringe) at member
    rcases List.mem_append.mp member with member | member
    · have h : child.tree.size ≤ l.tree.size := by
        cases cl
        · exact fringe_size_le l child member
        · have h := List.mem_singleton.mp member; subst child; exact Nat.le_refl _
      simp only [tree, Tree.size]; omega
    · have h : child.tree.size ≤ r.tree.size := by
        cases cr
        · exact fringe_size_le r child member
        · have h := List.mem_singleton.mp member; subst child; exact Nat.le_refl _
      simp only [tree, Tree.size]; omega

private theorem matching_flatMap {α β γ : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (matching : List.Forall₂ R xs ys) (f : α → List γ) (g : β → List γ)
    (equal : ∀ a ∈ xs, ∀ b ∈ ys, R a b → f a = g b) : xs.flatMap f = ys.flatMap g := by
  induction matching with
  | nil => rfl
  | @cons a b xs ys h hs ih =>
    simp only [List.flatMap_cons]
    rw [equal a (List.mem_cons_self ..) b (List.mem_cons_self ..) h]
    rw [ih (fun a ha b hb hab => equal a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)]

/-- Equal nesting determines every component's absolute key set, in the same
fringe order, not just the root component or the total universe size. -/
theorem nesting_components_eq (s t : MarkedTree) (same : s.nesting = t.nesting) (lo : Nat) :
    ((s.components lo).map fun p => p.2.keys p.1) = ((t.components lo).map fun p => p.2.keys p.1) := by
  cases s with
  | nil =>
    cases t with
    | nil => rfl
    | node a b ca cb => cases same
  | node l r cl cr =>
    cases t with
    | nil => cases same
    | node a b ca cb =>
      have root := nesting_keys_eq same lo
      simp only [components, rootComponent, List.singleton_append, List.map_cons]
      rw [root]
      congr 1
      rw [detached_fringeAt, detached_fringeAt, List.map_flatMap, List.map_flatMap]
      apply matching_flatMap (fringeAt_matching same lo)
      intro p hp q hq related
      have member : p.2 ∈ (MarkedTree.node l r cl cr).fringe := by
        rw [← fringeAt_snd (.node l r cl cr) lo]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      have smaller := fringe_size_lt (.node l r cl cr) (by simp) p.2 member
      have childResult := nesting_components_eq p.2 q.2 related.2 p.1
      simpa only [related.1] using childResult
termination_by s.tree.size

theorem represents_of_nesting {s t : MarkedTree} {reference : Tree} {past : List Nat}
    (represented : Represents s reference past) (same : s.nesting = t.nesting) : Represents t reference past := by
  exact ⟨(nesting_size_eq same).symm.trans represented.1,
    nesting_components_eq s t same 0 ▸ represented.2.1,
    (nesting_keys_eq same 0).symm.trans represented.2.2⟩

/-- The full maintenance invariant can be established from nesting alone. -/
theorem maintains_of_nesting (s : MarkedTree) (reference : Tree) (past : List Nat)
    (same : s.nesting = (canonical reference 0 past).nesting) : Maintains s reference past :=
  ⟨represents_of_nesting (canonical_represents reference past) same.symm, same⟩

end RotationBST.Tango.MarkedTree
