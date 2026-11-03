module

public import RotationBST.Models.Pointer.Lazy.Components

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {ops : List (α × α)} {a b r : α} {s t : LabelledTree α}

theorem Connected.invariant (h : Connected ops a b) (P : α → Prop)
    (edges : ∀ e ∈ ops, P e.1 ↔ P e.2) : P a ↔ P b := by
  induction h with
  | refl => rfl
  | edge h => exact edges _ h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Connected.support (h : Connected ops a b) :
    a = b ∨ (a ∈ endpointSupport ops ∧ b ∈ endpointSupport ops) := by
  induction h with
  | refl => exact Or.inl rfl
  | @edge x y he =>
      right
      constructor
      · exact List.mem_flatMap.mpr ⟨(x, y), he, by simp⟩
      · exact List.mem_flatMap.mpr ⟨(x, y), he, by simp⟩
  | symm _ ih =>
      rcases ih with he | hh
      · exact Or.inl he.symm
      · exact Or.inr ⟨hh.2, hh.1⟩
  | trans _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | h₁
      · exact ih₂
      · rcases ih₂ with rfl | h₂
        · exact Or.inr h₁
        · exact Or.inr ⟨h₁.1, h₂.2⟩

theorem endpointSupport_length (ops : List (α × α)) : (endpointSupport ops).length = 2 * ops.length := by
  induction ops with
  | nil => rfl
  | cons e es ih =>
      simp only [endpointSupport, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at *
      omega

/-- Ghost coloring by the rotation graph component of the initial root. -/
noncomputable def rootColor (ops : List (α × α)) (root x : α) : Bool := by
  classical
  exact decide (Connected ops root x)

theorem rootColor_spec (ops : List (α × α)) (root x : α) :
    rootColor ops root x = true ↔ Connected ops root x := by
  classical
  simp [rootColor]

theorem rootColor_self (ops : List (α × α)) (root : α) : rootColor ops root root = true :=
  (rootColor_spec ops root root).mpr .refl

theorem rootColor_uniform (ops : List (α × α)) (root : α) :
    ∀ e ∈ ops, rootColor ops root e.1 = rootColor ops root e.2 := by
  intro e he
  have hi : Connected ops root e.1 ↔ Connected ops root e.2 := by
    constructor
    · exact fun h => .trans h (.edge he)
    · exact fun h => .trans h (.symm (.edge he))
  classical
  simp only [rootColor, hi]

/-- Every key in the root's rotation-graph component already lies in a connected
rooted region of the initial tree. Uniform rotations preserve that region. -/
theorem rootColor_connected (h : Trace s ops t) (distinct : s.inorder.Nodup)
    (source : rootKey? s = some r) :
    ∀ x, rootColor ops r x = true → x ∈ componentKeys (rootColor ops r) true s := by
  have edges := h.component_pairs (rootColor ops r) true (rootColor_uniform ops r) distinct
  have hr := component_root_mem (rootColor ops r) s r source (rootColor_self ops r)
  intro x hx
  have hc := (rootColor_spec ops r x).mp hx
  exact (hc.invariant (fun y => y ∈ componentKeys (rootColor ops r) true s) edges).mp hr

/-- The active region contains at most one initial root plus two endpoints per
selected rotation. Deferred rotations do not enter this charge. -/
theorem rootColor_size (ops : List (α × α)) (root : α) (s : LabelledTree α)
    (distinct : s.inorder.Nodup) :
    (componentKeys (rootColor ops root) true s).length ≤
      2 * (ops.filter fun e => rootColor ops root e.1).length + 1 := by
  let color := rootColor ops root
  have hsub : componentKeys color true s ⊆ root :: endpointSupport (ops.filter fun e => color e.1) := by
    intro x hx
    have hc := componentKeys_color color true s x hx
    have hconn := (rootColor_spec ops root x).mp hc
    rcases hconn.support with heq | hs
    · exact List.mem_cons.mpr (Or.inl heq.symm)
    · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hs.2
      have hec : color e.1 = true := by
        have hu := rootColor_uniform ops root e he
        rcases List.mem_cons.mp hx with hx | hx
        · simpa only [hx] using hc
        · have hx := List.mem_singleton.mp hx
          change rootColor ops root e.1 = true
          rw [hu]
          simpa only [hx] using hc
      exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨e, List.mem_filter.mpr ⟨he, hec⟩, hx⟩))
  have hn := (componentKeys_sublist color true s).nodup distinct
  have hlen := hn.length_le_of_subset hsub
  rw [List.length_cons, endpointSupport_length] at hlen
  exact hlen

end RotationBST.Pointer.Lazy
