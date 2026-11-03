module

public import RotationBST.Models.Pointer.Lazy.Partition

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {x y r : α} {s t : LabelledTree α} {ops : List (α × α)}

/-- A rotation can change a specified root key only if that key is an endpoint. -/
theorem RotateAt.root_iff (h : RotateAt x y s t) (hne : r ≠ x ∧ r ≠ y) :
    rootKey? s = some r ↔ rootKey? t = some r := by
  cases h <;> simp_all [rootKey?, ne_comm]

theorem Trace.root_iff (h : Trace s ops t) (hne : ∀ e ∈ ops, r ≠ e.1 ∧ r ≠ e.2) :
    rootKey? s = some r ↔ rootKey? t = some r := by
  induction h with
  | nil => rfl
  | @cons x y s v t es h ht ih =>
      exact (h.root_iff (hne (x, y) (by simp))).trans
        (ih (by intro e he; exact hne e (by simp [he])))

theorem Trace.access (h : Trace s ops t) (root : rootKey? t = some x) :
    LabelledTree.Access s t x ops.length := by
  refine ⟨h.forget, ?_⟩
  cases t with
  | nil => simp [rootKey?] at root
  | node l y r => exact Option.some.inj root

theorem partition_length (color : α → Bool) (ops : List (α × α)) :
    (ops.filter fun e => color e.1).length +
      (ops.filter fun e => !(color e.1)).length = ops.length := by
  induction ops with
  | nil => rfl
  | cons e es ih =>
      cases hc : color e.1 <;> simp only [List.filter_cons, hc, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ite_true, ite_false, List.length_cons] <;> omega

theorem unselected_excludes (color : α → Bool) (ops : List (α × α))
    (uniform : ∀ e ∈ ops, color e.1 = color e.2) (selected : color x = true) :
    ∀ e ∈ ops.filter (fun e => !(color e.1)), x ≠ e.1 ∧ x ≠ e.2 := by
  intro e he
  obtain ⟨he, hc⟩ := List.mem_filter.mp he
  have hu := uniform e he
  constructor
  · intro hx
    have hh := congrArg color hx
    simp_all
  · intro hx
    have hh := congrArg color hx
    simp_all

/-- An access can postpone every independent color class not containing its
requested key. The selected prefix still serves that key at its root, the exact
final tree is recovered by the deferred suffix, and no rotations are added. -/
theorem postpone_access (color : α → Bool) (h : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2)
    (root : rootKey? t = some x) (selected : color x = true) :
    ∃ q, LabelledTree.Access s q x (ops.filter fun e => color e.1).length ∧
      Trace q (ops.filter fun e => !(color e.1)) t ∧
      (ops.filter fun e => color e.1).length +
        (ops.filter fun e => !(color e.1)).length = ops.length := by
  obtain ⟨q, hselected, hother⟩ := partition_trace color h uniform
  have hne := unselected_excludes color ops uniform selected
  exact ⟨q, hselected.access ((hother.root_iff hne).mpr root), hother, partition_length color ops⟩

end RotationBST.Pointer.Lazy
