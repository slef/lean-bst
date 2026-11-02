module

public import RotationBST.Pointer.Lazy.Components.Abstract
public import RotationBST.Pointer.Lazy.Postpone
public import RotationBST.Representation.ArbitraryKeys
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {x y : α} {s t : LabelledTree α} {ops : List (α × α)}

theorem componentKeys_sublist (color : α → Bool) (wanted : Bool) (t : LabelledTree α) :
    List.Sublist (componentKeys color wanted t) t.inorder := by
  induction t with
  | nil => exact .refl _
  | node l x r il ir =>
      simp only [componentKeys, LabelledTree.inorder]
      split
      · exact il.append (.cons_cons _ ir)
      · exact List.nil_sublist _

theorem RotateAt.component_eq (color : α → Bool) (wanted : Bool) (h : RotateAt x y s t)
    (uniform : color x = color y) : componentKeys color wanted s = componentKeys color wanted t := by
  induction h with
  | @right a b c x y =>
      by_cases hc : color x = wanted <;> simp [componentKeys, ← uniform, hc, List.append_assoc]
  | @left a b c x y =>
      by_cases hc : color x = wanted <;> simp [componentKeys, ← uniform, hc, List.append_assoc]
  | inLeft _ ih => simp only [componentKeys, ih uniform]
  | inRight _ ih => simp only [componentKeys, ih uniform]

theorem RotateAt.keys (h : RotateAt x y s t) : x ∈ s.inorder ∧ y ∈ s.inorder := by
  induction h with
  | @right a b c x y => simp [LabelledTree.inorder]
  | @left a b c x y => simp [LabelledTree.inorder]
  | inLeft _ ih =>
      simp only [LabelledTree.inorder, List.mem_append, List.mem_cons]
      exact ⟨Or.inl ih.1, Or.inl ih.2⟩
  | inRight _ ih =>
      simp only [LabelledTree.inorder, List.mem_append, List.mem_cons]
      exact ⟨Or.inr (Or.inr ih.1), Or.inr (Or.inr ih.2)⟩

/-- For a distinct labelling, adjacent same-colored endpoints either both
belong to the root component or both lie outside it. -/
theorem RotateAt.component_membership (color : α → Bool) (wanted : Bool)
    (h : RotateAt x y s t) (uniform : color x = color y) (distinct : s.inorder.Nodup) :
    x ∈ componentKeys color wanted s ↔ y ∈ componentKeys color wanted s := by
  induction h with
  | @right a b c x y =>
      by_cases hc : color x = wanted <;> simp [componentKeys, ← uniform, hc]
  | @left a b c x y =>
      by_cases hc : color x = wanted <;> simp [componentKeys, ← uniform, hc]
  | @inLeft a b c x y z h ih =>
      have hd := List.nodup_append.mp distinct
      have hx := h.keys.1
      have hy := h.keys.2
      have hxout : x ∉ z :: componentKeys color wanted c := by
        intro hh
        exact hd.2.2 x hx x ((List.Sublist.cons_cons z (componentKeys_sublist color wanted c)).subset hh) rfl
      have hyout : y ∉ z :: componentKeys color wanted c := by
        intro hh
        exact hd.2.2 y hy y ((List.Sublist.cons_cons z (componentKeys_sublist color wanted c)).subset hh) rfl
      by_cases hz : color z = wanted
      · simpa only [componentKeys, ite_eq_left hz, List.mem_append, hxout, hyout, or_false]
          using ih uniform hd.1
      · simp only [componentKeys, ite_eq_right hz, List.not_mem_nil]
  | @inRight a b c x y z h ih =>
      have hd := List.nodup_append.mp distinct
      have hn := List.nodup_cons.mp hd.2.1
      have hx := h.keys.1
      have hy := h.keys.2
      have hxout : x ∉ componentKeys color wanted c := by
        intro hh
        exact hd.2.2 x ((componentKeys_sublist color wanted c).subset hh) x (by simp [hx]) rfl
      have hyout : y ∉ componentKeys color wanted c := by
        intro hh
        exact hd.2.2 y ((componentKeys_sublist color wanted c).subset hh) y (by simp [hy]) rfl
      have hxz : x ≠ z := by intro hh; subst x; exact hn.1 hx
      have hyz : y ≠ z := by intro hh; subst y; exact hn.1 hy
      by_cases hz : color z = wanted
      · simpa only [componentKeys, ite_eq_left hz, List.mem_append, List.mem_cons,
          hxout, hyout, hxz, hyz, false_or] using ih uniform hn.2
      · simp only [componentKeys, ite_eq_right hz, List.not_mem_nil]

theorem Trace.component_eq (color : α → Bool) (wanted : Bool) (h : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2) :
    componentKeys color wanted s = componentKeys color wanted t := by
  induction h with
  | nil => rfl
  | @cons x y s v t es h ht ih =>
      exact (h.component_eq color wanted (uniform (x, y) (by simp))).trans
        (ih (by intro e he; exact uniform e (by simp [he])))

theorem Trace.component_pairs (color : α → Bool) (wanted : Bool) (h : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2) (distinct : s.inorder.Nodup) :
    ∀ e ∈ ops, e.1 ∈ componentKeys color wanted s ↔ e.2 ∈ componentKeys color wanted s := by
  induction h with
  | nil => simp
  | @cons x y s v t es h ht ih =>
      have hu := uniform (x, y) (by simp)
      have hv : v.inorder.Nodup := by
        rw [← Representation.Bridge.inorder_rotate h.forget]
        exact distinct
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e; exact h.component_membership color wanted hu distinct
      · rw [h.component_eq color wanted hu]
        exact ih (by intro e he; exact uniform e (by simp [he])) hv e he

theorem RotateAt.root_color (color : α → Bool) (h : RotateAt x y s t)
    (uniform : color x = color y) :
    (rootKey? s).map color = (rootKey? t).map color := by
  cases h <;> simp [rootKey?, uniform]

theorem Trace.root_color (color : α → Bool) (h : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2) :
    (rootKey? s).map color = (rootKey? t).map color := by
  induction h with
  | nil => rfl
  | @cons x y s v t es h ht ih =>
      exact (h.root_color color (uniform (x, y) (by simp))).trans
        (ih (by intro e he; exact uniform e (by simp [he])))

theorem component_root_mem (color : α → Bool) (t : LabelledTree α) (x : α)
    (root : rootKey? t = some x) (selected : color x = true) : x ∈ componentKeys color true t := by
  cases t with
  | nil => simp [rootKey?] at root
  | node l y r =>
      have hy : y = x := Option.some.inj root
      subst y
      simp [componentKeys, selected]

theorem componentKeys_color (color : α → Bool) (wanted : Bool) (t : LabelledTree α) :
    ∀ x ∈ componentKeys color wanted t, color x = wanted := by
  induction t with
  | nil => simp [componentKeys]
  | node l y r il ir =>
      intro x hx
      unfold componentKeys at hx
      split at hx
      next hy =>
        rcases List.mem_append.mp hx with hx | hx
        · exact il x hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hy
          · exact ir x hx
      next => simp at hx

end RotationBST.Pointer.Lazy
