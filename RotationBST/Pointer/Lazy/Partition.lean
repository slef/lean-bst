module

public import RotationBST.Pointer.Lazy.Commutation

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {x y : α} {s t z : LabelledTree α} {ops : List (α × α)}

theorem Trace.forget (h : Trace s ops t) : LabelledTree.Rotations s t ops.length := by
  induction h with
  | nil => exact .refl
  | cons h _ ih => exact .step h.forget ih

theorem trace_of_rotations {k : Nat} (h : LabelledTree.Rotations s t k) :
    ∃ ops, ops.length = k ∧ Trace s ops t := by
  induction h with
  | refl => exact ⟨[], rfl, .nil⟩
  | step h _ ih =>
      obtain ⟨x, y, hx⟩ := endpoints h
      obtain ⟨ops, hk, ht⟩ := ih
      exact ⟨(x, y) :: ops, by simp [hk], .cons hx ht⟩

/-- Move one rotation past an entire independent block. -/
theorem commute_trace (h : RotateAt x y s t) (g : Trace t ops z)
    (disjoint : ∀ e ∈ ops, DisjointPairs x y e.1 e.2) :
    ∃ q, Trace s ops q ∧ RotateAt x y q z := by
  induction g generalizing s with
  | nil => exact ⟨s, .nil, h⟩
  | @cons a b t v z es hg ht ih =>
      obtain ⟨q, hfirst, hsecond⟩ := commute h hg (disjoint (a, b) (by simp))
      obtain ⟨r, htail, hlast⟩ := ih hsecond (by intro e he; exact disjoint e (by simp [he]))
      exact ⟨r, .cons hfirst htail, hlast⟩

private theorem disjoint_of_colors (color : α → Bool) (x y u v : α)
    (hxy : color x = color y) (huv : color u = color v) (hne : color x ≠ color u) :
    DisjointPairs x y u v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => hne (congrArg color h)
  · exact fun h => hne ((congrArg color h).trans huv.symm)
  · exact fun h => hne (hxy.trans (congrArg color h))
  · exact fun h => hne ((hxy.trans (congrArg color h)).trans huv.symm)

/-- Stable partition of independent rotation components. If every rotation's
endpoints have the same color, all selected rotations can be done first and all
other rotations postponed, preserving the exact final tree and instruction list
within each color. No navigation-cost assertion is hidden here. -/
theorem partition_trace (color : α → Bool) (h : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2) :
    ∃ q, Trace s (ops.filter fun e => color e.1) q ∧
      Trace q (ops.filter fun e => !(color e.1)) t := by
  induction h with
  | nil => exact ⟨_, .nil, .nil⟩
  | @cons x y s v t es h ht ih =>
      obtain ⟨q, hselected, hother⟩ := ih (by intro e he; exact uniform e (by simp [he]))
      cases hc : color x with
      | true =>
          simp only [List.filter_cons, hc, Bool.not_true, Bool.false_eq_true,
            ite_true, ite_false]
          exact ⟨q, .cons h hselected, hother⟩
      | false =>
          have hd : ∀ e ∈ es.filter (fun e => color e.1), DisjointPairs x y e.1 e.2 := by
            intro e he
            obtain ⟨he, hec⟩ := List.mem_filter.mp he
            apply disjoint_of_colors color x y e.1 e.2
              (uniform (x, y) (by simp)) (uniform e (by simp [he]))
            simpa only [hc, hec] using Bool.false_ne_true
          obtain ⟨r, hs, hr⟩ := commute_trace h hselected hd
          simp only [List.filter_cons, hc, Bool.not_false, Bool.false_eq_true,
            ite_true, ite_false]
          exact ⟨r, hs, .cons hr hother⟩

end RotationBST.Pointer.Lazy
