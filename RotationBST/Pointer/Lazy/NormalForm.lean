module

public import RotationBST.Pointer.Lazy.RootComponent

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {α : Type} {r x : α} {s t : LabelledTree α} {ops : List (α × α)}

/-- A root-access program has a normal form consisting of rotations in a small
connected region at the initial root, followed by deferred independent rotations.
The region has at most two endpoints per executed rotation plus the initial root.
This theorem supplies the combinatorial normal form; `Skeleton.reshape`
supplies the linear pointer-navigation bound used by `Simulation`. -/
theorem rooted_normal_form (h : Trace s ops t) (distinct : s.inorder.Nodup)
    (source : rootKey? s = some r) (target : rootKey? t = some x) :
    ∃ (color : α → Bool) (q : LabelledTree α),
      (∀ e ∈ ops, color e.1 = color e.2) ∧ color r = true ∧
      (∀ y, color y = true → y ∈ componentKeys color true s) ∧
      (componentKeys color true s).length ≤ 2 * (ops.filter fun e => color e.1).length + 1 ∧
      Trace s (ops.filter fun e => color e.1) q ∧
      LabelledTree.Access s q x (ops.filter fun e => color e.1).length ∧
      Trace q (ops.filter fun e => !(color e.1)) t ∧
      (ops.filter fun e => color e.1).length +
        (ops.filter fun e => !(color e.1)).length = ops.length := by
  let color := rootColor ops r
  have hu := rootColor_uniform ops r
  have hc := h.root_color color hu
  rw [source, target] at hc
  simp only [Option.map_some] at hc
  have hx : color x = true := (Option.some.inj hc).symm.trans (rootColor_self ops r)
  obtain ⟨q, hselected, hother⟩ := partition_trace color h hu
  have hroot := (hother.root_iff (unselected_excludes color ops hu hx)).mpr target
  exact ⟨color, q, hu, rootColor_self ops r, rootColor_connected h distinct source,
    rootColor_size ops r s distinct, hselected, hselected.access hroot, hother,
    partition_length color ops⟩

end RotationBST.Pointer.Lazy
