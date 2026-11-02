module

public import RotationBST.Pointer.Lazy.NormalForm
public import RotationBST.Pointer.Lazy.Skeleton

@[expose] public section

namespace RotationBST.Pointer.Lazy

/-- Retain the selected component at the root, treating every other subtree as
one untouched hole. Labels are erased from the resulting region. -/
def project {α : Type} (color : α → Bool) : LabelledTree α → Skeleton
  | .nil => .hole .nil
  | .node l x r => if color x then .node (project color l) (project color r)
      else .hole (.node l.erase r.erase)

theorem project_tree {α : Type} (color : α → Bool) (s : LabelledTree α) :
    (project color s).tree = s.erase := by
  induction s with
  | nil => rfl
  | node l x r il ir => cases h : color x <;> simp [project, h, Skeleton.tree, il, ir, LabelledTree.erase]

theorem project_size {α : Type} (color : α → Bool) (s : LabelledTree α) :
    (project color s).size = (componentKeys color true s).length := by
  induction s with
  | nil => rfl
  | node l x r il ir =>
      cases h : color x <;> simp [project, h, Skeleton.size, componentKeys, il, ir, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

variable {α : Type} {x y : α} {s t : LabelledTree α} {ops : List (α × α)}

theorem RotateAt.project_fringe (color : α → Bool) (h : RotateAt x y s t)
    (hx : color x = true) (hy : color y = true) (distinct : s.inorder.Nodup)
    (active : x ∈ componentKeys color true s) :
    (project color s).fringe = (project color t).fringe := by
  induction h with
  | right => simp [project, hx, hy, Skeleton.fringe, List.append_assoc]
  | left => simp [project, hx, hy, Skeleton.fringe, List.append_assoc]
  | @inLeft a b c x y z h ih =>
      have hd := List.nodup_append.mp distinct
      have hout : x ∉ z :: componentKeys color true c := by
        intro hh
        exact hd.2.2 x h.keys.1 x
          ((List.Sublist.cons_cons z (componentKeys_sublist color true c)).subset hh) rfl
      cases hz : color z with
      | false => simp [componentKeys, hz] at active
      | true =>
          have ha : x ∈ componentKeys color true a := by
            simpa only [componentKeys, hz, ite_true, List.mem_append, hout, or_false] using active
          simp only [project, hz, ite_true, Skeleton.fringe, ih hx hy hd.1 ha]
  | @inRight a b c x y z h ih =>
      have hd := List.nodup_append.mp distinct
      have hn := List.nodup_cons.mp hd.2.1
      have hout : x ∉ componentKeys color true c := by
        intro hh
        exact hd.2.2 x ((componentKeys_sublist color true c).subset hh) x
          (by simp [h.keys.1]) rfl
      have hxz : x ≠ z := by intro hh; subst x; exact hn.1 h.keys.1
      cases hz : color z with
      | false => simp [componentKeys, hz] at active
      | true =>
          have ha : x ∈ componentKeys color true a := by
            simpa only [componentKeys, hz, ite_true, List.mem_append, List.mem_cons,
              hout, hxz, false_or] using active
          simp only [project, hz, ite_true, Skeleton.fringe, ih hx hy hn.2 ha]

theorem Trace.project_fringe (color : α → Bool) (h : Trace s ops t)
    (selected : ∀ e ∈ ops, color e.1 = true ∧ color e.2 = true)
    (distinct : s.inorder.Nodup)
    (covered : ∀ x, color x = true → x ∈ componentKeys color true s) :
    (project color s).fringe = (project color t).fringe := by
  induction h with
  | nil => rfl
  | @cons x y s v t es h ht ih =>
      have hs := selected (x, y) (by simp)
      have hu : color x = color y := hs.1.trans hs.2.symm
      have hv : v.inorder.Nodup := by
        rw [← Representation.Bridge.inorder_rotate h.forget]
        exact distinct
      have hc : ∀ z, color z = true → z ∈ componentKeys color true v := by
        intro z hz
        rw [← h.component_eq color true hu]
        exact covered z hz
      exact (h.project_fringe color hs.1 hs.2 distinct (covered x hs.1)).trans
        (ih (by intro e he; exact selected e (by simp [he])) hv hc)

end RotationBST.Pointer.Lazy
