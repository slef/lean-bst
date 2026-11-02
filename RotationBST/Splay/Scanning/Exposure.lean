module

public import RotationBST.Splay.Scanning.Arithmetic

@[expose] public section

namespace RotationBST.Splay.Scanning.Marked

/-- First mark a previously untouched left spine. -/
def paint : Tree → Marked
  | .nil => .hole .nil
  | .node l r => .node (paint l) (.hole r)

/-- Mark the left spine, retaining all existing marks. -/
def expose : Marked → Marked
  | .hole t => paint t
  | .node l r => .node (expose l) r

/-- The left spine ends at an actual empty hole. -/
def Ready : Marked → Prop
  | .hole t => t = .nil
  | .node l _ => l.Ready

theorem paint_tree (t : Tree) : (paint t).tree = t := by
  induction t with
  | nil => rfl
  | node l r il _ => simp only [paint, tree, il]

theorem paint_rank (t : Tree) : (paint t).rank ≤ 1 := by
  cases t <;> simp [paint, rank]

theorem paint_valid (t : Tree) : (paint t).Valid := by
  induction t with
  | nil => trivial
  | node l r il _ => exact ⟨il, trivial, paint_rank l⟩

theorem paint_ready (t : Tree) : (paint t).Ready := by
  induction t with
  | nil => rfl
  | node _ _ ih _ => exact ih

theorem paint_potential (t : Tree) : (paint t).potential + 7 * (paint t).rank ≤ 18 * t.size := by
  induction t with
  | nil => simp [paint, potential, rank, Tree.size]
  | node l r il _ =>
      have hr := paint_rank l
      have hc : credit 1 (paint l).rank ≤ 11 := by
        have := credit_mono (g := 1) hr
        norm_num [credit, alpha] at this ⊢
        exact this
      simp only [paint, potential, rank, Tree.size, Nat.zero_add]
      omega

theorem expose_tree (t : Marked) : t.expose.tree = t.tree := by
  induction t with
  | hole => exact paint_tree _
  | node l r il _ => simp only [expose, tree, il]

theorem expose_rank (t : Marked) : t.rank ≤ t.expose.rank ∧
    t.expose.rank ≤ max 1 t.rank ∧ (t.rank ≠ 0 → t.expose.rank = t.rank) := by
  cases t with
  | hole t => exact ⟨Nat.zero_le _, by simpa [rank, expose] using paint_rank t, by simp [rank]⟩
  | node l r => simp [expose, rank]

theorem expose_valid (t : Marked) (valid : t.Valid) : t.expose.Valid := by
  induction t with
  | hole => exact paint_valid _
  | node l r il _ =>
      refine ⟨il valid.1, valid.2.1, ?_⟩
      have h := expose_rank l
      have hh := valid.2.2
      change l.expose.rank ≤ r.rank + 1
      omega

theorem expose_ready (t : Marked) : t.expose.Ready := by
  induction t with
  | hole => exact paint_ready _
  | node _ _ ih _ => exact ih

theorem expose_potential (t : Marked) :
    t.expose.potential + 7 * t.expose.rank ≤ t.potential + 7 * t.rank := by
  induction t with
  | hole t => simpa only [expose, potential, rank, Nat.mul_zero, Nat.add_zero] using paint_potential t
  | node l r il _ =>
      have hr := expose_rank l
      have hc : credit (r.rank + 1) l.expose.rank + 7 * l.rank ≤
          credit (r.rank + 1) l.rank + 7 * l.expose.rank := by
        by_cases hz : l.rank = 0
        · have he : l.expose.rank = 0 ∨ l.expose.rank = 1 := by omega
          rcases he with he | he
          · simp only [hz, he, le_refl]
          · rw [hz, he]
            have := credit_expose (r.rank + 1) (by omega)
            omega
        · rw [hr.2.2 hz]
      simp only [expose, potential, rank]
      omega

end RotationBST.Splay.Scanning.Marked
