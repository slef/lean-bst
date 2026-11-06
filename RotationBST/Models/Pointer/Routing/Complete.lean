module

public import RotationBST.Models.Pointer.Routing.Correctness

@[expose] public section
namespace RotationBST.Pointer.Routing

/-- Any distance-decreasing neighbor is precisely the edge chosen by the
stored interval rule. This identifies abstract scan moves with executable ones. -/
theorem next_of_move (v : View) {a b : Config} (target nextKey : Nat) (view : v.Valid a)
    (move : Move a b) (keyB : b.key? = some nextKey) (valid : target < a.tree.size)
    (closer : LazyFinger.distance b.tree nextKey target + 1 = LazyFinger.distance a.tree v.key target) :
    next v a target = some b := by
  rcases v with ⟨low, key, high⟩
  cases move with
  | @downLeft l r other cs =>
    simp only [View.Valid, Config.key?, offset, Option.some.injEq] at view keyB
    rcases view with ⟨rfl, rfl, rfl⟩
    subst nextKey
    have inside : offset cs ≤ target ∧ target < offset cs + (Tree.node l r).size := by
      by_contra outside
      have reverse := LazyFinger.up_left_closer l r other cs target valid outside
      change LazyFinger.distance (plug cs (.node (.node l r) other)) (offset cs + l.size) target + 1 =
        LazyFinger.distance (plug cs (.node (.node l r) other)) (offset cs + (Tree.node l r).size) target at closer
      omega
    have below : target < offset cs + (Tree.node l r).size := inside.2
    have inParent : offset cs ≤ target ∧ target < offset cs + (Tree.node (.node l r) other).size := by
      simp only [Tree.size] at *
      omega
    simp only [next, choose, Ne.symm (Nat.ne_of_gt below), inParent, below, and_self, ↓reduceIte, Option.bind_some, perform]
  | @downRight other l r cs =>
    simp only [View.Valid, Config.key?, offset, Option.some.injEq] at view keyB
    rcases view with ⟨rfl, rfl, rfl⟩
    subst nextKey
    have inside : offset cs + other.size + 1 ≤ target ∧
        target < offset cs + other.size + 1 + (Tree.node l r).size := by
      by_contra outside
      have reverse := LazyFinger.up_right_closer other l r cs target valid outside
      simp only [Config.tree, plug, Nat.add_assoc] at closer reverse
      omega
    have above : offset cs + other.size < target := by omega
    have inParent : offset cs ≤ target ∧ target < offset cs + (Tree.node other (.node l r)).size := by
      simp only [Tree.size] at *
      omega
    simp only [next, choose, Nat.ne_of_gt above, inParent, Nat.not_lt_of_ge (Nat.le_of_lt above), and_self,
      ↓reduceIte, Option.bind_some, perform]
  | @upLeft l r other cs =>
    simp only [View.Valid, Config.key?, offset, Option.some.injEq] at view keyB
    rcases view with ⟨rfl, rfl, rfl⟩
    subst nextKey
    have outside : ¬ (offset cs ≤ target ∧ target < offset cs + (Tree.node l r).size) := by
      intro inside
      have localValid : target - offset cs < (Tree.node l r).size := by omega
      have shifted : offset cs + (target - offset cs) = target := by omega
      have reverse := LazyFinger.down_left_closer l r other cs (target - offset cs) localValid
      rw [shifted] at reverse
      simp only [Config.tree, plug] at closer
      omega
    have different : target ≠ offset cs + l.size := by
      intro same
      apply outside
      simp only [same, Tree.size]
      omega
    simp only [next, choose, different, outside, ↓reduceIte, Option.bind_some, perform]
  | @upRight l r other cs =>
    simp only [View.Valid, Config.key?, offset, Option.some.injEq] at view keyB
    rcases view with ⟨rfl, rfl, rfl⟩
    subst nextKey
    have outside : ¬ (offset cs + other.size + 1 ≤ target ∧
        target < offset cs + other.size + 1 + (Tree.node l r).size) := by
      intro inside
      have localValid : target - (offset cs + other.size + 1) < (Tree.node l r).size := by omega
      have shifted : offset cs + (other.size + 1 + (target - (offset cs + other.size + 1))) = target := by omega
      have reverse := LazyFinger.down_right_closer other l r cs
        (target - (offset cs + other.size + 1)) localValid
      rw [shifted] at reverse
      simp only [Config.tree, plug, Nat.add_assoc] at closer reverse
      omega
    have different : target ≠ offset cs + other.size + 1 + l.size := by
      intro same
      apply outside
      simp only [same, Tree.size]
      omega
    simp only [next, choose, different, outside, ↓reduceIte, Option.bind_some, perform]

end RotationBST.Pointer.Routing
