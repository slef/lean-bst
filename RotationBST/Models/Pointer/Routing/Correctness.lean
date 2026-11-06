module

public import RotationBST.Models.Pointer.Routing.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.LocalRouting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Pointer.Routing

theorem perform_sound {direction : Direction} {a b : Config} (step : perform direction a = some b) :
    Move a b := by
  unfold perform at step
  split at step <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst b; constructor

/-- With correct current-node fields, the local rule chooses a legal edge
whose endpoint is exactly one unit closer to the requested key. -/
theorem next_correct (v : View) (cursor : Config) (target : Nat) (view : v.Valid cursor)
    (valid : target < cursor.tree.size) (different : v.key ≠ target) :
    ∃ nextCursor key, next v cursor target = some nextCursor ∧ Move cursor nextCursor ∧
      nextCursor.key? = some key ∧
      LazyFinger.distance nextCursor.tree key target + 1 = LazyFinger.distance cursor.tree v.key target := by
  rcases cursor with ⟨focus, cs⟩
  rcases v with ⟨low, key, high⟩
  change low = offset cs ∧ (Config.mk focus cs).key? = some key ∧ high = low + focus.size at view
  rcases view with ⟨rfl, keyAt, rfl⟩
  cases focus with
  | nil => simp [Config.key?] at keyAt
  | node l r =>
    have root : offset cs + l.size = key := Option.some.inj keyAt
    subst key
    change offset cs + l.size ≠ target at different
    change target < (plug cs (.node l r)).size at valid
    by_cases inside : offset cs ≤ target ∧ target < offset cs + (Tree.node l r).size
    · by_cases left : target < offset cs + l.size
      · cases l with
        | nil => simp only [Tree.size, Nat.add_zero] at left; omega
        | node a b =>
          have localY : target - offset cs < (Tree.node a b).size := by omega
          have shifted : target = offset cs + (target - offset cs) := by omega
          refine ⟨⟨.node a b, .left r :: cs⟩, offset cs + a.size, ?_, .downLeft, rfl, ?_⟩
          · simp only [next, choose, Ne.symm different, inside, and_self, left, ↓reduceIte, Option.bind_some, perform]
          · change LazyFinger.distance (plug cs (.node (.node a b) r)) (offset cs + a.size) target + 1 = _
            rw [shifted]
            exact LazyFinger.down_left_closer a b r cs _ localY
      · cases r with
        | nil => simp only [Tree.size] at inside; omega
        | node a b =>
          have localY : target - offset cs - l.size - 1 < (Tree.node a b).size := by
            simp only [Tree.size] at inside ⊢; omega
          have shifted : target = offset cs + (l.size + 1 + (target - offset cs - l.size - 1)) := by omega
          refine ⟨⟨.node a b, .right l :: cs⟩, offset cs + l.size + 1 + a.size, ?_, .downRight, rfl, ?_⟩
          · simp only [next, choose, Ne.symm different, inside, and_self, left, ↓reduceIte, Option.bind_some, perform]
          · change LazyFinger.distance (plug cs (.node l (.node a b))) (offset cs + l.size + 1 + a.size) target + 1 = _
            rw [shifted]
            simpa only [Nat.add_assoc, Config.tree] using LazyFinger.down_right_closer l a b cs _ localY
    · cases cs with
      | nil => simp only [plug, offset] at valid inside; omega
      | cons frame cs =>
        cases frame with
        | left other =>
          refine ⟨⟨.node (.node l r) other, cs⟩, offset cs + (Tree.node l r).size, ?_, .upLeft, rfl, ?_⟩
          · simp only [next, choose, Ne.symm different, inside, ↓reduceIte, Option.bind_some, perform]
          · exact LazyFinger.up_left_closer l r other cs target valid inside
        | right other =>
          refine ⟨⟨.node other (.node l r), cs⟩, offset cs + other.size, ?_, .upRight, rfl, ?_⟩
          · simp only [next, choose, Ne.symm different, inside, ↓reduceIte, Option.bind_some, perform]
          · simpa only [Config.tree, plug, offset, Nat.add_assoc] using
              LazyFinger.up_right_closer other l r cs target valid inside

theorem arrived (v : View) (cursor : Config) : next v cursor v.key = none := by simp [next, choose]

/-- Correct interval fields fit in the existing key universe. -/
theorem view_bounds (v : View) (cursor : Config) (view : v.Valid cursor) :
    v.low ≤ v.key ∧ v.key < v.high ∧ v.high ≤ cursor.tree.size := by
  rcases view with ⟨low, key, high⟩
  have bound := offset_add_size_le_plug cursor.context cursor.focus
  change offset cursor.context + cursor.focus.size ≤ cursor.tree.size at bound
  cases focus : cursor.focus with
  | nil => simp [Config.key?, focus] at key
  | node l r =>
    have root : offset cursor.context + l.size = v.key := by simpa only [Config.key?, focus, Option.some.injEq] using key
    rw [focus] at bound high
    simp only [Tree.size] at bound high
    omega

end RotationBST.Pointer.Routing
