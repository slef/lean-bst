module

public import RotationBST.Bounds.LazyFinger.ReadonlyWalk
public import RotationBST.Bounds.LazyFinger.Initialization
public import RotationBST.Models.Pointer.Location
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Embedding a subtree preserves distances between its keys. -/
theorem distance_plug (cs : List Pointer.Frame) (t : Tree) (x y : Nat)
    (hx : x < t.size) (hy : y < t.size) :
    distance (Pointer.plug cs t) (Pointer.offset cs + x) (Pointer.offset cs + y) = distance t x y := by
  induction cs generalizing t x y with
  | nil => simp [Pointer.plug, Pointer.offset]
  | cons frame cs ih =>
    cases frame with
    | left r =>
      simp only [Pointer.plug, Pointer.offset]
      rw [ih (.node t r) x y (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
      simp only [distance, hx, hy, and_self, ↓reduceIte]
    | right l =>
      simp only [Pointer.plug, Pointer.offset]
      have px : Pointer.offset cs + l.size + 1 + x = Pointer.offset cs + (l.size + 1 + x) := by omega
      have py : Pointer.offset cs + l.size + 1 + y = Pointer.offset cs + (l.size + 1 + y) := by omega
      rw [px, py, ih (.node l t) (l.size + 1 + x) (l.size + 1 + y)
        (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
      have highX : l.size < l.size + 1 + x := by omega
      have highY : l.size < l.size + 1 + y := by omega
      have indexX : l.size + 1 + x - l.size - 1 = x := by omega
      have indexY : l.size + 1 + y - l.size - 1 = y := by omega
      simp only [distance, Nat.not_lt.mpr highX.le, highX, highY, false_and, and_self, ↓reduceIte, indexX, indexY]

private theorem parent_left (a b r : Tree) : distance (.node (.node a b) r) (Tree.node a b).size a.size = 1 := by
  rw [distance_from_root]
  have left : a.size < (Tree.node a b).size := by simp only [Tree.size]; omega
  simp [Tree.depth, left]

private theorem parent_right (l a b : Tree) :
    distance (.node l (.node a b)) l.size (l.size + 1 + a.size) = 1 := by
  rw [distance_from_root]
  have high : l.size < l.size + 1 + a.size := by omega
  have index : l.size + 1 + a.size - l.size - 1 = a.size := by omega
  simp [Tree.depth, Nat.not_lt.mpr high.le, Nat.ne_of_gt high, index]

/-- Every navigation primitive traverses exactly one edge in the fixed tree. -/
theorem move_distance {a b : Pointer.Config} (move : Pointer.Move a b) (x y : Nat)
    (keyA : a.key? = some x) (keyB : b.key? = some y) : distance a.tree x y = 1 := by
  cases move with
  | @downLeft a b r cs =>
    have first := Option.some.inj keyA
    have last := Option.some.inj keyB
    change Pointer.offset cs + (Tree.node a b).size = x at first
    change Pointer.offset cs + a.size = y at last
    rw [← first, ← last]
    change distance (Pointer.plug cs (.node (.node a b) r)) _ _ = 1
    rw [distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
    exact parent_left a b r
  | @downRight l a b cs =>
    have first := Option.some.inj keyA
    have last := Option.some.inj keyB
    change Pointer.offset cs + l.size = x at first
    change Pointer.offset cs + l.size + 1 + a.size = y at last
    have shifted : Pointer.offset cs + l.size + 1 + a.size = Pointer.offset cs + (l.size + 1 + a.size) := by omega
    rw [← first, ← last, shifted]
    change distance (Pointer.plug cs (.node l (.node a b))) _ _ = 1
    rw [distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
    exact parent_right l a b
  | @upLeft a b r cs =>
    have first := Option.some.inj keyA
    have last := Option.some.inj keyB
    change Pointer.offset cs + a.size = x at first
    change Pointer.offset cs + (Tree.node a b).size = y at last
    rw [← first, ← last]
    change distance (Pointer.plug cs (.node (.node a b) r)) _ _ = 1
    rw [distance_symm, distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
    exact parent_left a b r
  | @upRight a b l cs =>
    have first := Option.some.inj keyA
    have last := Option.some.inj keyB
    change Pointer.offset cs + l.size + 1 + a.size = x at first
    change Pointer.offset cs + l.size = y at last
    have shifted : Pointer.offset cs + l.size + 1 + a.size = Pointer.offset cs + (l.size + 1 + a.size) := by omega
    rw [← first, ← last, shifted]
    change distance (Pointer.plug cs (.node l (.node a b))) _ _ = 1
    rw [distance_symm, distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
    exact parent_right l a b

/-- No navigation-only walk is shorter than the lazy-finger distance. -/
theorem distance_le_walk {a b : Pointer.Config} {k : Nat} (walk : Pointer.Walk a b k)
    (x y : Nat) (keyA : a.key? = some x) (keyB : b.key? = some y) : distance a.tree x y ≤ k := by
  induction walk generalizing x with
  | @refl c =>
    have same : x = y := Option.some.inj (keyA.symm.trans keyB)
    subst y
    rw [distance_self _ _ (c.key_lt_size _ keyA)]
  | @step a b c k move rest ih =>
    obtain ⟨z, key⟩ := move.step.keys_exist.2
    have tail := ih z key keyB
    have edge := move_distance move x z keyA key
    have triangle := distance_triangle a.tree x z y (a.key_lt_size x keyA)
      (by rw [move.tree_eq]; exact b.key_lt_size z key)
      (by rw [(Pointer.Walk.step move rest).tree_eq]; exact c.key_lt_size y keyB)
    rw [← move.tree_eq] at tail
    omega

/-- A pending target always admits a legal one-edge move that decreases its
distance. This prevents the scan semantics from assuming an unrealizable route. -/
theorem toward_exists (a : Pointer.Config) (x y : Nat) (key : a.key? = some x)
    (valid : y < a.tree.size) (different : x ≠ y) :
    ∃ b z, Pointer.Move a b ∧ b.key? = some z ∧ distance b.tree z y + 1 = distance a.tree x y := by
  obtain ⟨start, finish, treeStart, treeFinish, keyStart, keyFinish, walk⟩ :=
    readonly_walk a.tree x y (a.key_lt_size x key) valid
  have same : start = a := Pointer.Config.ext_key treeStart keyStart key
  subst start
  generalize length : distance a.tree x y = k at walk
  cases walk with
  | refl => exact False.elim (different (Option.some.inj (key.symm.trans keyFinish)))
  | @step _ b _ k move rest =>
    obtain ⟨z, nextKey⟩ := move.step.keys_exist.2
    have upper := distance_le_walk rest z y nextKey keyFinish
    have triangle := distance_triangle a.tree x z y (a.key_lt_size x key)
      (by rw [move.tree_eq]; exact b.key_lt_size z nextKey) valid
    have edge := move_distance move x z key nextKey
    refine ⟨b, z, move, nextKey, ?_⟩
    rw [← move.tree_eq] at upper ⊢
    omega

end RotationBST.LazyFinger
