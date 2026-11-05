module

public import RotationBST.Bounds.LazyFinger.Separation.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Neighborhood.Average

@[expose] public section
namespace RotationBST.LazyFinger

@[simp] theorem pairBlock_length (x y rounds : Nat) : (pairBlock x y rounds).length = 2 * rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp only [pairBlock, List.length_cons, ih]; omega

theorem pairBlock_valid (n x y rounds : Nat) (hx : x < n) (hy : y < n) :
    ∀ z ∈ pairBlock x y rounds, z < n := by
  induction rounds with
  | zero => simp [pairBlock]
  | succ rounds ih => intro z hz; simp only [pairBlock, List.mem_cons] at hz; rcases hz with rfl | rfl | hz <;> aesop

@[simp] theorem pairBlocks_length (pairs : List (Nat × Nat)) (rounds : Nat) :
    (pairBlocks pairs rounds).length = 2 * rounds * pairs.length := by
  induction pairs with
  | nil => simp [pairBlocks]
  | cons pair pairs ih =>
    change (pairBlock pair.1 pair.2 rounds ++ pairBlocks pairs rounds).length = _
    rw [List.length_append, pairBlock_length, ih, List.length_cons]
    ring

@[simp] theorem pairSequence_length (n rounds : Nat) :
    (pairSequence n rounds).length = 2 * rounds * n * n := by
  simp [pairSequence, List.length_flatMap, List.sum_replicate, Nat.mul_assoc]

theorem pairBlocks_valid (n rounds : Nat) (pairs : List (Nat × Nat))
    (valid : ∀ pair ∈ pairs, pair.1 < n ∧ pair.2 < n) :
    ∀ z ∈ pairBlocks pairs rounds, z < n := by
  intro z hz
  obtain ⟨pair, member, hz⟩ := List.mem_flatMap.mp hz
  exact pairBlock_valid n pair.1 pair.2 rounds (valid pair member).1 (valid pair member).2 z hz

theorem pairSequence_valid (n rounds : Nat) : ∀ z ∈ pairSequence n rounds, z < n := by
  apply pairBlocks_valid
  intro pair member
  obtain ⟨x, hx, hp⟩ := List.mem_flatMap.mp member
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  exact ⟨List.mem_range.mp hx, List.mem_range.mp hy⟩

/-- Each pair repetition contains its forward transition, independently of
where the lazy finger started and of transitions between adjacent blocks. -/
theorem pairBlock_lower (t : Tree) (p x y rounds : Nat) :
    rounds * distance t x y ≤ costFrom t p (pairBlock x y rounds) := by
  induction rounds generalizing p with
  | zero => simp [pairBlock, costFrom]
  | succ rounds ih =>
    have tail := ih y
    simp only [pairBlock, costFrom]
    nlinarith

theorem costFrom_append (t : Tree) (p : Nat) (xs ys : List Nat) :
    costFrom t p (xs ++ ys) = costFrom t p xs + costFrom t (xs.getLastD p) ys := by
  induction xs generalizing p with
  | nil => simp [costFrom]
  | cons x xs ih => simp only [List.cons_append, costFrom, ih, List.getLastD_cons]; omega

theorem pairBlocks_lower (t : Tree) (p rounds : Nat) (pairs : List (Nat × Nat)) :
    rounds * (pairs.map fun pair => distance t pair.1 pair.2).sum ≤
      costFrom t p (pairBlocks pairs rounds) := by
  induction pairs generalizing p with
  | nil => simp [pairBlocks, costFrom]
  | cons pair pairs ih =>
    change _ ≤ costFrom t p (pairBlock pair.1 pair.2 rounds ++ pairBlocks pairs rounds)
    rw [costFrom_append]
    have block := pairBlock_lower t p pair.1 pair.2 rounds
    have tail := ih ((pairBlock pair.1 pair.2 rounds).getLastD p)
    simp only [List.map_cons, List.sum_cons]
    nlinarith

theorem pairSequence_lower_from (t : Tree) (p rounds : Nat) :
    rounds * (∑ x ∈ Finset.range t.size, ∑ y ∈ Finset.range t.size, distance t x y) ≤
      costFrom t p (pairSequence t.size rounds) := by
  have bound := pairBlocks_lower t p rounds
    ((List.range t.size).flatMap fun x => (List.range t.size).map fun y => (x, y))
  have flatten_sum (xs : List Nat) (f : Nat → List Nat) :
      (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]
  have range_sum (n : Nat) (f : Nat → Nat) :
      ((List.range n).map f).sum = ∑ x ∈ Finset.range n, f x := by
    induction n with
    | zero => simp
    | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ih, Finset.sum_range_succ]
  simpa only [pairSequence, List.map_flatMap, List.map_map, Function.comp_def,
    flatten_sum, range_sum] using bound

/-- A single deterministic sequence incurs the all-pairs distance lower bound
in every reference tree, even though each block uses at most two keys. -/
theorem pairSequence_lower (t : Tree) (rounds r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    rounds * (r + 1) * t.size * t.size ≤ 2 * cost t (pairSequence t.size rounds) := by
  cases t with
  | nil => simp [Tree.size]
  | node l u =>
    have pairs := pair_distance_lower (.node l u) r large
    have blocks := pairSequence_lower_from (.node l u) l.size rounds
    change _ ≤ 2 * costFrom (.node l u) l.size _
    nlinarith

end RotationBST.LazyFinger
