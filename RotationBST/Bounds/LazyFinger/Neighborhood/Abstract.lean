module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Neighborhood.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Neighborhood.Results

/-- Uniform exponential bound on every fixed tree's lazy-finger neighborhood. -/
theorem cardinality (t : Tree) (x r : Nat) (valid : x < t.size) :
    (ball t x r).card ≤ 7 ^ r := ball_card t x r valid

/-- Counting the near ball gives a distance-sum lower bound without asymptotics. -/
theorem distance_sum (t : Tree) (x r : Nat) (valid : x < t.size) :
    (r + 1) * t.size ≤ (r + 1) * 7 ^ r + ∑ y ∈ Finset.range t.size, distance t x y :=
  distance_sum_lower t x r valid

/-- Every starting key has average distance at least `(r+1)/2` when the universe
has at least `2 * 7^r` keys. -/
theorem average (t : Tree) (x r : Nat) (valid : x < t.size) (large : 2 * 7 ^ r ≤ t.size) :
    (r + 1) * t.size ≤ 2 * ∑ y ∈ Finset.range t.size, distance t x y :=
  average_distance_lower t x r valid large

/-- The all-pairs version used for the lazy-finger/dynamic separation. -/
theorem pairs (t : Tree) (r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    (r + 1) * t.size * t.size ≤
      2 * ∑ x ∈ Finset.range t.size, ∑ y ∈ Finset.range t.size, distance t x y :=
  pair_distance_lower t r large

end RotationBST.LazyFinger.Neighborhood.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Neighborhood.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Neighborhood.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Neighborhood.Definitions.Abstract]
