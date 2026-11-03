module

public import RotationBST.Structures.Treap.Projection
public import RotationBST.Models.Region.Heapify
public import RotationBST.Structures.Treap.Restore
public import RotationBST.Models.Geometric.Offline.Proofs
public import RotationBST.Models.Region.View.Abstract

@[expose] public section
namespace RotationBST.Arboral
open Pointer.Lazy.Skeleton

/-- A connected-region rearrangement can visit any active key and finish in the
specified new shape, charging at most 33 pointer units per active node. -/
theorem region_serves {s u : Region} {x : Nat} (same : Region.Same s u 0)
    (hx : x ∈ Region.keys s 0) :
    ∃ cost, Pointer.Serves s.tree u.tree x cost ∧ cost ≤ 33 * s.size := by
  obtain ⟨a, b, hv, hroot⟩ := Region.expose s 0 x hx
  obtain ⟨i, hi, before⟩ := reshape s (.node a b) hv.fringe
  obtain ⟨j, hj, after⟩ := reshape (.node a b) u (hv.fringe.symm.trans same.fringe)
  have hsize := hv.size
  have positive : 0 < s.size := by
    rw [← Region.keys_card s 0]
    exact Finset.card_pos.mpr ⟨x, hx⟩
  refine ⟨1 + i + j, ?_, by omega⟩
  refine ⟨⟨(Pointer.Lazy.Skeleton.node a b).tree, []⟩, ⟨u.tree, []⟩, i, j, before, ?_, after, rfl, rfl⟩
  simp only [Pointer.Config.key?, tree, Pointer.offset, Nat.zero_add]
  simpa only [Nat.zero_add] using congrArg some hroot

/-- One ASS row is exactly one rooted-region operation. -/
theorem treap_region_step {P : Finset Point} {time request : Nat} (sat : ASS P)
    (t : Tree) (heap : Heap (nextTouch P time) t 0)
    (bounded : ∀ p ∈ P, p.1 < t.size) (req : (request, time) ∈ P) :
    ∃ u, ∃ step : RegionStep t u request, u.size = t.size ∧
      Heap (nextTouch P (time + 1)) u 0 ∧ step.before.size = (keysAt P time).card := by
  let s := Region.project P time t 0
  have hsTree : s.tree = t := Region.project_tree P time t 0
  have complete := Region.project_keys t 0 (P := P) (time := time)
  have hkeys : Region.keys s 0 = keysAt P time := by
    ext x
    rw [mem_keysAt]
    constructor
    · intro hx
      exact ((complete x heap).mp hx).1
    · intro hx
      exact (complete x heap).mpr ⟨hx, Nat.zero_le x, by simpa using bounded (x, time) hx⟩
  obtain ⟨u, same, active⟩ := Region.heapify (nextTouch P (time + 1)) s 0
  have heapU : Heap (nextTouch P (time + 1)) u.tree 0 := by
    apply Region.restore sat u 0 active
    · intro x
      rw [← same.2.1, ← same.1, hsTree]
      exact complete x heap
    · intro e he
      rw [← same.2.2] at he
      exact Region.project_holes t 0 heap e he
  have hx : request ∈ Region.keys s 0 := by rw [hkeys, mem_keysAt]; exact req
  let step : RegionStep t u.tree request := {
    before := s, after := u, source := hsTree, target := rfl,
    fringe := same.fringe, visits := hx }
  refine ⟨u.tree, step, ?_, heapU, ?_⟩
  · rw [← same.1, hsTree]
  · change s.size = (keysAt P time).card
    rw [← Region.keys_card s 0, hkeys]

/-- One offline ASS row is realized by an actual pointer-machine search. -/
theorem treap_step {P : Finset Point} {time request : Nat} (sat : ASS P)
    (t : Tree) (heap : Heap (nextTouch P time) t 0)
    (bounded : ∀ p ∈ P, p.1 < t.size) (req : (request, time) ∈ P) :
    ∃ u cost, u.size = t.size ∧ Heap (nextTouch P (time + 1)) u 0 ∧
      Pointer.Serves t u request cost ∧ cost ≤ 33 * (keysAt P time).card := by
  let s := Region.project P time t 0
  have hsTree : s.tree = t := Region.project_tree P time t 0
  have complete := Region.project_keys t 0 (P := P) (time := time)
  have hkeys : Region.keys s 0 = keysAt P time := by
    ext x
    rw [mem_keysAt]
    constructor
    · intro hx
      exact ((complete x heap).mp hx).1
    · intro hx
      exact (complete x heap).mpr ⟨hx, Nat.zero_le x, by simpa using bounded (x, time) hx⟩
  obtain ⟨u, same, active⟩ := Region.heapify (nextTouch P (time + 1)) s 0
  have heapU : Heap (nextTouch P (time + 1)) u.tree 0 := by
    apply Region.restore sat u 0 active
    · intro x
      rw [← same.2.1, ← same.1, hsTree]
      exact complete x heap
    · intro e he
      rw [← same.2.2] at he
      exact Region.project_holes t 0 heap e he
  have hx : request ∈ Region.keys s 0 := by rw [hkeys, mem_keysAt]; exact req
  obtain ⟨cost, serves, bound⟩ := region_serves same hx
  refine ⟨u.tree, cost, ?_, heapU, ?_, ?_⟩
  · rw [← same.1, hsTree]
  · simpa only [hsTree] using serves
  · rw [← Region.keys_card s 0, hkeys] at bound
    exact bound

end RotationBST.Arboral
