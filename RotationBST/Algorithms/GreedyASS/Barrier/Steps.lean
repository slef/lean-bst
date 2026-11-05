module

public import RotationBST.Algorithms.GreedyASS.Barrier.Definitions.Abstract
public import RotationBST.Models.Geometric.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Barrier

/-- An access on the last row establishes both barrier directions. No
assumption about how that history was generated is needed. -/
theorem of_history {n stamp key : Nat} {P : Finset Point}
    (history : History n (stamp + 1) P) (accessed : (key, stamp) ∈ P) :
    Left P key stamp ∧ Right P key stamp := by
  exact ⟨⟨accessed, fun p hp _ => by have := (history p hp).2; omega⟩,
    ⟨accessed, fun p hp _ => by have := (history p hp).2; omega⟩⟩

/-- A request on or to the right of a left barrier cannot project an old
point from the far side: the barrier witnesses its nonempty rectangle. -/
theorem sweep_left {P : Finset Point} {key stamp time request : Nat}
    (barrier : Left P key stamp) (later : stamp ≤ time) (side : key ≤ request) :
    ∀ x ∈ greedySweep time request P, key ≤ x := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact side
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hq, visible⟩ := Finset.mem_filter.mp hq
  by_contra crossed
  have far : q.1 < key := by omega
  have old := barrier.2 q hq far
  have distinct : (key, stamp) ≠ q := by
    intro equal
    have := congrArg Prod.fst equal
    simp only at this
    omega
  apply visible.2 (key, stamp) barrier.1 distinct
  unfold Rectangle
  simp only
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem sweep_right {P : Finset Point} {key stamp time request : Nat}
    (barrier : Right P key stamp) (later : stamp ≤ time) (side : request ≤ key) :
    ∀ x ∈ greedySweep time request P, x ≤ key := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact side
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hq, visible⟩ := Finset.mem_filter.mp hq
  by_contra crossed
  have far : key < q.1 := by omega
  have old := barrier.2 q hq far
  have distinct : (key, stamp) ≠ q := by
    intro equal
    have := congrArg Prod.fst equal
    simp only at this
    omega
  apply visible.2 (key, stamp) barrier.1 distinct
  unfold Rectangle
  simp only
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A sweep on the near side preserves the original barrier point and leaves
every point on the far side unchanged. -/
theorem step_left {P : Finset Point} {key stamp time request : Nat}
    (barrier : Left P key stamp) (later : stamp ≤ time) (side : key ≤ request) :
    Left (P ∪ row time (greedySweep time request P)) key stamp ∧
      ∀ p : Point, p.1 < key →
        (p ∈ P ∪ row time (greedySweep time request P) ↔ p ∈ P) := by
  have blocked := sweep_left barrier later side
  have unchanged : ∀ p : Point, p.1 < key →
      (p ∈ P ∪ row time (greedySweep time request P) ↔ p ∈ P) := by
    intro p far
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hp
      · have := blocked p.1 ((mem_row p time _).mp hp).1
        omega
    · exact Finset.mem_union_left _
  exact ⟨⟨Finset.mem_union_left _ barrier.1,
    fun p hp far => barrier.2 p ((unchanged p far).mp hp) far⟩, unchanged⟩

theorem step_right {P : Finset Point} {key stamp time request : Nat}
    (barrier : Right P key stamp) (later : stamp ≤ time) (side : request ≤ key) :
    Right (P ∪ row time (greedySweep time request P)) key stamp ∧
      ∀ p : Point, key < p.1 →
        (p ∈ P ∪ row time (greedySweep time request P) ↔ p ∈ P) := by
  have blocked := sweep_right barrier later side
  have unchanged : ∀ p : Point, key < p.1 →
      (p ∈ P ∪ row time (greedySweep time request P) ↔ p ∈ P) := by
    intro p far
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hp
      · have := blocked p.1 ((mem_row p time _).mp hp).1
        omega
    · exact Finset.mem_union_left _
  exact ⟨⟨Finset.mem_union_left _ barrier.1,
    fun p hp far => barrier.2 p ((unchanged p far).mp hp) far⟩, unchanged⟩

end RotationBST.Geometric.GreedyASS.Barrier
