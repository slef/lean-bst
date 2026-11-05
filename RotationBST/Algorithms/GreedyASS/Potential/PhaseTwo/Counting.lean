module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.Items
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Blue
public import RotationBST.Algorithms.GreedyASS.Virgin.Potential
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
open Items Reference

/-- Charge each colored new access to a touched reference component.
The union-cardinality bound does not need arbitrary choices of owners. -/
theorem count_components (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t)
    (color : Color) (limit : Nat)
    (bound : ∀ c ∈ forest t lo searched,
      (((Virgin.points (searches ++ [searched])).image Prod.fst).filter fun x =>
        c.Contains x ∧ itemColor t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) x = some color).card ≤ limit) :
    (coloredKeys t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched]))
      (Virgin.keys searches searched) color).card ≤ limit * (Virgin.touched t lo searches searched).card := by
  classical
  let Q := Virgin.points (searches ++ [searched])
  let selected := coloredKeys t lo (searches ++ [searched]) Q (Virgin.keys searches searched) color
  let components := Virgin.touched t lo searches searched
  let f := fun c : Component => (Q.image Prod.fst).filter fun x =>
    c.Contains x ∧ itemColor t lo (searches ++ [searched]) Q x = some color
  have subset : selected ⊆ components.biUnion f := by
    intro x hx
    obtain ⟨accessed, colored⟩ := Finset.mem_filter.mp hx
    have point : (x, searches.length) ∈ Q := by
      change (x, searches.length) ∈ Virgin.points (searches ++ [searched])
      rw [Virgin.points_snoc]
      exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨accessed, rfl⟩)
    have inside := Unaccessed.points_property _ (searches ++ [searched]) valid _ point
    obtain ⟨c, member, contains⟩ := Reference.covers t lo searched x inside
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr member, x, accessed, contains⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(x, searches.length), point, rfl⟩, contains, colored⟩
  have sumBound : ∑ c ∈ components, (f c).card ≤ ∑ _c ∈ components, limit := by
    apply Finset.sum_le_sum
    intro c hc
    exact bound c (List.mem_toFinset.mp (Finset.mem_filter.mp hc).1)
  have cardinal := (Finset.card_le_card subset).trans ((Finset.card_biUnion_le).trans sumBound)
  simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using cardinal

/-- All newly blue and purple accesses lie in touched components, so the
four-blue/two-purple bounds sum to six times the touched-root count. -/
theorem color_counts (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t) :
    (coloredKeys t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched]))
        (Virgin.keys searches searched) .blue).card +
      (coloredKeys t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched]))
        (Virgin.keys searches searched) .purple).card ≤ 6 * (Virgin.touched t lo searches searched).card := by
  have satisfied := Unaccessed.points_satisfied (searches ++ [searched]) (fun x hx => (valid x hx).2)
  have history : History (lo + leaves t) (searches.length + 1) (Virgin.points (searches ++ [searched])) := by
    simpa only [List.length_append, List.length_singleton] using
      Virgin.points_history _ (searches ++ [searched]) (fun x hx => (valid x hx).2)
  have blueBound := count_components t lo searches searched valid .blue 4
    (fun c hc => Counting.blue_count t lo searches searched satisfied history hc)
  have purpleBound := count_components t lo searches searched valid .purple 2
    (fun c hc => Counting.purple_count t lo searches searched satisfied history hc)
  omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
