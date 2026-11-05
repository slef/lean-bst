module

public import RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract
public import Mathlib.Basic.ExistsUnique
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference

theorem leaves_positive (t : Tree) : 0 < leaves t := by
  induction t with
  | nil => decide
  | node l r il ir => simp only [leaves]; omega

theorem leaves_eq (t : Tree) : leaves t = t.size + 1 := by
  induction t with
  | nil => rfl
  | node l r il ir => simp only [leaves, Tree.size, il, ir]; omega

theorem component_nonempty (c : Component) : c.first < c.last := by
  have := leaves_positive c.shape
  unfold Component.last
  omega

/-- Every forest component is a nonempty subinterval of the reference tree. -/
theorem bounds (t : Tree) (lo searched : Nat) {c : Component}
    (member : c ∈ forest t lo searched) : lo ≤ c.first ∧ c.last ≤ lo + leaves t := by
  induction t generalizing lo with
  | nil =>
    simp only [forest, List.mem_singleton] at member
    subst c
    simp [Component.last]
  | node l r il ir =>
    simp only [forest] at member
    split at member
    · rcases List.mem_append.mp member with member | member
      · have h := il lo member
        simp only [leaves]
        omega
      · simp only [List.mem_singleton] at member
        subst c
        simp [Component.last, leaves, Nat.add_assoc]
    · rcases List.mem_cons.mp member with member | member
      · subst c
        simp [Component.last, leaves]
      · have h := ir (lo + leaves l) member
        simp only [leaves]
        omega

/-- Components are ordered and disjoint, rather than merely covering keys. -/
theorem ordered (t : Tree) (lo searched : Nat) :
    (forest t lo searched).Pairwise (fun a b => a.last ≤ b.first) := by
  induction t generalizing lo with
  | nil => simp [forest]
  | node l r il ir =>
    rw [forest]
    split
    · rw [List.pairwise_append]
      refine ⟨il lo, by simp, ?_⟩
      intro a ha b hb
      have eq : b = ⟨lo + leaves l, r⟩ := by simpa using hb
      subst b
      exact (bounds l lo searched ha).2
    · rw [List.pairwise_cons]
      exact ⟨fun b hb => (bounds r (lo + leaves l) searched hb).1, ir _⟩

/-- Every valid reference key belongs to a forest component. -/
theorem covers (t : Tree) (lo searched key : Nat)
    (valid : lo ≤ key ∧ key < lo + leaves t) :
    ∃ c ∈ forest t lo searched, c.Contains key := by
  induction t generalizing lo with
  | nil =>
    exact ⟨⟨lo, .nil⟩, by simp [forest], valid⟩
  | node l r il ir =>
    rw [forest]
    simp only [leaves] at valid
    split
    · by_cases left : key < lo + leaves l
      · obtain ⟨c, member, contains⟩ := il lo ⟨valid.1, left⟩
        exact ⟨c, List.mem_append_left _ member, contains⟩
      · exact ⟨⟨lo + leaves l, r⟩, List.mem_append_right _ (by simp),
          by simp only [Component.Contains, Component.last]; omega⟩
    · by_cases left : key < lo + leaves l
      · exact ⟨⟨lo, l⟩, by simp, ⟨valid.1, left⟩⟩
      · obtain ⟨c, member, contains⟩ := ir (lo + leaves l) (by omega)
        exact ⟨c, List.mem_cons_of_mem _ member, contains⟩

/-- The searched leaf survives as a singleton component. -/
theorem selected (t : Tree) (lo searched : Nat)
    (valid : lo ≤ searched ∧ searched < lo + leaves t) :
    (⟨searched, .nil⟩ : Component) ∈ forest t lo searched := by
  induction t generalizing lo with
  | nil =>
    have eq : searched = lo := by simp only [leaves] at valid; omega
    simp [forest, eq]
  | node l r il ir =>
    rw [forest]
    split
    · exact List.mem_append_left _ (il lo ⟨valid.1, by assumption⟩)
    · apply List.mem_cons_of_mem
      apply ir (lo + leaves l)
      simp only [leaves] at valid
      constructor <;> omega

theorem unique_of_ordered (cs : List Component)
    (sorted : cs.Pairwise (fun a b => a.last ≤ b.first))
    {a b : Component} {key : Nat} (ha : a ∈ cs) (hb : b ∈ cs)
    (ca : a.Contains key) (cb : b.Contains key) : a = b := by
  induction cs with
  | nil => simp at ha
  | cons c cs ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp sorted
    rcases List.mem_cons.mp ha with eq | ha
    · subst a
      rcases List.mem_cons.mp hb with eq | hb
      · exact eq.symm
      · have h := head b hb
        unfold Component.Contains at ca cb
        omega
    · rcases List.mem_cons.mp hb with eq | hb
      · subst b
        have h := head a ha
        unfold Component.Contains at ca cb
        omega
      · exact ih tail ha hb

/-- A valid leaf belongs to exactly one component, with no overlapping roots. -/
theorem partition (t : Tree) (lo searched key : Nat)
    (valid : lo ≤ key ∧ key < lo + leaves t) :
    ∃! c, c ∈ forest t lo searched ∧ c.Contains key := by
  obtain ⟨c, member, contains⟩ := covers t lo searched key valid
  refine ⟨c, ⟨member, contains⟩, ?_⟩
  intro b hb
  exact unique_of_ordered _ (ordered t lo searched) hb.1 member hb.2 contains

theorem contains_searched (t : Tree) (lo searched : Nat)
    (valid : lo ≤ searched ∧ searched < lo + leaves t) {c : Component}
    (member : c ∈ forest t lo searched) (contains : c.Contains searched) :
    c = ⟨searched, .nil⟩ := by
  apply unique_of_ordered _ (ordered t lo searched) member (selected t lo searched valid) contains
  simp [Component.Contains, Component.last, leaves]

end RotationBST.Geometric.GreedyASS.Reference
