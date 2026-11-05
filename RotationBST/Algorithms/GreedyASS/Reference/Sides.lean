module

public import RotationBST.Algorithms.GreedyASS.Reference.Partition
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference

/-- If a component persists for two searches outside its range, both
searches are on the same side. The searched singleton is excluded explicitly. -/
theorem same_side (t : Tree) (lo x y : Nat) {c : Component}
    (vx : lo ≤ x ∧ x < lo + leaves t) (vy : lo ≤ y ∧ y < lo + leaves t)
    (mx : c ∈ forest t lo x) (my : c ∈ forest t lo y)
    (ox : ¬ c.Contains x) (oy : ¬ c.Contains y) :
    (x < c.first ∧ y < c.first) ∨ (c.last ≤ x ∧ c.last ≤ y) := by
  induction t generalizing lo with
  | nil =>
    have eq : c = ⟨lo, .nil⟩ := by simpa [forest] using mx
    subst c
    exact (ox vx).elim
  | node l r il ir =>
    simp only [leaves] at vx vy
    by_cases hx : x < lo + leaves l <;> by_cases hy : y < lo + leaves l
    · simp only [forest, hx, hy, ↓reduceIte, List.mem_append, List.mem_singleton] at mx my
      by_cases eq : c = ⟨lo + leaves l, r⟩
      · subst c
        exact Or.inl ⟨hx, hy⟩
      · exact il lo ⟨vx.1, hx⟩ ⟨vy.1, hy⟩ (mx.resolve_right eq) (my.resolve_right eq)
    · simp only [forest, hx, hy, ↓reduceIte, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mx my
      rcases mx with ml | eq
      · rcases my with eq | mr
        · subst c
          exact (ox ⟨vx.1, hx⟩).elim
        · have bl := bounds l lo x ml
          have br := bounds r (lo + leaves l) y mr
          have nonempty := component_nonempty c
          omega
      · subst c
        apply False.elim
        apply oy
        simp only [Component.Contains, Component.last]
        omega
    · simp only [forest, hx, hy, ↓reduceIte, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mx my
      rcases my with ml | eq
      · rcases mx with eq | mr
        · subst c
          exact (oy ⟨vy.1, hy⟩).elim
        · have bl := bounds l lo y ml
          have br := bounds r (lo + leaves l) x mr
          have nonempty := component_nonempty c
          omega
      · subst c
        apply False.elim
        apply ox
        simp only [Component.Contains, Component.last]
        omega
    · simp only [forest, hx, hy, ↓reduceIte, List.mem_cons] at mx my
      by_cases eq : c = ⟨lo, l⟩
      · subst c
        right
        simp only [Component.last]
        constructor <;> omega
      · apply ir (lo + leaves l) (by omega) (by omega)
          (mx.resolve_left eq) (my.resolve_left eq)

/-- The membership-based form of the search-side conclusion. A component
other than either searched singleton is disjoint from both searches. -/
theorem persistent_side (t : Tree) (lo x y : Nat) {c : Component}
    (vx : lo ≤ x ∧ x < lo + leaves t) (vy : lo ≤ y ∧ y < lo + leaves t)
    (mx : c ∈ forest t lo x) (my : c ∈ forest t lo y)
    (nx : c ≠ ⟨x, .nil⟩) (ny : c ≠ ⟨y, .nil⟩) :
    (x < c.first ∧ y < c.first) ∨ (c.last ≤ x ∧ c.last ≤ y) :=
  same_side t lo x y vx vy mx my
    (fun h => nx (contains_searched t lo x vx mx h))
    (fun h => ny (contains_searched t lo y vy my h))

/-- A reference component that persists outside a sequence of searched
singletons has one fixed search side for the whole sequence. -/
theorem stream_side (t : Tree) (lo first : Nat) (xs : List Nat) {c : Component}
    (valid : ∀ x ∈ first :: xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ first :: xs, c ∈ forest t lo x)
    (other : ∀ x ∈ first :: xs, c ≠ ⟨x, .nil⟩) :
    (∀ x ∈ first :: xs, x < c.first) ∨ (∀ x ∈ first :: xs, c.last ≤ x) := by
  have initialValid := valid first (by simp)
  have initialMember := member first (by simp)
  have initialOther := other first (by simp)
  by_cases left : first < c.first
  · left
    intro x hx
    have sides := persistent_side t lo first x initialValid (valid x hx)
      initialMember (member x hx) initialOther (other x hx)
    have nonempty := component_nonempty c
    omega
  · right
    intro x hx
    have sides := persistent_side t lo first x initialValid (valid x hx)
      initialMember (member x hx) initialOther (other x hx)
    omega

/-- Even a searched singleton cannot persist while searches straddle a key
inside its component. This handles visits to that singleton without assuming
that every search lies outside the component. -/
theorem not_straddle (t : Tree) (lo x y key : Nat) {c : Component}
    (vx : lo ≤ x ∧ x < lo + leaves t) (vy : lo ≤ y ∧ y < lo + leaves t)
    (mx : c ∈ forest t lo x) (my : c ∈ forest t lo y)
    (within : c.Contains key) (left : x < key) (right : key < y) : False := by
  have ox : ¬ c.Contains x := by
    intro contains
    have eq := contains_searched t lo x vx mx contains
    rw [eq] at within
    simp only [Component.Contains, Component.last, leaves] at within
    omega
  have oy : ¬ c.Contains y := by
    intro contains
    have eq := contains_searched t lo y vy my contains
    rw [eq] at within
    simp only [Component.Contains, Component.last, leaves] at within
    omega
  have sides := same_side t lo x y vx vy mx my ox oy
  unfold Component.Contains at within
  omega

/-- Relative to any accessed key in a persistent component, all searches
lie weakly on one side. Unlike the strict interval-side statement, this
includes searches to the component's own singleton leaf. -/
theorem point_side (t : Tree) (lo : Nat) (xs : List Nat) {c : Component} {key : Nat}
    (within : c.Contains key)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ xs, c ∈ forest t lo x) :
    (∀ x ∈ xs, x ≤ key) ∨ (∀ x ∈ xs, key ≤ x) := by
  classical
  by_cases allRight : ∀ x ∈ xs, key ≤ x
  · exact Or.inr allRight
  · push Not at allRight
    obtain ⟨x, hx, left⟩ := allRight
    left
    intro y hy
    by_contra right
    exact not_straddle t lo x y key (valid x hx) (valid y hy)
      (member x hx) (member y hy) within left (by omega)

end RotationBST.Geometric.GreedyASS.Reference
