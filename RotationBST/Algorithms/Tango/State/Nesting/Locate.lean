module

public import RotationBST.Algorithms.Tango.State.Nesting.Offsets
public import RotationBST.Algorithms.Tango.State.Context.Position

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem matching_member {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (matching : List.Forall₂ R xs ys) {y : β} (member : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction matching with
  | nil => simp at member
  | @cons a b xs ys hab h ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨x, hx, hxy⟩ := ih member
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-- A nonempty fringe component in the reference marking identifies a concrete
component of the maintained BST, at the same key offset and with the same
nesting, together with the context needed to update it. -/
theorem locate_reference_component_at (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) {p : Nat × MarkedTree}
    (member : p ∈ (canonical reference 0 past).fringeAt 0) (nonempty : p.2 ≠ .nil) :
    ∃ child : MarkedTree, ∃ fs : List Context.Frame,
      (p.1, child) ∈ s.fringeAt 0 ∧ child.nesting = p.2.nesting ∧
      fs ≠ [] ∧ Context.Boundary fs ∧ Context.plug fs child = s ∧ Context.offset fs 0 = p.1 := by
  have matching := fringeAt_matching maintained.2 0
  obtain ⟨q, hq, offset, nested⟩ := matching_member matching member
  have childNonempty : q.2 ≠ .nil := by
    intro empty
    have hn : p.2.nesting = ComponentNesting.empty := by rw [← nested, empty]; rfl
    cases hp : p.2 with
    | nil => exact nonempty hp
    | node l r cl cr => rw [hp] at hn; cases hn
  obtain ⟨fs, hn, hb, hp, ho⟩ := Context.locate_fringeAt s 0 q.2 q.1 hq childNonempty
  refine ⟨q.2, fs, ?_, nested, hn, hb, hp, ho.trans offset⟩
  simpa only [← offset] using hq

/-- The position-free version of component localization. -/
theorem locate_reference_component (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) {p : Nat × MarkedTree}
    (member : p ∈ (canonical reference 0 past).fringeAt 0) (nonempty : p.2 ≠ .nil) :
    ∃ child : MarkedTree, ∃ fs : List Context.Frame,
      (p.1, child) ∈ s.fringeAt 0 ∧ child.nesting = p.2.nesting ∧
      fs ≠ [] ∧ Context.Boundary fs ∧ Context.plug fs child = s := by
  obtain ⟨child, fs, hm, hn, hf, hb, hp, _⟩ :=
    locate_reference_component_at s reference past maintained member nonempty
  exact ⟨child, fs, hm, hn, hf, hb, hp⟩

end RotationBST.Tango.MarkedTree
