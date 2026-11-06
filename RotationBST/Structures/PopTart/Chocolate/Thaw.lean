module

public import RotationBST.Structures.PopTart.Chocolate.Invariant
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Every valid icing can refill an empty regular list. -/
theorem thaw_valid {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    ∃ rest, icing.thaw = some rest ∧ rest.Valid level := by
  cases icing with
  | base crumb => exact ⟨_, rfl, trivial, valid, fun _ => ⟨_, rfl⟩⟩
  | solid crumb tail =>
    obtain ⟨perfect, nonnegative, tailValid, dominates⟩ := valid
    cases perfect with
    | node pb pc =>
      exact ⟨_, rfl, ⟨⟨pb, nonnegative.1⟩, ⟨pc, nonnegative.2⟩⟩, tailValid, by intro h; cases h⟩
  | frozen carry old tail =>
    obtain ⟨perfect, nonnegative, oldValid, tailValid, thick, dominates⟩ := valid
    cases perfect with
    | node pb pc =>
      exact ⟨_, rfl, ⟨⟨pb, nonnegative.1⟩, ⟨pc, nonnegative.2⟩⟩, oldValid, tailValid,
        (by intro h; cases h), thick⟩

theorem thawed_valid {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {rest : Layer} (thawed : icing.thaw = some rest) : rest.Valid level := by
  obtain ⟨other, same, result⟩ := thaw_valid valid
  rw [thawed] at same
  cases same
  exact result

theorem thaw_fringe {icing : Icing} {rest : Layer} (thawed : icing.thaw = some rest) :
    rest.decode.fringe = icing.decode.fringe := by
  cases icing with
  | base crumb => cases thawed; rfl
  | solid crumb tail =>
    cases crumb with
    | leaf => cases thawed
    | node b c =>
      cases thawed
      simp only [Layer.decode, Icing.decode, Regulars.attach, fringe, List.append_assoc]
  | frozen carry old tail =>
    cases carry with
    | leaf => cases thawed
    | node b c =>
      cases thawed
      simp only [Layer.decode, Icing.decode, Regulars.attach, fringe, List.append_assoc]

theorem thaw_potential {icing : Icing} {rest : Layer} (thawed : icing.thaw = some rest) :
    rest.potential = icing.potential := by
  cases icing with
  | base crumb => cases thawed; rfl
  | solid crumb tail => cases crumb <;> cases thawed; simp [Layer.potential, Icing.potential, Regulars.potential]
  | frozen carry old tail => cases carry <;> cases thawed; simp [Layer.potential, Icing.potential, Regulars.potential]

/-- Thawing uses at most two right rotations, preserving every frozen interior. -/
theorem thaw_trace {icing : Icing} {rest : Layer} (thawed : icing.thaw = some rest) :
    Pointer.Trace ⟨icing.decode.tree, []⟩ ⟨rest.decode.tree, []⟩ icing.thawCost := by
  cases icing with
  | base crumb => cases thawed; exact .refl
  | solid crumb tail =>
    cases crumb with
    | leaf => cases thawed
    | node b c => cases thawed; exact .step .downLeft (.step .rotateLeftChild .refl)
  | frozen carry old tail =>
    cases carry with
    | leaf => cases thawed
    | node b c =>
      cases thawed
      have first : Pointer.Trace
          ⟨.node (.node (.node b.tree c.tree) old.decode.tree) tail.decode.tree, []⟩
          ⟨.node (.node b.tree c.tree) (.node old.decode.tree tail.decode.tree), []⟩ 2 :=
        .step .downLeft (.step .rotateLeftChild .refl)
      have second : Pointer.Trace
          ⟨.node (.node b.tree c.tree) (.node old.decode.tree tail.decode.tree), []⟩
          ⟨.node b.tree (.node c.tree (.node old.decode.tree tail.decode.tree)), []⟩ 2 :=
        .step .downLeft (.step .rotateLeftChild .refl)
      exact first.append second

/-- The actual pop boundary keeps the exposed separator above the thawed tree. -/
theorem thaw_under {icing : Icing} {rest : Layer} (thawed : icing.thaw = some rest) (a : WeightedTree) :
    Pointer.Trace ⟨.node a.tree icing.decode.tree, []⟩
      ⟨.node a.tree rest.decode.tree, []⟩ icing.popCost := by
  cases icing with
  | base crumb => cases thawed; exact .refl
  | solid crumb tail =>
    cases crumb with
    | leaf => cases thawed
    | node b c =>
      cases thawed
      exact (thaw_trace (icing := .solid (.node b c) tail) rfl).inContext
        (by intro h; cases h) (by intro h; cases h) [.right a.tree]
  | frozen carry old tail =>
    cases carry with
    | leaf => cases thawed
    | node b c =>
      cases thawed
      exact (thaw_trace (icing := .frozen (.node b c) old tail) rfl).inContext
        (by intro h; cases h) (by intro h; cases h) [.right a.tree]

end RotationBST.PopTart.Chocolate
