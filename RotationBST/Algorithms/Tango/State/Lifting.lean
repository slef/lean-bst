module

public import RotationBST.Algorithms.Tango.State.Fringe

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Region

/-- Rotations within an auxiliary component transport all component marks.
The entire marked fringe, including every lower component, stays identical. -/
theorem lift_rotate {a b : Tree} (rotation : Rotate a b) (s : MarkedTree)
    (hs : shape s.region = a) :
    ∃ u : MarkedTree, shape u.region = b ∧ s.fringe = u.fringe ∧ Rotate s.tree u.tree := by
  induction rotation generalizing s with
  | right =>
    cases s with
    | nil => simp [region, shape] at hs
    | node l r cl cr =>
      cases cl
      · cases l with
        | nil => simp [region, shape] at hs
        | node a b ca cb =>
          refine ⟨.node a (.node b r cb cr) ca false, ?_, ?_, Rotate.right⟩
          · cases ca <;> cases cb <;> cases cr <;> simp [region, shape] at hs ⊢ <;> tauto
          · simp [fringe, List.append_assoc]
      · simp [region, shape] at hs
  | left =>
    cases s with
    | nil => simp [region, shape] at hs
    | node l r cl cr =>
      cases cr
      · cases r with
        | nil => simp [region, shape] at hs
        | node b c cb cc =>
          refine ⟨.node (.node l b cl cb) c false cc, ?_, ?_, Rotate.left⟩
          · cases cl <;> cases cb <;> cases cc <;> simp [region, shape] at hs ⊢ <;> tauto
          · simp [fringe, List.append_assoc]
      · simp [region, shape] at hs
  | inLeft rotation ih =>
    cases s with
    | nil => simp [region, shape] at hs
    | node l r cl cr =>
      cases cl
      · have hl := (Tree.node.inj hs).1
        obtain ⟨u, hu, hf, ht⟩ := ih l hl
        refine ⟨.node u r false cr, ?_, ?_, Rotate.inLeft ht⟩
        · have hr := (Tree.node.inj hs).2
          cases cr <;> simp [region, shape] at hr ⊢ <;> simp [hu, hr]
        · simp [fringe, hf]
      · have hn := (Tree.node.inj hs).1
        simp only [ite_true, shape] at hn
        rw [← hn] at rotation
        cases rotation
  | inRight rotation ih =>
    cases s with
    | nil => simp [region, shape] at hs
    | node l r cl cr =>
      cases cr
      · have hr := (Tree.node.inj hs).2
        obtain ⟨u, hu, hf, ht⟩ := ih r hr
        refine ⟨.node l u cl false, ?_, ?_, Rotate.inRight ht⟩
        · have hl := (Tree.node.inj hs).1
          cases cl <;> simp [region, shape] at hl ⊢ <;> simp [hu, hl]
        · simp [fringe, hf]
      · have hn := (Tree.node.inj hs).2
        simp only [ite_true, shape] at hn
        rw [← hn] at rotation
        cases rotation

theorem lift_rotations {a b : Tree} {cost : Nat} (rotations : Rotations a b cost)
    (s : MarkedTree) (hs : shape s.region = a) :
    ∃ u : MarkedTree, shape u.region = b ∧ s.fringe = u.fringe ∧ Rotations s.tree u.tree cost := by
  induction rotations generalizing s with
  | refl => exact ⟨s, hs, rfl, .refl⟩
  | step first _ ih =>
    obtain ⟨v, hv, hf, hr⟩ := lift_rotate first s hs
    obtain ⟨u, hu, hfu, hru⟩ := ih v hv
    exact ⟨u, hu, hf.trans hfu, .step hr hru⟩

end RotationBST.Tango.MarkedTree
