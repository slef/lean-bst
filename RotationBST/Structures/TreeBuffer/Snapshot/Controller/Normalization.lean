module

public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Normalization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Controller
open Multifinger

theorem Run.append {s t u : State} {first last : List Opcode} (left : Run s first t) (right : Run t last u) :
    Run s (first ++ last) u := by
  induction left with
  | refl => exact right
  | silent step _ ih => exact .silent step (ih right)
  | instruction step _ ih => exact .instruction step (ih right)

/-- The local controller emits exactly the recorded normalizer, starting in
any ancestor context and returning to the same spine-depth counter. -/
theorem recordFuel_run (fuel : Nat) (t : Tree) (enough : work t ≤ fuel)
    (cs : List Pointer.Frame) (depth : Nat) :
    Run ⟨⟨t, cs⟩, depth, .scan⟩ (recordFuel fuel t) ⟨⟨vine t.size, cs⟩, depth, .ascend⟩ := by
  induction fuel generalizing t cs depth with
  | zero =>
    cases t with
    | nil => exact .silent rfl .refl
    | node l r => simp only [work] at enough; omega
  | succ fuel ih =>
    cases t with
    | nil => exact .silent rfl .refl
    | node l r =>
      cases l with
      | nil =>
        cases r with
        | nil => exact .silent rfl .refl
        | node a b =>
          have remaining : work (.node a b) ≤ fuel := by simp only [work, Tree.size] at enough ⊢; omega
          have inner := ih (.node a b) remaining (.right .nil :: cs) (depth + 1)
          have nonempty := vine_nonempty (Tree.node a b).size (by simp only [Tree.size]; omega)
          cases canonical : vine (Tree.node a b).size with
          | nil => exact False.elim (nonempty canonical)
          | node c d =>
            rw [canonical] at inner
            have outward : Run ⟨⟨.node .nil (.node a b), cs⟩, depth, .scan⟩ [.downRight]
                ⟨⟨.node a b, .right .nil :: cs⟩, depth + 1, .scan⟩ := .instruction rfl .refl
            have inward : Run ⟨⟨.node c d, .right .nil :: cs⟩, depth + 1, .ascend⟩ [.upRight]
                ⟨⟨.node .nil (.node c d), cs⟩, depth, .ascend⟩ := .instruction rfl .refl
            have all := (outward.append inner).append inward
            have outer : (Tree.node .nil (.node a b)).size = (Tree.node a b).size + 1 := by simp only [Tree.size]; omega
            simpa only [recordFuel, List.cons_append, List.nil_append, List.append_assoc, outer, vine, canonical] using all
      | node a b =>
        have remaining : work (.node a (.node b r)) ≤ fuel := by simp only [work, Tree.size] at enough ⊢; omega
        have inner := ih (.node a (.node b r)) remaining cs depth
        have size : (Tree.node a (.node b r)).size = (Tree.node (.node a b) r).size := by simp only [Tree.size]; omega
        rw [size] at inner
        exact .instruction rfl (.instruction rfl inner)

theorem normalization (t : Tree) :
    Run ⟨⟨t, []⟩, 0, .scan⟩ (record t) ⟨⟨vine t.size, []⟩, 0, .ascend⟩ :=
  recordFuel_run (work t) t le_rfl [] 0

theorem normalized_halts (t : Tree) : tick ⟨⟨vine t.size, []⟩, 0, .ascend⟩ = none := rfl

end RotationBST.TreeBuffer.Snapshot.Controller
