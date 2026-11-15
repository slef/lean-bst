module

import RotationBST.Models.RealWorld.Abstract

open RotationBST RotationBST.RealWorld

private def program : Machine 1 2 2 where
  code i := if i.val = 0 then .mark 1 else .finish
  entry := 0

private def boundary : State 4 1 2 2 where
  cursor := ⟨.node .nil ⟨3, fun _ => 0⟩ .nil, []⟩
  regs := fun _ => 0
  request := 0
  seen := false
  pc := none

private def active : State 4 1 2 2 := { boundary with request := 3, pc := some 0 }

example : accept program 3 boundary = some active := rfl
example : accept program 2 active = none := rfl
example : tick program active = some ({ active with seen := true, pc := some 1 }, none) := rfl
example : eval (.mark 1) { active with request := 2 } = none := rfl
example : eval .finish active = none := rfl
example : eval (.bst .upLeft 1) active = none := rfl
example : eval (.add 0 0 1 1) { active with regs := fun _ => 15 } =
    some ({ active with regs := Function.update (fun _ : Fin 2 => (15 : BitVec 4)) 0 14, pc := some 1 }, none) := rfl
example : eval (.store 0 1 1) active = some ({ active with pc := some 1 }, none) := by
  simp [eval, active, boundary, LabelledCursor.Config.read, LabelledCursor.Config.write]

/-- The known-key singleton program takes two scalar steps and no BST steps. -/
example : Responds program boundary 3 { active with seen := true, pc := none } 2 0 := by
  refine ⟨active, rfl, ?_, rfl⟩
  apply Run.cons (t := { active with seen := true, pc := some 1 }) (out := none) (by rfl)
  exact Run.cons (out := none) (by rfl) Run.nil

example : accept program 2 { active with seen := true, pc := none } =
    some { active with request := 2, seen := false, pc := some 0 } := rfl
