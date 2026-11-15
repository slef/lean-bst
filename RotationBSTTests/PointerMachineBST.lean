module

public import RotationBST.Models.RealWorld.PointerMachine.Abstract

@[expose] public section
namespace RotationBSTTests.PointerMachineBST
open RotationBST.RealWorld.PointerMachine

-- Root 4 has left child 2, whose right child 3 is transferred by rotation.
-- Every record also has a metadata word which must survive the two writes.
def record (key tag : Nat) (l r : Option Nat) : Record 8 1 :=
  ⟨fun f => if f = 0 then l else r,
   fun f => BitVec.ofNat 8 (if f = 0 then key else tag)⟩

def initial : State 8 1 :=
  ⟨0, fun _ => some 0, fun _ => 0,
    [record 4 40 (some 1) none, record 2 20 none (some 2), record 3 30 none none]⟩

def finalState := effects rotateRight initial

example : finalState.ptr 0 = some 1 := by decide
example : (finalState.heap[0]).ptr 0 = some 2 := by decide
example : (finalState.heap[1]).ptr 1 = some 0 := by decide
example : (finalState.heap[2]).ptr 0 = none := by decide
example : finalState.heap.map (fun r => r.data 1) = [40, 20, 30] := by decide
example : finalState.heap.length = initial.heap.length := by decide
example : Cslib.PointerMachine.Executes (rotateRight ++ [.halt]) initial finalState 6 := by
  refine ⟨5, Results.rotation_time initial rfl, ?_, rfl⟩
  rfl

-- Input injection preserves the heap and pointer registers; arithmetic is modular.
example : (accept 7 9 initial).heap = initial.heap := rfl
example : (accept 7 9 initial).ptr = initial.ptr := rfl
example : (words 8).evalOp .add 255 1 = 0 := by decide

#print axioms RotationBST.RealWorld.PointerMachine.Results.rotation
#print axioms RotationBST.RealWorld.PointerMachine.Results.causal
end RotationBSTTests.PointerMachineBST
