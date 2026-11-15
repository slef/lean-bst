module

public import RotationBST.Models.RealWorld.Compiler.Abstract
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBSTTests.CompiledBST
open RotationBST RealWorld
open RealWorld.Compiler

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Search a three-node tree, mark the visit, exercise all scalar and metadata
instructions, return to the root, and finish. The same code serves every request. -/
def controller : Machine 1 3 18 where
  entry := 0
  code pc := match pc.val with
    | 0 => .query 0 1
    | 1 => .key 1 2
    | 2 => .branch 0 1 3 4
    | 3 => .bst .downLeft 6
    | 4 => .branch 1 0 5 6
    | 5 => .bst .downRight 6
    | 6 => .mark 7
    | 7 => .literal 2 1 8
    | 8 => .store 0 2 9
    | 9 => .load 2 0 10
    | 10 => .add 2 2 2 11
    | 11 => .sub 2 2 2 12
    | 12 => .copy 2 0 13
    | 13 => .branch 0 1 14 15
    | 14 => .bst .upLeft 17
    | 15 => .branch 1 0 16 17
    | 16 => .bst .upRight 17
    | _ => .finish

def label (addr key : Nat) : Linked.Label 8 1 :=
  (addr, fun i => if i = 0 then BitVec.ofNat 8 key else 0)

def cursor : Linked.Cursor 8 1 :=
  ⟨.node (.node .nil (label 1 1) .nil) (label 0 2) (.node .nil (label 2 3) .nil), []⟩

def initial : Target 8 1 3 :=
  ⟨boundary 18, fun r => if r = 0 ∨ r = 1 then some 0 else none, fun _ => 0,
    [Linked.node (some 1) (some 2) none (label 0 2),
     Linked.node none none (some 0) (label 1 1),
     Linked.node none none (some 0) (label 2 3)]⟩

def sourceInitial : RealWorld.State 8 1 3 18 :=
  ⟨cursor.map decode, fun _ => 0, 0, false, none⟩

/-- The integration fixture satisfies the full source/target invariant. -/
theorem initial_image : Image sourceInitial initial := by
  refine ⟨cursor, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · constructor
    · constructor
      · intro r a ha
        fin_cases r <;> simp [initial] at ha <;> subst a <;> decide
      · intro rec mem f a ha
        simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;>
          fin_cases f <;> simp [Linked.node] at ha <;> subst a <;> decide
    · simp [initial, cursor, Linked.Represents, Linked.root, Linked.parent, label]
    · trivial
    · decide
    · intro a
      simp [initial, cursor, Linked.addresses, LabelledCursor.Config.tree,
        LabelledCursor.plug, LabelledTree.inorder, label]
      omega
    · simp [cursor, Linked.keys, LabelledCursor.Config.tree, LabelledCursor.plug,
        LabelledTree.Ordered, LabelledTree.inorder, label]
    · rfl
    · rfl
    · simp [cursor]
  · intro i; rfl
  · decide

def serve (key : BitVec 8) (s : Target 8 1 3) : Target 8 1 3 :=
  match Compiler.accept (l := 18) key s with
  | none => s
  | some input => Linked.run (compile controller) 100 input

def first := serve 1 initial
def second := serve 3 first

example : first.pc = boundary 18 ∧ first.ptr 0 = some 0 := by decide
example : (first.heap[1]).data 1 = 1 := by decide
example : second.pc = boundary 18 ∧ second.ptr 0 = some 0 := by decide
example : (second.heap[2]).data 1 = 1 ∧ (second.heap[1]).data 1 = 1 := by decide
example : second.data (queryReg 3) = 3 ∧ second.data (userReg (2 : Fin 3)) = 3 := by decide
example : second.heap.length = initial.heap.length := by decide
example : (compile (w := 8) controller).length = 436 := by decide

/-- Real charged execution for both requests, without restarting or changing code. -/
example : ∃ time, Compiler.Responds controller initial 1 first time := by
  let input := (Compiler.accept (l := 18) 1 initial).getD initial
  have acc : Compiler.accept (l := 18) 1 initial = some input := by rfl
  have halted : (compile (w := 8) controller)[(Linked.run (compile controller) 100 input).pc]? =
      some .halt := by rfl
  obtain ⟨time, _, run⟩ := Linked.run_executes (compile controller) 100 input halted
  exact ⟨time, input, acc, run⟩

example : ∃ time, Compiler.Responds controller first 3 second time := by
  let input := (Compiler.accept (l := 18) 3 first).getD first
  have acc : Compiler.accept (l := 18) 3 first = some input := by rfl
  have halted : (compile (w := 8) controller)[(Linked.run (compile controller) 100 input).pc]? =
      some .halt := by rfl
  obtain ⟨time, _, run⟩ := Linked.run_executes (compile controller) 100 input halted
  exact ⟨time, input, acc, run⟩

-- An unmarked finish cannot successfully halt, even after a preceding visit.
def unmarked : Machine 1 3 1 := ⟨fun _ => .finish, 0⟩
def unmarkedInput : Target 8 1 3 :=
  { initial.setData (seenReg 3) 1 with pc := entry 1 }
example : (Linked.run (compile unmarked) 12 unmarkedInput).pc = trap 1 := by decide

-- A failed mark goes to the nonhalting trap.
def wrongMark : Machine 1 3 2 := ⟨fun pc => if pc = 0 then .mark 1 else .finish, 0⟩
def wrongInput : Target 8 1 3 := { initial.setData (queryReg 3) 7 with pc := entry 2 }
example : (Linked.run (compile wrongMark) 12 wrongInput).pc = trap 2 := by decide

-- Rotation blocks are relocated away from address zero, and their final
-- halt is replaced by a charged continuation to mark and finish.
def rotating (right : Bool) : Machine 1 3 4 where
  entry := 0
  code pc := match pc.val with
    | 0 => .literal 0 7 1
    | 1 => .bst (if right then .rotateRightChild else .rotateLeftChild) 2
    | 2 => .mark 3
    | _ => .finish

def rotationInput (right : Bool) : Target 8 1 3 :=
  ⟨entry 4, fun r => if r = 0 then some 1 else if r = 1 then some 0 else none,
    fun i => if i = queryReg 3 then (if right then 3 else 1) else 0,
    [Linked.node (if right then none else some 1) (if right then some 1 else none)
      none (label 0 2), Linked.node none none (some 0) (label 1 (if right then 3 else 1))]⟩

def rotated (right : Bool) := Linked.run (compile (rotating right)) 50 (rotationInput right)
example : (rotated false).pc = boundary 4 ∧ (rotated false).ptr 1 = some 1 := by decide
example : (rotated true).pc = boundary 4 ∧ (rotated true).ptr 1 = some 1 := by decide
example : ((rotated false).heap[0]).ptr 2 = some 1 := by decide
example : ((rotated true).heap[1]).ptr 2 = none := by decide
example : (rotated true).data (userReg (0 : Fin 3)) = 7 := by decide

#print axioms RotationBST.RealWorld.Compiler.execution_simulation
#print axioms RotationBST.RealWorld.Compiler.storage_preserved
end RotationBSTTests.CompiledBST
