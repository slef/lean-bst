module

import RotationBST.Audit.Check
public import RotationBST.Models.RealWorld.Compiler.AbstractBridge

@[expose] public section
namespace RotationBST.RealWorld.Compiler.Results

/-- Compile every successful source request into one fixed pointer-machine
program, with charged dispatch, request setup and halt. -/
theorem response {w f r l : Nat} (p : Machine f r l)
    {s u : State w f r l} {t : Target w f r} {key : BitVec w} {time cost : Nat}
    (width : 0 < w) (image : Image s t)
    (source : RealWorld.Responds p s key u time cost) :
    ∃ v actual, actual ≤ 19 * time + 3 ∧ Responds p t key v actual ∧ Image u v :=
  response_simulation p width image source

/-- The compiled code is reused unchanged across the whole online sequence. -/
theorem execution {w f r l : Nat} (p : Machine f r l)
    {s u : State w f r l} {t : Target w f r} {xs : List (BitVec w)} {time cost : Nat}
    (width : 0 < w) (image : Image s t)
    (source : RealWorld.Execution p s xs u time cost) :
    ∃ v actual, actual ≤ 19 * time + 3 * xs.length ∧ Execution p t xs v actual ∧ Image u v :=
  execution_simulation p width image source

/-- Source time proportional to BST work transfers with explicit constants. -/
theorem proportional_time {w f r l : Nat} (p : Machine f r l)
    {s u : State w f r l} {t : Target w f r} {key : BitVec w} {time cost constant : Nat}
    (width : 0 < w) (image : Image s t)
    (source : RealWorld.Responds p s key u time cost) (bound : time ≤ constant * (cost + 1)) :
    ∃ v actual, actual ≤ (19 * constant + 3) * (cost + 1) ∧
      Responds p t key v actual ∧ Image u v := proportional_response p width image source bound

/-- No execution of compiled code allocates or removes a record. -/
theorem storage {w f r l : Nat} (p : Machine f r l) {s t : Target w f r} {n : Nat}
    (run : Cslib.PointerMachine.Runs (compile p) s t n) : t.heap.length = s.heap.length :=
  storage_preserved p run

/-- Code size is fixed by the source controller, independent of tree size. -/
theorem code_size {w f r l : Nat} (p : Machine f r l) :
    (compile (w := w) p).length = 24 * l + 4 := compile_length p

/-- Concrete successful requests have unique states and exact instruction counts. -/
theorem deterministic {w f r l : Nat} {p : Machine f r l} {s t u : Target w f r}
    {key : BitVec w} {a b : Nat} (h : Responds p s key t a) (k : Responds p s key u b) :
    t = u ∧ a = b := response_unique h k

end RotationBST.RealWorld.Compiler.Results

/-- info: abstract audit passed for `RotationBST.RealWorld.Compiler.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.RealWorld.Compiler.Results allowing [
  RotationBST.Models.RealWorld.Compiler.Definitions.Abstract,
  RotationBST.Models.RealWorld.Definitions.Abstract,
  RotationBST.Models.RealWorld.Linked.Definitions.Abstract,
  RotationBST.Models.RealWorld.PointerMachine.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  CslibFrontier.Computability.PointerMachine.Defs]
