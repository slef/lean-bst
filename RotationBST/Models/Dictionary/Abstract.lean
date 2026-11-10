module

import RotationBST.Audit.Check
public import RotationBST.Models.Dictionary.AbstractBridge

@[expose] public section

/-! The dictionary model: operations by rank on trees with node data, with a
main cost (search path and rotations) and a count of data edits.
`Definitions/Abstract` gives operations, moves, splices, steps, executions and
online dictionary algorithms. -/
namespace RotationBST.Dictionary.Results

variable {α : Type}

/-- Operations change the number of keys as expected. -/
theorem step_size {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    t.erase.size = op.resize s.erase.size :=
  h.size

/-- Only valid operations have steps. -/
theorem step_valid {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    op.Valid s.erase.size :=
  h.valid

/-- Node data do not affect the main cost: forgetting them keeps every step. -/
theorem step_unit {s t : LabelledTree α} {op : Op} {c e : Nat} (h : Step s op t c e) :
    Step s.erase.unit op t.erase.unit c 0 :=
  h.unit

theorem execution_unit {s t : LabelledTree α} {ops : List Op} {c e : Nat}
    (h : Execution s ops t c e) : Execution s.erase.unit ops t.erase.unit c 0 :=
  h.unit

/-- An online dictionary algorithm executes every valid sequence. -/
theorem algorithm_execution (A : Algorithm α) (t : LabelledTree α) (ops : List Op)
    (valid : Op.ValidSeq t.erase.size ops) :
    Execution t ops (A.runFrom [] t ops).1 (A.runFrom [] t ops).2.1 (A.runFrom [] t ops).2.2 :=
  A.runFrom_execution [] t ops valid

/-- Each rotation changes a depth by at most one. -/
theorem rotations_depth_reverse {s t : Tree} {k : Nat} (h : Rotations s t k) (x : Nat) :
    s.depth x ≤ t.depth x + k :=
  h.depth_le_reverse x

/-- **The rotation model embeds.** An execution of root accesses with `R`
rotations is a dictionary execution of the same accesses with main cost at
most `m + 2R`: the search path to each requested node is paid by the
rotations that bring it to the root. -/
theorem of_execution {s t : Tree} {xs : List Nat} {k : Nat} (h : RotationBST.Execution s xs t k) :
    ∃ c, Dictionary.Execution s.unit (xs.map .access) t.unit c 0 ∧ c ≤ xs.length + 2 * k :=
  Dictionary.of_execution h

/-- Searching without moving costs `∑ (1 + depth x)`, the static search cost
(`StaticTree.cost` of the shape). -/
theorem static_execution (s : LabelledTree α) (xs : List Nat) (valid : ∀ x ∈ xs, x < s.erase.size) :
    Execution s (xs.map .access) s ((xs.map fun x => s.erase.depth x + 1).sum) 0 :=
  Dictionary.static_execution s xs valid

end RotationBST.Dictionary.Results

/-- info: abstract audit passed for `RotationBST.Dictionary.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Dictionary.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Dictionary.Definitions.Abstract]
