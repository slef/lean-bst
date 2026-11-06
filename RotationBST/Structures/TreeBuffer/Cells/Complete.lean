module

public import RotationBST.Structures.TreeBuffer.Cells.Transfers
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

/-- Finish reading a pending scan with no additional rotations. The bound
includes every navigation primitive and every read. -/
theorem finish_read {α : Type} (s : Scan.State) (valid : s.Valid) (data : Nat → α) :
    ∃ t work, Trace ⟨s, data⟩ ⟨t, data⟩
      (s.requests.map fun x => Event.read x (data x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * s.tree.size := by
  obtain ⟨t, work, run, done, _⟩ := Scan.finish s valid
  exact ⟨t, work, read_complete run valid done data, done, by simpa using run.cost valid⟩

/-- Finish writing a pending scan, setting exactly its remaining keys. -/
theorem finish_write {α : Type} (s : Scan.State) (valid : s.Valid) (target data : Nat → α) :
    ∃ t final work, Trace ⟨s, data⟩ ⟨t, final⟩
      (s.requests.map fun x => Event.write x (target x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * s.tree.size ∧
      ∀ x, final x = if x ∈ s.requests then target x else data x := by
  obtain ⟨t, work, run, done, _⟩ := Scan.finish s valid
  obtain ⟨final, writes, effect⟩ := write_complete run valid done target data
  exact ⟨t, final, work, writes, done, by simpa using run.cost valid, effect⟩

/-- A whole-buffer read from any existing node. Empty trees have no cursor;
their empty stream is handled separately by the reflexive trace. -/
theorem read_all {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (data : Nat → α) :
    ∃ t work, Trace ⟨⟨tree, position, 0, false⟩, data⟩ ⟨t, data⟩
      ((List.range tree.size).map fun x => Event.read x (data x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size := by
  simpa [Scan.State.requests, ← List.range_eq_range'] using
    finish_read (α := α) ⟨tree, position, 0, false⟩ ⟨present, Nat.zero_le _⟩ data

/-- A whole-buffer write leaves all nonexisting keys unchanged. The target
function specifies the input stream, rather than an extra runtime array. -/
theorem write_all {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (target data : Nat → α) :
    ∃ t final work, Trace ⟨⟨tree, position, 0, false⟩, data⟩ ⟨t, final⟩
      ((List.range tree.size).map fun x => Event.write x (target x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size ∧
      ∀ x, final x = if x < tree.size then target x else data x := by
  simpa [Scan.State.requests, ← List.range_eq_range'] using
    finish_write (α := α) ⟨tree, position, 0, false⟩ ⟨present, Nat.zero_le _⟩ target data

theorem read_all_reverse {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (data : Nat → α) :
    ∃ t work, Trace ⟨⟨tree, position, tree.size, true⟩, data⟩ ⟨t, data⟩
      ((List.range tree.size).reverse.map fun x => Event.read x (data x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size := by
  simpa [Scan.State.requests, ← List.range_eq_range'] using
    finish_read (α := α) ⟨tree, position, tree.size, true⟩ ⟨present, Nat.le_refl _⟩ data

end RotationBST.TreeBuffer.Cells
