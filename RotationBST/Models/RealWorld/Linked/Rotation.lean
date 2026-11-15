module

public import RotationBST.Models.RealWorld.Linked.Heap
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Pointer Instr step)
variable {w e regs : Nat}

def write (h : List (Record w e regs)) (p : Pointer) (f : Fin 3) (v : Pointer) :=
  match p with
  | none => h
  | some a => h.modify a (fun r => { r with ptr := Function.update r.ptr f v })

@[simp] theorem write_length (h : List (Record w e regs)) (p : Pointer) (f : Fin 3) (v : Pointer) :
    (write h p f v).length = h.length := by
  cases p <;> simp [write]

@[simp] theorem write_get (h : List (Record w e regs)) (p : Pointer) (f : Fin 3)
    (v : Pointer) (z : Nat) :
    (write h p f v)[z]? = (h[z]?).map (fun r =>
      if p = some z then { r with ptr := Function.update r.ptr f v } else r) := by
  cases p <;> simp [write, List.getElem?_modify]

/-- The five field writes common to both rotation directions. -/
def pivot (h : List (Record w e regs)) (x y : Nat) (beta g : Pointer) (side other : Fin 3) :=
  write (write (write (write (write h (some y) side beta) beta 2 (some y))
    (some x) other (some y)) (some y) 2 (some x)) (some x) 2 g

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem rotate_root_effect (s : State w e regs) (side other : Fin 3) (x y : Nat)
    (rx ry : Record w e regs) (cur : s.ptr 0 = some x)
    (hx : s.heap[x]? = some rx) (hy : s.heap[y]? = some ry)
    (px : rx.ptr 2 = some y) (py : ry.ptr 2 = none) :
    let t := run (rotate side other) 18 (start s)
    t.heap = pivot s.heap x y (rx.ptr other) none side other ∧
      t.ptr 0 = some x ∧ t.ptr 1 = some x := by
  cases hb : rx.ptr other <;>
    simp [run, step, rotate, start, Instr.effect, Instr.next,
    Cslib.PointerMachine.State.deref, Cslib.PointerMachine.State.setPtr,
    Cslib.PointerMachine.State.modify, cur, hx, hy, px, py, pivot, write, hb]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem rotate_inner_effect (s : State w e regs) (side other : Fin 3) (x y g : Nat)
    (rx ry rg : Record w e regs) (cur : s.ptr 0 = some x)
    (hx : s.heap[x]? = some rx) (hy : s.heap[y]? = some ry)
    (hg : s.heap[g]? = some rg) (px : rx.ptr 2 = some y) (py : ry.ptr 2 = some g)
    (gx : g ≠ x) (gy : g ≠ y) (gb : rx.ptr other ≠ some g) :
    let t := run (rotate side other) 18 (start s)
    t.heap = write (pivot s.heap x y (rx.ptr other) (some g) side other) (some g)
      (if rg.ptr 0 = some y then 0 else 1) (some x) ∧
      t.ptr 0 = some x ∧ t.ptr 1 = s.ptr 1 := by
  cases hb : rx.ptr other <;>
    simp [hb] at gb <;>
    simp [run, step, rotate, start, Instr.effect, Instr.next,
      Cslib.PointerMachine.State.deref, Cslib.PointerMachine.State.setPtr,
      Cslib.PointerMachine.State.modify, cur, hx, hy, hg, px, py, pivot, write,
      hb, Ne.symm gx, Ne.symm gy, gb]
  all_goals split_ifs <;> simp_all

theorem write_other (h : List (Record w e regs)) (p v : Pointer) (f : Fin 3) (z : Nat)
    (ne : p ≠ some z) : (write h p f v)[z]? = h[z]? := by simp [ne]

theorem pivot_other (h : List (Record w e regs)) (x y z : Nat) (beta g : Pointer)
    (side other : Fin 3) (hx : x ≠ z) (hy : y ≠ z) :
    (pivot h x y beta g side other)[z]? =
      (h[z]?).map (fun r => if beta = some z then
        { r with ptr := Function.update r.ptr 2 (some y) } else r) := by
  simp [pivot, hx, hy, Function.comp_def]

theorem context_reconnect {h : List (Record w e regs)} {cs : List (LabelledCursor.Frame (Label w e))}
    {p q : Pointer} (rep : Context h p cs) (nd : (outside cs).Nodup) :
    Context (write h (parent cs) (contextSide cs) q) q cs := by
  cases cs with
  | nil => trivial
  | cons f cs =>
    cases f with
    | left x r =>
      simp only [outside, List.nodup_cons, List.nodup_append] at nd
      refine ⟨?_, represents_congr rep.2.1 ?_, context_congr rep.2.2 ?_⟩
      · simp [parent, contextSide, rep.1, node]
        funext i; fin_cases i <;> simp
      · intro z hz
        exact write_other h _ _ _ z (by simp [parent]; grind)
      · intro z hz
        exact write_other h _ _ _ z (by simp [parent]; grind)
    | right l x =>
      simp only [outside, List.nodup_cons, List.nodup_append] at nd
      refine ⟨?_, represents_congr rep.2.1 ?_, context_congr rep.2.2 ?_⟩
      · simp [parent, contextSide, rep.1, node]
        funext i; fin_cases i <;> simp
      · intro z hz
        exact write_other h _ _ _ z (by simp [parent]; grind)
      · intro z hz
        exact write_other h _ _ _ z (by simp [parent]; grind)

end RotationBST.RealWorld.Linked
