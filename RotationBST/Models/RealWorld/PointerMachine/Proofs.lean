module

public import RotationBST.Models.RealWorld.PointerMachine.Definitions.Abstract

@[expose] public section
namespace RotationBST.RealWorld.PointerMachine
open Cslib.PointerMachine (Instr Runs Executes)

variable {w e : Nat}

theorem response_unique {p : Protocol w e} {s t u : State w e}
    {key : BitVec w} {a b : Nat}
    (h : Responds p s key t a) (k : Responds p s key u b) : t = u ∧ a = b :=
  h.2.1.unique k.2.1

theorem execution_unique {p : Protocol w e} {s t u : State w e}
    {xs : List (BitVec w)} {a b : Nat}
    (h : Execution p s xs t a) (k : Execution p s xs u b) : t = u ∧ a = b := by
  induction h generalizing u b with
  | nil => cases k; exact ⟨rfl, rfl⟩
  | cons h rest ih =>
    cases k with
    | cons k more =>
      obtain ⟨rfl, rfl⟩ := response_unique h k
      obtain ⟨rfl, rfl⟩ := ih more
      exact ⟨rfl, rfl⟩

theorem execution_append {p : Protocol w e} {s t u : State w e}
    {xs ys : List (BitVec w)} {a b : Nat}
    (h : Execution p s xs t a) (k : Execution p t ys u b) :
    Execution p s (xs ++ ys) u (a + b) := by
  induction h with
  | nil => simpa using k
  | cons h _ ih => simpa [Nat.add_assoc] using Execution.cons h (ih k)

/-- Following either child uses one actual instruction and leaves the heap unchanged. -/
theorem down_effect (s : State w e) (side : Fin 2) (record : Record w e)
    (h : s.deref 0 = some record) :
    (down side).effect s = s.setPtr 0 (record.ptr side) := by
  simp [down, Instr.effect, h]

theorem down_runs (s : State w e) (side : Fin 2) (hpc : s.pc = 0) :
    Runs [down side, .halt] s (effects [down side] s) 1 := by
  apply Relation.RelatesInSteps.single
  simp [Cslib.PointerMachine.step, hpc, effects, down, Instr.next]

/-- Both subtree representation witnesses are retained by navigation. -/
theorem down_left_refines {s : State w e} {l r : Tree w} {x : Nat × BitVec w}
    (h : Represents s.heap (.node l x r)) (cursor : s.ptr 0 = some x.1) :
    (effects [down 0] s).ptr 0 = root l ∧
      Represents (effects [down 0] s).heap l := by
  obtain ⟨⟨record, hr, hl, _, _⟩, hleft, _⟩ := h
  have hd : s.deref 0 = some record := by
    simp [Cslib.PointerMachine.State.deref, cursor, hr]
  simp [effects, down_effect s 0 record hd, Cslib.PointerMachine.State.setPtr, hl, hleft]

/-- Replacing records outside a represented subtree preserves its representation. -/
theorem represents_frame {h k : List (Record w e)} {t : Tree w}
    (rep : Represents h t) (agree : ∀ a ∈ addresses t, k[a]? = h[a]?) :
    Represents k t := by
  induction t with
  | nil => trivial
  | node l x r il ir =>
    obtain ⟨⟨record, hr, hl, hh, hk⟩, rl, rr⟩ := rep
    have mem : addresses (.node l x r) = addresses l ++ x.1 :: addresses r := by
      simp [addresses, LabelledTree.inorder]
    refine ⟨⟨record, ?_, hl, hh, hk⟩, il rl ?_, ir rr ?_⟩
    · rw [agree x.1 (by simp [mem]), hr]
    · intro a ha; exact agree a (by simp [mem, ha])
    · intro a ha; exact agree a (by simp [mem, ha])

/-- The straight-line rotation executes five instructions; halt is a sixth. -/
theorem rotateRight_runs (s : State w e) (hpc : s.pc = 0) :
    Runs (rotateRight ++ [.halt]) s (effects rotateRight s) 5 := by
  let s1 := { (Instr.loadPtr 1 0 0).effect s with pc := s.pc + 1 }
  let s2 := { (Instr.loadPtr 2 1 1).effect s1 with pc := s1.pc + 1 }
  let s3 := { (Instr.storePtr 0 0 2).effect s2 with pc := s2.pc + 1 }
  let s4 := { (Instr.storePtr 1 1 0).effect s3 with pc := s3.pc + 1 }
  let s5 := { (Instr.movePtr 0 1).effect s4 with pc := s4.pc + 1 }
  have h1 : Cslib.PointerMachine.step (rotateRight ++ [.halt]) s = some s1 := by
    simp [Cslib.PointerMachine.step, rotateRight, hpc, Instr.next, s1]
  have h2 : Cslib.PointerMachine.step (rotateRight ++ [.halt]) s1 = some s2 := by
    simp [Cslib.PointerMachine.step, rotateRight, s1, s2, hpc, Instr.next]
  have h3 : Cslib.PointerMachine.step (rotateRight ++ [.halt]) s2 = some s3 := by
    simp [Cslib.PointerMachine.step, rotateRight, s1, s2, s3, hpc, Instr.next]
  have h4 : Cslib.PointerMachine.step (rotateRight ++ [.halt]) s3 = some s4 := by
    simp [Cslib.PointerMachine.step, rotateRight, s1, s2, s3, s4, hpc, Instr.next]
  have h5 : Cslib.PointerMachine.step (rotateRight ++ [.halt]) s4 = some s5 := by
    simp [Cslib.PointerMachine.step, rotateRight, s1, s2, s3, s4, s5, hpc, Instr.next]
  have run1 : Runs (rotateRight ++ [.halt]) s s1 1 := .single h1
  exact ((run1.tail _ _ _ _ h2).tail _ _ _ _ h3).tail _ _ _ _ h4 |>.tail _ _ _ _ h5

end RotationBST.RealWorld.PointerMachine
