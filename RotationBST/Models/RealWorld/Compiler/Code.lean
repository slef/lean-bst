module

public import RotationBST.Models.RealWorld.Compiler.Relocation

@[expose] public section
namespace RotationBST.RealWorld.Compiler
variable {w f r l : Nat}

theorem block_lookup (p : Machine f r l) (pc : Fin l) (k : Nat) (hk : k < stride) :
    (compile (w := w) p)[address pc + k]? =
      some (((block (w := w) (address pc) (p.code pc))[k]?).getD (.goto (trap l))) := by
  have hi : address pc + k < boundary l := by
    simp only [address, boundary, stride] at *
    have := pc.isLt
    omega
  have hb : address pc + k < boundary l + 4 := by omega
  have hd : (address pc + k) / stride = pc.val := by
    simp only [address, stride] at *; omega
  have hm : (address pc + k) % stride = k := by
    simp only [address, stride] at *; omega
  simp only [compile, List.getElem?_ofFn]
  simp [hb, hi, hd, hm]

theorem boundary_lookup (p : Machine f r l) :
    (compile (w := w) p)[boundary l]? = some .halt := by
  simp only [compile, List.getElem?_ofFn]
  simp

theorem entry_lookup (p : Machine f r l) :
    (compile (w := w) p)[entry l]? =
      some (.op (.literal 0) (seenReg r) (zeroReg r) (zeroReg r)) := by
  simp only [compile, List.getElem?_ofFn]
  simp [entry]

theorem entry_next_lookup (p : Machine f r l) :
    (compile (w := w) p)[entry l + 1]? = some (.goto (address p.entry)) := by
  simp only [compile, List.getElem?_ofFn]
  simp [entry, Nat.add_assoc]

theorem block_length (base : Nat) (i : Instruction f r l) :
    (block (w := w) base i).length ≤ stride := by
  cases i <;> simp [block, stride]
  rename_i op next
  cases op <;> simp [Linked.program, Linked.move, Linked.rotate]

/-- The compiler contains every relocated primitive at the correct address. -/
theorem primitive_contains (p : Machine f r l) (pc next : Fin l) (op : Multifinger.Opcode)
    (source : p.code pc = .bst op next) :
    Contains (compile (w := w) p) (Linked.program op) (address pc) (address next) := by
  intro k i hi
  have hk := List.getElem?_eq_some_iff.mp hi |>.1
  have bound : (Linked.program (w := w) (e := f) (regs := r + 4) op).length ≤ stride := by
    cases op <;> simp [Linked.program, Linked.move, Linked.rotate, stride]
  have lookup := block_lookup (w := w) p pc k (by omega)
  simpa [source, block, List.getElem?_map, hi] using lookup

end RotationBST.RealWorld.Compiler
