module

public import RotationBST.Bounds.LazyFinger.PointerWalk
public import RotationBST.Models.Multifinger.PointerTrace

@[expose] public section
namespace RotationBST.LazyFinger

/-- One lazy-finger transition is exactly a persistent one-finger trace. -/
theorem multifinger_walk (t : Tree) (p x : Nat) (hp : p < t.size) (hx : x < t.size) :
    ∃ touches : List Nat, touches.length = distance t p x ∧
      Multifinger.Trace (⟨t, fun _ : Fin 1 => p⟩ : Multifinger.State 1) touches ⟨t, fun _ => x⟩ := by
  obtain ⟨a, b, treeA, treeB, keyA, keyB, trace⟩ := pointer_walk t p x hp hx
  obtain ⟨touches, length, run⟩ := Multifinger.pointer_trace trace keyA keyB
  exact ⟨touches, length, by simpa only [treeA, treeB] using run⟩

theorem multifinger_request (t : Tree) (p x : Nat) (hp : p < t.size) (hx : x < t.size) :
    Multifinger.Serves (⟨t, fun _ : Fin 1 => p⟩ : Multifinger.State 1) ⟨t, fun _ => x⟩ x
      (1 + distance t p x) := by
  obtain ⟨touches, length, run⟩ := multifinger_walk t p x hp hx
  exact ⟨⟨t, fun _ => x⟩, touches, [], 0, run, rfl, .refl, by simp only [length, List.length_nil, Nat.add_zero]⟩

/-- A fixed-tree lazy finger gives a legal multifinger request execution with
exactly the normalized lazy-finger cost, retaining its key between requests. -/
theorem multifinger_execution (t : Tree) (p : Nat) (xs : List Nat) (hp : p < t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ q : Nat, Multifinger.Execution (⟨t, fun _ : Fin 1 => p⟩ : Multifinger.State 1) xs
      ⟨t, fun _ => q⟩ (costFrom t p xs) := by
  induction xs generalizing p with
  | nil => exact ⟨p, .nil⟩
  | cons x xs ih =>
    have hx := valid x (by simp)
    obtain ⟨q, tail⟩ := ih x hx (by intro y hy; exact valid y (by simp [hy]))
    exact ⟨q, .cons (multifinger_request t p x hp hx) tail⟩

/-- With the lazy finger initially at the root, the source execution has the
all-root initialization required by the constant-factor simulator. -/
theorem multifinger_root_execution (t : Tree) (xs : List Nat) (nonempty : 0 < t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ q : Nat, Multifinger.Execution (Multifinger.initial 1 t) xs ⟨t, fun _ => q⟩ (cost t xs) := by
  cases t with
  | nil => simp [Tree.size] at nonempty
  | node l r =>
    exact multifinger_execution (.node l r) l.size xs (by simp only [Tree.size]; omega) valid

end RotationBST.LazyFinger
