module

public import RotationBST.Models.Multifinger.Program.Proofs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Vector

@[expose] public section
namespace RotationBST.Pointer

/-- Seven symbols encode the six primitive instructions and a padding symbol.
Padding is only for this counting argument, not a charged machine operation. -/
private def decodeStep (symbol : Fin 7) (c : Config) : Option Config :=
  match symbol.val with
  | 0 => some c
  | 1 => Multifinger.perform .downLeft c
  | 2 => Multifinger.perform .downRight c
  | 3 => Multifinger.perform .upLeft c
  | 4 => Multifinger.perform .upRight c
  | 5 => Multifinger.perform .rotateLeftChild c
  | _ => Multifinger.perform .rotateRightChild c

private def decode : List (Fin 7) → Config → Option Config
  | [], c => some c
  | symbol :: rest, c => (decodeStep symbol c).bind (decode rest)

private theorem step_code {a b : Config} (step : Step a b) :
    ∃ symbol : Fin 7, decodeStep symbol a = some b := by
  cases step with
  | downLeft => exact ⟨1, rfl⟩
  | downRight => exact ⟨2, rfl⟩
  | upLeft => exact ⟨3, rfl⟩
  | upRight => exact ⟨4, rfl⟩
  | rotateLeftChild => exact ⟨5, rfl⟩
  | rotateRightChild => exact ⟨6, rfl⟩

private theorem trace_code {a b : Config} {k : Nat} (trace : Trace a b k) :
    ∃ code : List (Fin 7), code.length = k ∧ decode code a = some b := by
  induction trace with
  | refl => exact ⟨[], rfl, rfl⟩
  | step instruction _ ih =>
    obtain ⟨symbol, first⟩ := step_code instruction
    obtain ⟨code, length, rest⟩ := ih
    exact ⟨symbol :: code, by simp only [List.length_cons, length], by simp only [decode, first, Option.bind_some, rest]⟩

private theorem decode_padding (r : Nat) (code : List (Fin 7)) (a : Config) :
    decode (List.replicate r 0 ++ code) a = decode code a := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

private theorem trace_vector {a b : Config} {k r : Nat} (trace : Trace a b k) (short : k ≤ r) :
    ∃ code : List.Vector (Fin 7) r, decode code.val a = some b := by
  obtain ⟨code, length, result⟩ := trace_code trace
  exact ⟨⟨List.replicate (r - k) 0 ++ code, by simp only [List.length_append, List.length_replicate, length]; omega⟩,
    by simpa only [decode_padding] using result⟩

/-- From a fixed cursor, at most `7^r` different endpoint keys can be reached
within `r` pointer instructions. Even paths using rotations satisfy this bound.
The source cursor must be fixed before the endpoint is chosen. -/
theorem reachable_keys_card (a : Config) (r : Nat) (keys : Finset Nat)
    (reachable : ∀ x ∈ keys, ∃ b k, Trace a b k ∧ k ≤ r ∧ b.key? = some x) :
    keys.card ≤ 7 ^ r := by
  classical
  have codes : ∀ x : keys, ∃ code : List.Vector (Fin 7) r,
      (decode code.val a).bind Config.key? = some x.val := by
    intro x
    obtain ⟨b, k, trace, short, key⟩ := reachable x.val x.property
    obtain ⟨code, result⟩ := trace_vector trace short
    exact ⟨code, by simp only [result, Option.bind_some, key]⟩
  choose encode specification using codes
  have injective : Function.Injective encode := by
    intro x y equal
    have same := (specification x).symm.trans (equal ▸ specification y)
    exact Subtype.ext (Option.some.inj same)
  have count := Fintype.card_le_of_injective encode injective
  simpa only [Fintype.card_coe, card_vector, Fintype.card_fin] using count

end RotationBST.Pointer
