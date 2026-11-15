module

public import RotationBST.Models.RealWorld.Compiler.Representation

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr)
variable {w f r l : Nat}

def updateLabel (x : Linked.Label w f) (i : Fin (f + 1)) (v : BitVec w) : Linked.Label w f :=
  (x.1, Function.update x.2 i v)

theorem addresses_plug (cs : List (LabelledCursor.Frame (Linked.Label w f)))
    {a b : Linked.Tree w f} (h : Linked.addresses a = Linked.addresses b) :
    Linked.addresses (LabelledCursor.plug cs a) = Linked.addresses (LabelledCursor.plug cs b) := by
  induction cs generalizing a b with
  | nil => exact h
  | cons frame cs ih =>
    cases frame <;> apply ih <;> simp [Linked.addresses_node, h]

theorem keys_plug (cs : List (LabelledCursor.Frame (Linked.Label w f)))
    {a b : Linked.Tree w f} (h : Linked.keys a = Linked.keys b) :
    Linked.keys (LabelledCursor.plug cs a) = Linked.keys (LabelledCursor.plug cs b) := by
  induction cs generalizing a b with
  | nil => exact h
  | cons frame cs ih => cases frame <;> apply ih <;> simp [Linked.keys, h]

/-- A metadata store changes exactly the current node's designated word.
The key, all links, and the rest of the heap remain represented. -/
theorem store_realizes {s : Target w f r} {a b : Linked.Tree w f} {x : Linked.Label w f}
    {cs : List (LabelledCursor.Frame (Linked.Label w f))}
    (h : Linked.Realizes s ⟨.node a x b, cs⟩) (i : Fin f) (src : Fin (r + 4)) :
    Linked.Realizes ((Instr.storeData (field i) 0 src).effect s)
      ⟨.node a (updateLabel x (field i) (s.data src)) b, cs⟩ := by
  have nd := (Linked.nodup_plug cs (.node a x b)).mp h.distinct
  simp only [Linked.addresses_node, List.nodup_append, List.nodup_cons,
    List.mem_append, List.mem_cons] at nd
  have effect : (Instr.storeData (field i) 0 src).effect s =
      { s with heap := s.heap.modify x.1 (fun n =>
        { n with data := Function.update n.data (field i) (s.data src) }) } := by
    simp [Instr.effect, Cslib.PointerMachine.State.modify, h.cursor, Linked.root]
  have ad : Linked.addresses (LabelledCursor.plug cs
      (.node a (updateLabel x (field i) (s.data src)) b)) =
      Linked.addresses (LabelledCursor.plug cs (.node a x b)) :=
    addresses_plug cs (by simp [updateLabel])
  have keyeq : Linked.keys (LabelledCursor.plug cs
      (.node a (updateLabel x (field i) (s.data src)) b)) =
      Linked.keys (LabelledCursor.plug cs (.node a x b)) := by
    apply keys_plug cs
    simp [Linked.keys, updateLabel, field, Fin.ext_iff]
  have valid := Instr.effect_valid (i := Instr.storeData (field i) 0 src) h.valid
  rw [effect] at valid ⊢
  refine ⟨valid, ?_, ?_, ?_, ?_, ?_, h.cursor, ?_, by simp⟩
  · refine ⟨?_, Linked.represents_congr h.focus.2.1 ?_, Linked.represents_congr h.focus.2.2 ?_⟩
    · simp [h.focus.1, updateLabel, Linked.node]
    · intro z hz
      have ne : x.1 ≠ z := by grind
      simp [ne]
    · intro z hz
      have ne : x.1 ≠ z := by grind
      simp [ne]
  · apply Linked.context_congr h.context
    intro z hz
    have ne : x.1 ≠ z := by grind
    simp [ne]
  · change (Linked.addresses (LabelledCursor.plug cs _)).Nodup
    rw [ad]; exact h.distinct
  · intro z
    simpa only [List.length_modify, LabelledCursor.Config.tree, ad] using h.covers z
  · change (Linked.keys (LabelledCursor.plug cs _)).Ordered
    rw [keyeq]; exact h.ordered
  · exact h.rootReg.trans (Linked.root_plug_congr cs rfl)

theorem decode_update (x : Linked.Label w f) (i : Fin f) (v : BitVec w) :
    decode (updateLabel x (field i) v) =
      { decode x with data := Function.update (decode x).data i v } := by
  simp only [decode, updateLabel]
  simp only [field]
  congr 1
  funext j
  simp [Function.update_apply, Fin.ext_iff]

end RotationBST.RealWorld.Compiler
