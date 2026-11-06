module

public import RotationBST.Models.Labelled.Cursor.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LabelledCursor

theorem erase_plug {α : Type} (cs : List (Frame α)) (t : LabelledTree α) :
    (plug cs t).erase = Pointer.plug (cs.map Frame.erase) t.erase := by
  induction cs generalizing t with
  | nil => rfl
  | cons frame cs ih => cases frame <;> simp only [plug, ih, List.map_cons, Frame.erase,
      Pointer.plug, LabelledTree.erase]

theorem erase_tree {α : Type} (c : Config α) : c.tree.erase = c.erase.tree :=
  erase_plug c.context c.focus

theorem perform_erase {α : Type} (op : Multifinger.Opcode) (c : Config α) :
    (perform op c).map Config.erase = Multifinger.perform op c.erase := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => cases op <;> rfl
  | node l entry r =>
    cases op with
    | downLeft => cases l <;> rfl
    | downRight => cases r <;> rfl
    | upLeft | upRight | rotateLeftChild | rotateRightChild =>
      cases cs with
      | nil => rfl
      | cons frame cs => cases frame <;> rfl

theorem perform_physical {α : Type} {op : Multifinger.Opcode} {s t : Config α}
    (step : perform op s = some t) : Pointer.Step s.erase t.erase := by
  apply Multifinger.perform_sound
  simpa only [step, Option.map_some] using (perform_erase op s).symm

theorem write_erase {α : Type} {s t : Config α} {entry : α}
    (write : s.write entry = some t) : t.erase = s.erase := by
  rcases s with ⟨focus, cs⟩
  cases focus <;> simp only [Config.write, reduceCtorEq, Option.some.injEq] at write
  subst t
  rfl

end RotationBST.LabelledCursor
