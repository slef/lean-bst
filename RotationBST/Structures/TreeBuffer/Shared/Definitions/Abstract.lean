module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Persistent node identities into a single shared labelled tree. As in the
multifinger model, keys denote existing nodes; zipper views below are semantic
witnesses rather than independent copies or runtime searches. -/
structure State (α : Type) (fingers : Nat) where
  tree : LabelledTree (Nodes.Entry α)
  position : Fin fingers → Nat

def State.Valid {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α) : Prop :=
  s.tree.map Nodes.Entry.routing = IntervalMetadata.label s.tree.erase 0 ∧
  s.tree.map Nodes.Entry.payload = Metadata.label data s.tree.erase 0 ∧
  ∀ i, s.position i < s.tree.erase.size

/-- The selected finger's local view of the one shared tree. -/
def View {α : Type} {fingers : Nat} (s : State α fingers) (i : Fin fingers)
    (c : LabelledCursor.Config (Nodes.Entry α)) (entry : Nodes.Entry α) : Prop :=
  c.tree = s.tree ∧ c.read = some entry ∧ entry.key = s.position i

/-- Navigation changes only the selected node identity. Reads keep all fingers
fixed; writes and maintained rotations update the shared tree in place. -/
inductive Step {α : Type} {fingers : Nat} : State α fingers → Fin fingers → State α fingers →
    Option (Cells.Event α) → Nat → Prop where
  | move {s : State α fingers} {i : Fin fingers} {c next : LabelledCursor.Config (Nodes.Entry α)}
      {entry nextEntry : Nodes.Entry α} (op : Multifinger.Opcode) :
      View s i c entry → LabelledCursor.perform op c = some next → Pointer.Move c.erase next.erase →
      next.read = some nextEntry →
      Step s i ⟨next.tree, Function.update s.position i nextEntry.key⟩ none 1
  | navigate {s : State α fingers} {i : Fin fingers} {c next : LabelledCursor.Config (Nodes.Entry α)}
      {entry nextEntry : Nodes.Entry α} (target : Nat) :
      View s i c entry → Nodes.route target c = some (4, next) → next.read = some nextEntry →
      Step s i ⟨next.tree, Function.update s.position i nextEntry.key⟩ none 4
  | read {s : State α fingers} {i : Fin fingers} {c : LabelledCursor.Config (Nodes.Entry α)}
      {entry : Nodes.Entry α} {value : α} :
      View s i c entry → Nodes.readCell c = some (1, value) →
      Step s i s (some (.read (s.position i) value)) 1
  | write {s : State α fingers} {i : Fin fingers} {c next : LabelledCursor.Config (Nodes.Entry α)}
      {entry : Nodes.Entry α} (value : α) :
      View s i c entry → Nodes.writeCell c value = some (1, next) →
      Step s i ⟨next.tree, s.position⟩ (some (.write (s.position i) value)) 1
  | rotate {s : State α fingers} {i : Fin fingers} {before after : Nodes.State α}
      {entry : Nodes.Entry α} (side : IntervalMetadata.Maintenance.Side) :
      View s i before.cursor entry → Nodes.maintain side before = some after →
      Step s i ⟨after.cursor.tree, s.position⟩ none 15

/-- Event lists are specifications. The runtime state keeps only the fixed
number of fingers, the node fields, and the local operation's scratch words. -/
inductive Trace {α : Type} {fingers : Nat} : State α fingers → State α fingers →
    List (Cells.Event α) → Nat → Prop where
  | refl {s : State α fingers} : Trace s s [] 0
  | step {s t u : State α fingers} {i : Fin fingers} {event : Option (Cells.Event α)}
      {events : List (Cells.Event α)} {cost rest : Nat} :
      Step s i t event cost → Trace t u events rest → Trace s u (event.toList ++ events) (cost + rest)

end RotationBST.TreeBuffer.Shared
