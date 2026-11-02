module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Abstract

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Recursively expose the current row. Fuel bounds recursion through nested
subtrees; untouched intervals stop immediately and preserve their states. -/
def extract : Nat → Finset Nat → Nat → Nested → Assembly × Nat
  | 0, _, _, state => (.hole state, 0)
  | fuel + 1, keys, lo, state =>
      if keys ∩ Finset.Ico lo (lo + state.tree.size) = ∅ then (.hole state, 0)
      else match state with
      | .empty => (.hole .empty, 0)
      | .layer parent children =>
          let selected := selectParent parent children lo keys
          let attached := selected.1.fill (fun child start => extract fuel keys start child) lo
          (attached.1, selected.2 + attached.2)

/-- A subtree has at most its number of keys in nonempty recursive layers.
The extraction algorithm uses only the stored state and the current row. -/
def extractRow (keys : Finset Nat) (lo : Nat) (state : Nested) : Assembly × Nat :=
  extract (state.tree.size + 1) keys lo state

end RotationBST.Arboral.Online.Supernode
