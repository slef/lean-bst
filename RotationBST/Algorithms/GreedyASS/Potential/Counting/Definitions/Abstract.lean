module

public import RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting

/-- Actual purple items contained in one reference component. -/
def purpleKeys (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (c : Reference.Component) : Finset Nat :=
  (P.image Prod.fst).filter fun x => c.Contains x ∧ itemColor t lo searches P x = some .purple

def blueKeys (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (c : Reference.Component) : Finset Nat :=
  (P.image Prod.fst).filter fun x => c.Contains x ∧ itemColor t lo searches P x = some .blue

def leftBlueKeys (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (c : Reference.Component) : Finset Nat :=
  (P.filter fun q => c.Contains q.1 ∧ Items.LeftExternal P q ∧
    color t lo searches P q = some .blue).image Prod.fst

def rightBlueKeys (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (c : Reference.Component) : Finset Nat :=
  (P.filter fun q => c.Contains q.1 ∧ Items.RightExternal P q ∧
    color t lo searches P q = some .blue).image Prod.fst

end RotationBST.Geometric.GreedyASS.Potential.Counting
