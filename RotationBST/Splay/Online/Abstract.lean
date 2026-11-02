module

public import RotationBST.Splay.Online.AbstractBridge

@[expose] public section

namespace RotationBST.Splay

/-- The certificate used by the bundled online algorithm. -/
theorem step_correct (t : Tree) (x : Nat) (valid : x < t.size) :
    Access t (run t x).1 x (run t x).2 :=
  (run_correct t x valid).1

/-- The splay algorithm is online and uses no persistent state beyond its tree. -/
def algorithm : Algorithm where
  step _ t x := run t x
  correct _ t x hx := step_correct t x hx

end RotationBST.Splay
