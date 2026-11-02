module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Height-weighted credits on minimal nodes along first-child edges. Other
child roots carry only the fixed node reserve; their descendants still carry
finger credits. The flag records whether to charge this root as a finger root. -/
def repairCredit : Nat → Bool → Multiway → Nat
  | _, _, .nil => 0
  | h, root, .two a b =>
      6 + (if root then 3 * h else 0) + repairCredit (h - 1) true a + repairCredit (h - 1) false b
  | h, _, .three a b c =>
      6 + repairCredit (h - 1) true a + repairCredit (h - 1) false b + repairCredit (h - 1) false c
  | h, _, .four a b c d =>
      6 + repairCredit (h - 1) true a + repairCredit (h - 1) false b +
        repairCredit (h - 1) false c + repairCredit (h - 1) false d

/-- Height read from the first-child path; balance makes it the common height. -/
def fingerHeight : Multiway → Nat
  | .nil => 0
  | .two a _ | .three a _ _ | .four a _ _ _ => fingerHeight a + 1

/-- Credits evaluated at the tree's own height, including after contraction. -/
def storedCredit (root : Bool) (t : Multiway) : Nat := repairCredit (fingerHeight t) root t

/-- Repeated minimum extraction, retaining the finger state between operations. -/
def extractMany : Nat → Multiway → Multiway × Nat
  | 0, t => (t, 0)
  | n + 1, t =>
      let step := extractView t
      let rest := extractMany n step.1
      (rest.1, step.2 + rest.2)

end RotationBST.Arboral.Split.Multiway.Finger
