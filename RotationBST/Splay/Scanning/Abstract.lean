module

import RotationBST.AbstractAudit.Check
public import RotationBST.Splay.Scanning.AbstractBridge

@[expose] public section

/-! Sequential access (the scanning theorem, ST85 Theorem 9), from any initial
shape. Constants are deliberately generous. The proof pairs red ancestors and
uses a quadratic right-spine potential, adapted from Kakimura--Terai (2026),
https://arxiv.org/abs/2609.19746. All markings are ghost state in the analysis. -/
namespace RotationBST.Splay.Results

/-- Accessing every key once in increasing order takes linear total cost. -/
theorem scanning (t : Tree) :
    algorithm.totalCost t (List.range t.size) ≤ 14 * t.size :=
  Scanning.total_bound t

/-- The same scan has a linear-cost conventional pointer implementation,
preserving the exact final splay tree. -/
theorem pointer_scanning (t : Tree) :
    ∃ k, k ≤ 40 * t.size ∧
      Pointer.Execution t (List.range t.size) (algorithm.runFrom [] t (List.range t.size)).1 k :=
  Scanning.pointer_bound t

end RotationBST.Splay.Results

-- The readable foundations below contain the model, executable algorithm and
-- its correctness certificate; the potential proof is outside this boundary.
#check_bst_abstract RotationBST.Splay.Results allowing [RotationBST.Model.Abstract,
  RotationBST.Online.Abstract, RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract, RotationBST.Splay.Online.Abstract]
