module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Updates.Dictionary.AbstractBridge

@[expose] public section

/-! Splay updates as an instance of the dictionary model
(`Models/Dictionary/Definitions/Abstract`). Each splay access, insertion and
deletion is a dictionary step on trees without data whose main cost is at
most a constant times splay's own charge, one unit plus its rotations. -/
namespace RotationBST.Splay.Updates.Results

theorem dictionary_access (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ c, Dictionary.Step t.unit (.access x) (run t x).1.unit c 0 ∧ c ≤ 2 * ((run t x).2 + 1) :=
  Updates.dictionary_access t x hx

theorem dictionary_insert (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    ∃ c, Dictionary.Step t.unit (.insert k) (insert t k).1.unit c 0 ∧
      c ≤ 3 * ((insert t k).2 + 1) :=
  Updates.dictionary_insert t k hk

theorem dictionary_delete (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ c, Dictionary.Step t.unit (.delete x) (delete t x).1.unit c 0 ∧
      c ≤ 2 * ((delete t x).2 + 1) :=
  Updates.dictionary_delete t x hx

end RotationBST.Splay.Updates.Results

/-- info: abstract audit passed for `RotationBST.Splay.Updates.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Updates.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Dictionary.Definitions.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Updates.Algorithm.Abstract]
