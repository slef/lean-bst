module

import RotationBST.Audit.Check
public import RotationBST.Structures.PrefixSum.AbstractBridge

@[expose] public section
namespace RotationBST.PrefixSum.Results

/-- Every cached prefix agrees with the defining rectangular sum. -/
theorem cached_prefix (f : Nat → Nat → Nat) (width height a b : Nat)
    (ha : a ≤ height) (hb : b ≤ width) :
    get (build f width height) a b = sumPrefix f a b := build_get f width height a b ha hb

/-- Four cached values answer a rectangle query exactly, including empty
rectangles and rectangles touching any edge of the stored matrix. -/
theorem rectangular_sum (f : Nat → Nat → Nat) (width height a b c d : Nat)
    (hab : a ≤ b) (hb : b ≤ height) (hcd : c ≤ d) (hd : d ≤ width) :
    rectangle (build f width height) a b c d = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico c d, f i j :=
  rectangle_build f width height a b c d hab hb hcd hd

end RotationBST.PrefixSum.Results

/-- info: abstract audit passed for `RotationBST.PrefixSum.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PrefixSum.Results allowing [
  RotationBST.Structures.PrefixSum.Definitions.Abstract]
