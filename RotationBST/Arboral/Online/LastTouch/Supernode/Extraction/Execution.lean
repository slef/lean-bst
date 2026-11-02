module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Progress

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Every stage of recursive extraction is an exact BST rotation execution,
with canonical nested states retained in its holes. -/
theorem extract_execution (fuel : Nat) (keys : Finset Nat) {P : Finset Point}
    {lo : Nat} {state : Nested} (represented : Represents P lo state) :
    (extract fuel keys lo state).1.Valid P lo ∧
      Rotations state.tree (extract fuel keys lo state).1.region.tree (extract fuel keys lo state).2 := by
  induction fuel generalizing lo state with
  | zero => exact ⟨represented, .refl⟩
  | succ fuel ih =>
    simp only [extract]
    split
    · exact ⟨represented, .refl⟩
    · cases state with
      | empty => exact ⟨represented, .refl⟩
      | layer parent children =>
        have selected := selectParent_spec represented keys
        have attached := Assembly.fill_spec (fun child start => extract fuel keys start child)
          (fun child start valid => ih valid) selected.1
        exact ⟨attached.1, selected.2.1.append attached.2⟩

end RotationBST.Arboral.Online.Supernode
