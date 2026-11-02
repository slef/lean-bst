module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Selection
public import RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Execution

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Independent child extractions spend only the credits stored in their
original holes; their costs and remaining credits add under exposed keys. -/
theorem Assembly.fill_credit {P : Finset Point} (expand : Nested → Nat → Assembly × Nat)
    (paid : ∀ state lo, Represents P lo state →
      (expand state lo).2 + (expand state lo).1.credit ≤ state.credit)
    {assembly : Assembly} {lo : Nat} (valid : assembly.Valid P lo) :
    (assembly.fill expand lo).2 + (assembly.fill expand lo).1.credit ≤ assembly.credit := by
  induction assembly generalizing lo with
  | hole state => exact paid state lo valid
  | node left right il ir =>
    have l := il valid.1
    have r := ir valid.2
    simp only [Assembly.fill, Assembly.credit]
    omega

/-- All recursive row extraction is paid from the old nested potential.
This holds at every depth, including the complete size-bounded execution. -/
theorem extract_credit (fuel : Nat) (keys : Finset Nat) {P : Finset Point}
    {lo : Nat} {state : Nested} (represented : Represents P lo state) :
    (extract fuel keys lo state).2 + (extract fuel keys lo state).1.credit ≤ state.credit := by
  induction fuel generalizing lo state with
  | zero => simp only [extract, Assembly.credit, Nat.zero_add, le_refl]
  | succ fuel ih =>
    simp only [extract]
    split
    · simp only [Assembly.credit, Nat.zero_add, le_refl]
    · cases state with
      | empty => simp only [Assembly.credit, Nat.zero_add, le_refl]
      | layer parent children =>
        have selected := selectParent_spec represented keys
        have parentPaid := selectParent_credit represented keys
        have childPaid := Assembly.fill_credit (fun child start => extract fuel keys start child)
          (fun child start valid => ih valid) selected.1
        dsimp only
        omega

end RotationBST.Arboral.Online.Supernode
