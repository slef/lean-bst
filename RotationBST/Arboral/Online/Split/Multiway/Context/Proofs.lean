module

public import RotationBST.Arboral.Online.Split.Multiway.Context.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Edges.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Context

theorem Frame.rotations (f : Frame) {s t : Multiway} {cost : Nat}
    (steps : Rotations s.binary t.binary cost) :
    Rotations (f.fill s).binary (f.fill t).binary cost := by
  cases f with
  | twoLeft b => exact steps.inLeft
  | twoRight a => exact steps.inRight
  | threeFirst b c => exact steps.inLeft
  | threeMiddle a c => exact steps.inLeft.inRight
  | threeLast a b => exact steps.inRight.inRight
  | fourFirst b c d => exact steps.inLeft.inLeft
  | fourSecond a c d => exact steps.inRight.inLeft
  | fourThird a b d => exact steps.inLeft.inRight
  | fourLast a b c => exact steps.inRight.inRight

/-- Enclosing depth adds no rotations when lifting a local edit. -/
theorem plug_rotations (fs : List Frame) {s t : Multiway} {cost : Nat}
    (steps : Rotations s.binary t.binary cost) :
    Rotations (plug fs s).binary (plug fs t).binary cost := by
  induction fs generalizing s t with
  | nil => exact steps
  | cons f fs ih => exact ih (f.rotations steps)

theorem Frame.nodes (f : Frame) (t : Multiway) :
    (f.fill t).nodes = t.nodes + (f.fill .nil).nodes := by
  cases f <;> simp only [Frame.fill, Multiway.nodes] <;> omega

/-- The entire node reserve splits into the local reserve and a fixed context. -/
theorem plug_nodes (fs : List Frame) (t : Multiway) :
    (plug fs t).nodes = t.nodes + (plug fs .nil).nodes := by
  induction fs generalizing t with
  | nil => simp [plug, Multiway.nodes]
  | cons f fs ih =>
    simp only [plug]
    rw [ih (f.fill t), ih (f.fill .nil), Frame.nodes f t]
    omega

theorem Frame.balanced (f : Frame) {h : Nat} {t : Multiway}
    (siblings : f.Valid h) (focus : Balanced h t) : Balanced (h + 1) (f.fill t) := by
  cases f with
  | twoLeft b => exact .two focus siblings
  | twoRight a => exact .two siblings focus
  | threeFirst b c => exact .three focus siblings.1 siblings.2
  | threeMiddle a c => exact .three siblings.1 focus siblings.2
  | threeLast a b => exact .three siblings.1 siblings.2 focus
  | fourFirst b c d => exact .four focus siblings.1 siblings.2.1 siblings.2.2
  | fourSecond a c d => exact .four siblings.1 focus siblings.2.1 siblings.2.2
  | fourThird a b d => exact .four siblings.1 siblings.2.1 focus siblings.2.2
  | fourLast a b c => exact .four siblings.1 siblings.2.1 siblings.2.2 focus

/-- Any replacement of the same local height preserves the global balance. -/
theorem plug_balanced (fs : List Frame) {h : Nat} {t : Multiway}
    (ancestors : Valid h fs) (focus : Balanced h t) : Balanced (h + fs.length) (plug fs t) := by
  induction fs generalizing h t with
  | nil => exact focus
  | cons f fs ih =>
    have result := ih ancestors.2 (f.balanced ancestors.1 focus)
    simpa only [plug, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using result


/-- The exact local reserve decrease survives every enclosing context. -/
theorem plug_nodes_drop (fs : List Frame) {s t : Multiway} {drop : Nat}
    (decrease : t.nodes + drop = s.nodes) :
    (plug fs t).nodes + drop = (plug fs s).nodes := by
  rw [plug_nodes fs t, plug_nodes fs s]
  omega

/-- Reassembly preserves both the concrete rotation cost and any node reserve charge. -/
theorem edit_spec (fs : List Frame) (s : Multiway) (operation : Multiway → Multiway × Nat)
    (steps : Rotations s.binary (operation s).1.binary (operation s).2)
    (reserve : (operation s).1.nodes ≤ s.nodes) :
    Rotations (plug fs s).binary (edit fs s operation).1.binary (edit fs s operation).2 ∧
      (edit fs s operation).2 = (operation s).2 ∧
      (edit fs s operation).1.nodes + (s.nodes - (operation s).1.nodes) = (plug fs s).nodes := by
  refine ⟨plug_rotations fs steps, rfl, ?_⟩
  apply plug_nodes_drop fs
  omega

end RotationBST.Arboral.Split.Multiway.Context
