module

public import RotationBST.Structures.HeavyPath.Paired.Push
public import RotationBST.Structures.HeavyPath.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate LabelledCursor

/-- All ancestors are consumed in one physical trace. The finger stays on
the endpoint between consecutive pushes and ends at the root of the pair. -/
theorem build_trace {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks)
    (ds : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, cs.map Frame.erase ++ ds⟩
      ⟨(Stacks.build weight cs p).tree, ds⟩ (Stacks.buildCost weight cs p) := by
  induction cs generalizing p with
  | nil => exact .refl
  | cons frame cs ih =>
    exact (push_trace weight frame p (cs.map Frame.erase ++ ds)).append (ih (p.push weight frame))

theorem build_valid {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).Valid := by
  induction cs generalizing p with
  | nil => exact valid
  | cons frame cs ih =>
    exact ih (push_valid valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf]))

theorem build_amortized {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    Stacks.buildCost weight cs p + (Stacks.build weight cs p).potential ≤ 23 * cs.length + p.potential := by
  induction cs generalizing p with
  | nil => simp [Stacks.buildCost, Stacks.build]
  | cons frame cs ih =>
    have first := push_amortized valid (nonnegative frame (by simp))
    have later := ih (push_valid valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf]))
    simp only [Stacks.buildCost, Stacks.build, List.length_cons]
    omega

theorem build_mass {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).mass = p.mass + (cs.map (frameMass weight)).sum := by
  induction cs generalizing p with
  | nil => simp [Stacks.build]
  | cons frame cs ih =>
    rw [Stacks.build, ih (push_valid valid (nonnegative frame (by simp)))
      (by intro f hf; exact nonnegative f (by simp [hf])),
      push_mass valid (nonnegative frame (by simp))]
    simp [add_assoc]

/-- The final root has precisely the original endpoint's inorder rank. -/
theorem build_lower_size {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks) :
    (Stacks.build weight cs p).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset (cs.map Frame.erase) := by
  induction cs generalizing p with
  | nil => simp [Stacks.build, Pointer.offset]
  | cons frame cs ih =>
    rw [Stacks.build, ih, push_lower_size]
    cases frame <;> simp [Pointer.offset, Frame.erase, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Canonical extraction followed by paired-stack construction. Off-path
subtrees are retained as opaque fringe payloads; recursive balancing of those
subtrees is a subsequent step of the simulation. -/
theorem extract_build {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    let q := extract weight t
    let p := Stacks.build weight q.context Stacks.empty
    ∃ x cost, q.focus = .node .nil x .nil ∧ p.Valid ∧
      weight x + p.mass = HeavyPath.mass weight t ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨p.tree, []⟩ cost ∧
      cost + p.potential ≤ 24 * q.context.length ∧
      (Pointer.Config.mk p.tree []).key? = q.erase.key? := by
  dsimp only
  obtain ⟨x, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  let cs := (extract weight t).context
  have charges : ∀ frame ∈ cs, 0 ≤ frameMass weight frame := by
    intro frame mem
    exact ((HeavyPath.Results.extract_positive positive).2 frame mem).le
  have down := HeavyPath.Results.extract_trace weight nonempty
  have up := build_trace weight cs Stacks.empty []
  have joined : Pointer.Trace ⟨t.erase, []⟩
      ⟨(Stacks.build weight cs Stacks.empty).tree, []⟩
      (cs.length + Stacks.buildCost weight cs Stacks.empty) := by
    apply down.append
    simpa only [Config.erase, focus, LabelledTree.erase, List.append_nil,
      Stacks.empty, Stacks.tree, Layer.decode, Icing.decode, Regulars.attach,
      WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror] using up
  refine ⟨x, _, focus, build_valid cs empty_valid charges, ?_, joined, ?_, ?_⟩
  · have partition := HeavyPath.Results.extract_mass weight t
    rw [focus] at partition
    rw [build_mass cs empty_valid charges]
    simpa only [HeavyPath.mass, zero_add, add_zero, Stacks.mass, Stacks.empty,
      Layer.decode, Regulars.attach, Icing.decode, WeightedTree.mass] using partition.symm
  · have bound := build_amortized cs empty_valid charges
    have emptyPotential : Stacks.empty.potential = 0 := rfl
    rw [emptyPotential, Nat.add_zero] at bound
    change cs.length + Stacks.buildCost weight cs Stacks.empty +
      (Stacks.build weight cs Stacks.empty).potential ≤ 24 * cs.length
    omega
  · simp only [Pointer.Config.key?, Stacks.tree, Pointer.offset,
      Config.erase, focus, LabelledTree.erase, Tree.size, Nat.zero_add, Nat.add_zero]
    rw [build_lower_size]
    change some (0 + _) = _
    simp only [Nat.zero_add]

end RotationBST.HeavyPath.Paired
