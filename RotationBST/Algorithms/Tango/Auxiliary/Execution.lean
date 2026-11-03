module

public import RotationBST.Algorithms.Tango.Auxiliary.Analysis

@[expose] public section
namespace RotationBST.Region
open Pointer.Lazy.Skeleton

theorem inflate_reconstruct_append (s : Region) (rest : List Tree) :
    inflate (shape s) (s.fringe ++ rest) = s := by
  induction s generalizing rest with
  | hole t => rfl
  | node l r il ir =>
    simp only [shape, inflate, fringe, List.append_assoc, il, shape_size,
      ← fringe_length l, List.drop_left, ir]

theorem inflate_reconstruct (s : Region) : inflate (shape s) s.fringe = s := by
  simpa only [List.append_nil] using inflate_reconstruct_append s []

theorem shape_fringe_injective {s t : Region} (hs : shape s = shape t)
    (hf : s.fringe = t.fringe) : s = t := by
  rw [← inflate_reconstruct s, hs, hf, inflate_reconstruct]

/-- The executable reconstruction has exactly the lifted splay's rotations. -/
theorem auxiliaryRun_correct (s : Region) (k : Nat) (valid : k < s.size) :
    shape (auxiliaryRun s k).1 = (Splay.run (shape s) k).1 ∧
      s.fringe = (auxiliaryRun s k).1.fringe ∧
      Rotations s.tree (auxiliaryRun s k).1.tree (auxiliaryRun s k).2 := by
  have access := (Splay.run_correct (shape s) k (by rwa [shape_size])).1
  obtain ⟨u, hu, hf, rotations⟩ := lift_rotations access.1 s rfl
  have reconstruction : inflate (Splay.run (shape s) k).1 s.fringe = u := by
    rw [← hu, hf, inflate_reconstruct]
  simpa only [auxiliaryRun, reconstruction] using And.intro hu (And.intro hf rotations)

theorem auxiliaryRun_access (s : Region) (x : Nat) (valid : x ∈ s.keys 0) :
    Access s.tree (auxiliaryRun s (index s 0 x)).1.tree x (auxiliaryRun s (index s 0 x)).2 := by
  obtain ⟨u, hu, hf, access⟩ := auxiliary_splay s x valid
  have reconstruction : inflate (Splay.run (shape s) (index s 0 x)).1 s.fringe = u := by
    rw [← hu, hf, inflate_reconstruct]
  simpa only [auxiliaryRun, reconstruction] using access

theorem auxiliaryRun_bound (s : Region) (k : Nat) (valid : k < s.size) :
    ((auxiliaryRun s k).2 : ℝ) + auxiliaryPotential (auxiliaryRun s k).1 - auxiliaryPotential s ≤
      3 * Real.logb 2 s.size + 1 := by
  have shape_eq := (auxiliaryRun_correct s k valid).1
  have bound := Splay.Updates.unit_access (shape s) k (by rwa [shape_size])
  change ((Splay.run (shape s) k).2 : ℝ) + auxiliaryPotential (auxiliaryRun s k).1 - auxiliaryPotential s ≤ _
  simpa only [← shape_eq, Splay.Updates.unitPotential, auxiliaryPotential, shape_size] using bound

end RotationBST.Region
