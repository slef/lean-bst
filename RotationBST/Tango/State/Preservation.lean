module

public import RotationBST.Tango.State.Lifting

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region

theorem fringeAt_snd (s : MarkedTree) (lo : Nat) : (s.fringeAt lo).map Prod.snd = s.fringe := by
  induction s generalizing lo with
  | nil => rfl
  | node l r cl cr il ir => cases cl <;> cases cr <;> simp [fringeAt, fringe, il, ir]

theorem fringeAt_holes (s : MarkedTree) (lo : Nat) :
    (s.fringeAt lo).map (fun p => (p.1, p.2.tree)) = s.region.holes lo := by
  induction s generalizing lo with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp [fringeAt, region, holes, Pointer.Lazy.Skeleton.tree, il, ir]

theorem detached_fringeAt (s : MarkedTree) (lo : Nat) :
    s.detached lo = (s.fringeAt lo).flatMap (fun p => p.2.components p.1) := by
  induction s generalizing lo with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp [fringeAt, detached, components, il, ir, List.append_assoc]

private theorem pair_list_ext {α β : Type} (s t : List (α × β))
    (hf : s.map Prod.fst = t.map Prod.fst) (hs : s.map Prod.snd = t.map Prod.snd) : s = t := by
  have zip (l : List (α × β)) : List.zip (l.map Prod.fst) (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p ps ih => simp [ih]
  rw [← zip s, hf, hs, zip]

theorem fringeAt_eq {s t : MarkedTree} (same : s.fringe = t.fringe) (lo : Nat) :
    s.fringeAt lo = t.fringeAt lo := by
  have hfr : s.region.fringe = t.region.fringe := by rw [← fringe_tree, ← fringe_tree, same]
  have holes := (same_of_fringe hfr lo).2.2
  apply pair_list_ext
  · have h := congrArg (List.map Prod.fst) holes
    rw [← fringeAt_holes, ← fringeAt_holes] at h
    simpa only [List.map_map, Function.comp_def] using h
  · rw [fringeAt_snd, fringeAt_snd, same]

theorem detached_eq {s t : MarkedTree} (same : s.fringe = t.fringe) (lo : Nat) :
    s.detached lo = t.detached lo := by
  rw [detached_fringeAt, detached_fringeAt, fringeAt_eq same lo]

/-- Reshaping the root auxiliary tree preserves the complete component
partition, including all absolute key sets of lower components. -/
theorem component_keys_eq {s t : MarkedTree} (same : s.fringe = t.fringe) (lo : Nat) :
    ((s.components lo).map fun p => p.2.keys p.1) =
      ((t.components lo).map fun p => p.2.keys p.1) := by
  have hfr : s.region.fringe = t.region.fringe := by rw [← fringe_tree, ← fringe_tree, same]
  have keys := (same_of_fringe hfr lo).2.1
  have lengths := congrArg List.length hfr
  simp only [Pointer.Lazy.Skeleton.fringe_length] at lengths
  simp only [components, List.map_append, detached_eq same lo]
  congr 1
  cases s <;> cases t
  · rfl
  · simp [region, Pointer.Lazy.Skeleton.size] at lengths
  · simp [region, Pointer.Lazy.Skeleton.size] at lengths
  · simpa only [rootComponent, List.map_singleton, List.singleton_inj] using keys

end RotationBST.Tango.MarkedTree
