module

public import RotationBST.Tango.Paths.Geometry.Abstract
public import RotationBST.Tango.Paths.Update

@[expose] public section
namespace RotationBST.Tango

theorem rootPath_bounds {t : Tree} {lo : Nat} {xs : List Nat} (path : RootPath t lo xs) :
    ∀ x ∈ xs, lo ≤ x ∧ x < lo + t.size := by
  induction path with
  | empty => simp
  | @left l r lo xs h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Tree.size]; omega
    · have hb := ih x hx
      simp only [Tree.size]; omega
  | @right l r lo xs h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [Tree.size]; omega
    · have hb := ih x hx
      simp only [Tree.size]; omega

/-- A depth suffix of a reference path is an inorder interval of that path.
This is why a Tango depth cut can be implemented by two key-boundary splays. -/
theorem rootPath_suffix_interval {t : Tree} {lo : Nat} {xs : List Nat}
    (path : RootPath t lo xs) (k : Nat) : KeyInterval (xs.drop k) xs := by
  induction path generalizing k with
  | empty => simp [KeyInterval]
  | @left l r lo xs h ih =>
    cases k with
    | zero => exact fun _ _ _ _ _ hx _ _ => hx
    | succ k =>
      intro a ha b hb x hx hax hxb
      simp only [List.drop_succ_cons] at ha hb ⊢
      rcases List.mem_cons.mp hx with rfl | hx
      · have bound := rootPath_bounds h a (List.mem_of_mem_drop ha)
        have bound' := rootPath_bounds h b (List.mem_of_mem_drop hb)
        omega
      · exact ih k a ha b hb x hx hax hxb
  | @right l r lo xs h ih =>
    cases k with
    | zero => exact fun _ _ _ _ _ hx _ _ => hx
    | succ k =>
      intro a ha b hb x hx hax hxb
      simp only [List.drop_succ_cons] at ha hb ⊢
      rcases List.mem_cons.mp hx with rfl | hx
      · have bound := rootPath_bounds h a (List.mem_of_mem_drop ha)
        omega
      · exact ih k a ha b hb x hx hax hxb

theorem decompose_rootPath (t : Tree) (lo : Nat) (past : List Nat) :
    RootPath t lo (decomposePaths t lo past).1 := by
  induction t generalizing lo with
  | nil => exact .empty _ _
  | node l r il ir =>
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [decomposePaths, h]
      first | exact .left (.empty _ _) | exact .left (il lo) | exact .right (ir _)

private theorem rest_in_parts (d : PathDecomposition) {xs : List Nat} (h : xs ∈ d.2) :
    xs ∈ d.parts := by
  unfold PathDecomposition.parts
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

theorem decompose_referencePaths (t : Tree) (lo : Nat) (past : List Nat) :
    ∀ xs ∈ (decomposePaths t lo past).parts, ReferencePath t lo xs := by
  induction t generalizing lo with
  | nil => simp [decomposePaths, PathDecomposition.parts]
  | node l r il ir =>
    have main := decompose_rootPath (.node l r) lo past
    have lp := il lo
    have rp := ir (lo + l.size + 1)
    have lr : ∀ xs ∈ (decomposePaths l lo past).2, ReferencePath l lo xs :=
      fun xs hx => lp xs (rest_in_parts _ hx)
    have rr : ∀ xs ∈ (decomposePaths r (lo + l.size + 1) past).2,
        ReferencePath r (lo + l.size + 1) xs := fun xs hx => rp xs (rest_in_parts _ hx)
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [decomposePaths, h, PathDecomposition.parts, List.cons_ne_nil, ite_false]
      simp only [decomposePaths, h] at main
      intro xs hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .root main
      · rcases List.mem_append.mp hx with hx | hx
        · first | exact .left (lp xs hx) | exact .left (lr xs hx)
        · first | exact .right (rp xs hx) | exact .right (rr xs hx)

theorem referencePath_suffix_interval {t : Tree} {lo : Nat} {xs : List Nat}
    (path : ReferencePath t lo xs) (k : Nat) : KeyInterval (xs.drop k) xs := by
  induction path with
  | root h => exact rootPath_suffix_interval h k
  | left _ ih => exact ih
  | right _ ih => exact ih

end RotationBST.Tango
