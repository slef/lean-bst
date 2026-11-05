module

public import RotationBST.Bounds.LazyFinger.Geometry
public import RotationBST.Models.Rotation.Search.Bounds

@[expose] public section
namespace RotationBST.LazyFinger

/-- Search depth is the number of proper ancestors; the path also includes
the requested node itself. -/
theorem searchPath_length (t : Tree) (lo x : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) :
    (t.searchPath lo x).length = Tree.depth t (x - lo) + 1 := by
  induction t generalizing lo with
  | nil => simp [Tree.size] at hx; omega
  | node l r ihl ihr =>
    by_cases hl : x < lo + l.size
    · have hx' : lo ≤ x ∧ x < lo + l.size := ⟨hx.1, hl⟩
      have he : x - lo < l.size := by omega
      simp [Tree.searchPath, hl, Tree.depth, he, ihl lo hx']
    · by_cases he : x = lo + l.size
      · subst x
        simp [Tree.searchPath, Tree.depth]
      · have hx' : lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size := by
          simp only [Tree.size] at hx; omega
        have hn : ¬ x - lo < l.size := by omega
        have hn' : x - lo ≠ l.size := by omega
        have hs : x - (lo + l.size + 1) = x - lo - l.size - 1 := by omega
        simp [Tree.searchPath, hl, he, Tree.depth, hn, hn', ihr _ hx', hs]

end RotationBST.LazyFinger
