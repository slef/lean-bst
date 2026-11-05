module

public import RotationBST.Models.Pointer.Navigation
public import RotationBST.Models.Pointer.Keys
public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST.Pointer

theorem Config.under_tree (c : Config) (cs : List Frame) : (c.under cs).tree = plug cs c.tree := by
  simp only [Config.under, Config.tree, plug_append]

theorem Config.under_key (c : Config) (cs : List Frame) (x : Nat) (key : c.key? = some x) :
    (c.under cs).key? = some (offset cs + x) := by
  rcases c with ⟨focus, path⟩
  cases focus with
  | nil => simp [Config.key?] at key
  | node l r =>
    have index := Option.some.inj key
    change offset path + l.size = x at index
    simp only [Config.under, Config.key?, offset_append]
    congr 1
    omega

/-- The ordinary rank-search path identifies an existing cursor at exactly the
static search depth, including all off-path reference subtrees. -/
theorem search_location (t : Tree) (x : Nat) (valid : x < t.size) :
    ∃ (a b : Tree) (cs : List Frame), plug cs (.node a b) = t ∧
      offset cs + a.size = x ∧ cs.length = Tree.depth t x := by
  induction t generalizing x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    by_cases left : x < l.size
    · obtain ⟨a, b, cs, tree, key, depth⟩ := il x left
      refine ⟨a, b, cs ++ [.left r], ?_, ?_, ?_⟩
      · simp only [plug_append, tree, plug]
      · simpa only [offset_append, offset, Nat.add_zero] using key
      · simp only [List.length_append, List.length_cons, List.length_nil, depth,
          Tree.depth, left, ↓reduceIte]
    · by_cases root : x = l.size
      · subst x
        exact ⟨l, r, [], rfl, by simp [offset], by simp [Tree.depth]⟩
      · have right : x - l.size - 1 < r.size := by simp only [Tree.size] at valid; omega
        obtain ⟨a, b, cs, tree, key, depth⟩ := ir _ right
        refine ⟨a, b, cs ++ [.right l], ?_, ?_, ?_⟩
        · simp only [plug_append, tree, plug]
        · simp only [offset_append, offset]
          omega
        · simp only [List.length_append, List.length_cons, List.length_nil, depth,
            Tree.depth, left, root, ↓reduceIte]

/-- Outward and return walks of exactly the ordinary search depth. -/
theorem search_walk (t : Tree) (x : Nat) (valid : x < t.size) :
    ∃ c : Config, c.tree = t ∧ c.key? = some x ∧
      Trace ⟨t, []⟩ c (Tree.depth t x) ∧ Trace c ⟨t, []⟩ (Tree.depth t x) := by
  obtain ⟨a, b, cs, tree, key, depth⟩ := search_location t x valid
  refine ⟨⟨.node a b, cs⟩, tree, congrArg some key, ?_, ?_⟩
  · simpa only [tree, depth] using descend cs a b
  · simpa only [tree, depth] using ascend cs a b

end RotationBST.Pointer
