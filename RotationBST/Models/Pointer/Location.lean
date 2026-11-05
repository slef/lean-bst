module

public import RotationBST.Models.Pointer.Keys

@[expose] public section
namespace RotationBST.Pointer

private def seek : Tree → Nat → List Frame → Option Config
  | .nil, _, _ => none
  | .node l r, x, cs =>
      if x < l.size then seek l x (.left r :: cs)
      else if x = l.size then some ⟨.node l r, cs⟩
      else seek r (x - l.size - 1) (.right l :: cs)

private theorem seek_plug (cs : List Frame) (t : Tree) (x : Nat) (valid : x < t.size)
    (outer : List Frame) :
    seek (plug cs t) (offset cs + x) outer = seek t x (cs ++ outer) := by
  induction cs generalizing t x with
  | nil => simp only [plug, offset, Nat.zero_add, List.nil_append]
  | cons f cs ih =>
    cases f with
    | left r =>
      have range : x < (Tree.node t r).size := by simp only [Tree.size]; omega
      rw [plug, offset, ih (.node t r) x range]
      simp only [seek, valid, ↓reduceIte, List.cons_append]
    | right l =>
      have range : l.size + 1 + x < (Tree.node l t).size := by simp only [Tree.size]; omega
      have index : offset cs + l.size + 1 + x = offset cs + (l.size + 1 + x) := by omega
      simp only [plug, offset]
      rw [index, ih (.node l t) (l.size + 1 + x) range]
      have lt : ¬ l.size + 1 + x < l.size := by omega
      have eq : ¬ l.size + 1 + x = l.size := by omega
      have sub : l.size + 1 + x - l.size - 1 = x := by omega
      simp only [seek, lt, eq, ↓reduceIte, sub, List.cons_append]

private theorem seek_config (c : Config) (x : Nat) (key : c.key? = some x) :
    seek c.tree x [] = some c := by
  rcases c with ⟨t, cs⟩
  cases t with
  | nil => simp [Config.key?] at key
  | node l r =>
    have index : offset cs + l.size = x := Option.some.inj key
    rw [← index]
    change seek (plug cs (.node l r)) (offset cs + l.size) [] = _
    rw [seek_plug cs (.node l r) l.size (by simp only [Tree.size]; omega)]
    simp only [seek, Nat.lt_irrefl, ↓reduceIte, List.append_nil]

/-- Inorder ranks identify the entire reference cursor, including its focus
and zipper. Empty focuses are excluded by the valid-key hypotheses. -/
theorem Config.ext_key {a b : Config} {x : Nat} (tree : a.tree = b.tree)
    (left : a.key? = some x) (right : b.key? = some x) : a = b := by
  have ha := seek_config a x left
  have hb := seek_config b x right
  rw [tree, hb] at ha
  exact (Option.some.inj ha).symm

/-- An instruction either keeps the pointed key (a rotation), moves to one
child, or moves to the parent described by the first zipper frame. -/
theorem Step.destination {l r : Tree} {cs : List Frame} {b : Config}
    (step : Step ⟨.node l r, cs⟩ b) :
    b.key? = (Config.mk (.node l r) cs).key? ∨
      (l ≠ .nil ∧ b = ⟨l, .left r :: cs⟩) ∨
      (r ≠ .nil ∧ b = ⟨r, .right l :: cs⟩) ∨
      ∃ f ds, cs = f :: ds ∧ b = ⟨plug [f] (.node l r), ds⟩ := by
  cases step with
  | downLeft => exact Or.inr (Or.inl ⟨by simp, rfl⟩)
  | downRight => exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl⟩))
  | upLeft => exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
  | upRight => exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
  | rotateLeftChild => exact Or.inl rfl
  | rotateRightChild =>
    left
    simp only [Config.key?, offset, Tree.size, Nat.add_assoc]

end RotationBST.Pointer
