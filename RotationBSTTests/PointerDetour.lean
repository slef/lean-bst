module

public import RotationBST.Models.Pointer.Detour.Abstract
public import RotationBST.Algorithms.Deamortization.Window.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.PointerDetour

private def leaf : Tree := .node .nil .nil
private def tree : Tree := .node leaf (.node leaf leaf)
private def initial : Pointer.Config := ⟨tree, []⟩
private def interrupted : Pointer.Config := ⟨leaf, [.left leaf, .right leaf]⟩
private def finish : Pointer.Config := ⟨leaf, [.left (.node leaf leaf)]⟩
private def pending : List Multifinger.Opcode := [.downRight, .downLeft, .upLeft, .upRight, .downLeft]

private theorem depth_bound (x : Nat) (hx : x < tree.size) : Tree.depth tree x ≤ 2 := by
  change x < 5 at hx
  interval_cases x <;> decide

private theorem prefix_tree (cut : Nat) (middle : Pointer.Config)
    (replay : Multifinger.replay (pending.take cut) initial = some middle) : middle.tree = tree := by
  by_cases short : cut < 5
  · interval_cases cut <;> simp [pending, initial, tree, leaf, Multifinger.replay, Multifinger.perform] at replay <;>
      subst middle <;> rfl
  · have enough : pending.length ≤ cut := by change 5 ≤ cut; omega
    rw [List.take_of_length_le enough] at replay
    have same : middle = finish := Option.some.inj (replay.symm.trans (show Multifinger.replay pending initial = some finish from rfl))
    subst middle
    rfl

-- The paused cursor is two levels below the root. A read-only request must
-- return to that complete zipper before the original suffix can execute.
example : ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
    Multifinger.replay before interrupted = some visited ∧ visited.key? = some 0 ∧
    Multifinger.replay after visited = some interrupted ∧
    (1 + before.length + after.length : ℝ) ≤ 9 ∧
    Multifinger.replay (pending.take 2 ++ before ++ after ++ pending.drop 2) initial = some finish ∧
    (∀ cut, ∃ middle, Multifinger.replay (before.take cut) interrupted = some middle ∧ middle.tree = tree) ∧
    (∀ cut, ∃ middle, Multifinger.replay (after.take cut) visited = some middle ∧ middle.tree = tree) := by
  have depth : ∀ x < interrupted.tree.size, (Tree.depth interrupted.tree x : ℝ) ≤ 2 := by
    intro x hx
    exact_mod_cast depth_bound x hx
  obtain ⟨visited, before, after, outward, key, backward, work, _, firstFixed, lastFixed⟩ :=
    Pointer.Detour.Results.bounded (start := interrupted) (target := 0) (by decide) (by decide) depth
  exact ⟨visited, before, after, outward, key, backward, by norm_num at work ⊢; exact work,
    Pointer.Detour.Results.resume (earlier := pending.take 2) (later := pending.drop 2)
      (start := initial) (finish := finish) rfl outward backward rfl, firstFixed, lastFixed⟩

-- Repeating the key at a non-root cursor charges only the request: neither
-- the outward nor the return program contains a physical instruction.
example : ∃ visited before after,
    Multifinger.replay before interrupted = some visited ∧ visited.key? = some 2 ∧
    Multifinger.replay after visited = some interrupted ∧ before = [] ∧ after = [] := by
  have depth : ∀ x < interrupted.tree.size, (Tree.depth interrupted.tree x : ℝ) ≤ 2 := by
    intro x hx
    exact_mod_cast depth_bound x hx
  obtain ⟨visited, before, after, outward, key, backward, _, repeated, _, _⟩ :=
    Pointer.Detour.Results.bounded (start := interrupted) (target := 2) (by decide) (by decide) depth
  exact ⟨visited, before, after, outward, key, backward, repeated rfl⟩

-- No target visit occurs in the first two original operations. The window
-- therefore spends its whole budget, inserts the request, and leaves the
-- exact three-operation suffix ready to resume from the old paused cursor.
example : ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
    Multifinger.replay before initial = some visited ∧ visited.key? = some 0 ∧
    Multifinger.replay after visited = some interrupted ∧
    Multifinger.replay (pending.drop 2) interrupted = some finish ∧
    before.length + after.length ≤ 10 ∧ 1 + before.length + after.length ≤ 11 := by
  have visits : ∃ cut visited, cut ≤ pending.length ∧
      Multifinger.replay (pending.take cut) initial = some visited ∧ visited.key? = some 0 :=
    ⟨5, finish, by decide, rfl, rfl⟩
  have height : ∀ cut middle, Multifinger.replay (pending.take cut) initial = some middle →
      ∀ x < middle.tree.size, Tree.depth middle.tree x ≤ 2 := by
    intro cut middle replay x hx
    rw [prefix_tree cut middle replay] at hx ⊢
    exact depth_bound x hx
  obtain ⟨consumed, middle, visited, before, after, within, _, first, last, outward, key, backward,
    work, worst, stop⟩ := Deamortization.Window.Results.serve
      (ops := pending) (start := initial) (finish := finish) rfl (by decide) (by decide) visits height
  have count : consumed = 2 := by
    rcases stop with done | hit
    · exact done
    · interval_cases consumed <;>
        simp [pending, initial, tree, leaf, Multifinger.replay, Multifinger.perform] at first <;>
        subst middle <;> cases hit
  subst consumed
  have same : middle = interrupted := Option.some.inj (first.symm.trans rfl)
  subst middle
  exact ⟨visited, before, after, outward, key, backward, last, work, worst⟩

end RotationBST.Tests.PointerDetour
