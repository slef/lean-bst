module

public import RotationBST.Structures.HeavyPath.Recursive.History.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.History.Interruption.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Down.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Up.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Rotation.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RecursiveHistory
open HeavyPath HeavyPath.Paired HeavyPath.Recursive
open PopTart PopTart.Chocolate

private def chain : LabelledTree Nat := .node .nil 1 (.node .nil 1 (.node .nil 1 (.node .nil 1 .nil)))
private def slot : WeightedTree := .leaf .nil 1
private def frozenLayer : Layer := .last (.one slot) (.solid (.node slot slot) (.base (.leaf .nil 0)))
private def freshLayer : Layer := .last (.three slot slot slot) (.base (.leaf .nil 0))
private def frozen : Stacks := ⟨frozenLayer, Stacks.empty.upper⟩
private def fresh : Stacks := ⟨freshLayer, Stacks.empty.upper⟩
private def nilEntry : History.Entry Nat := ⟨.right .nil 1, .nil, 0⟩
private def entries : List (History.Entry Nat) := [nilEntry, nilEntry, nilEntry]

private theorem frozenValid : frozenLayer.Valid 0 := by
  refine ⟨⟨.leaf _ _, by norm_num [slot, WeightedTree.Nonnegative]⟩,
    ⟨.node (.leaf _ _) (.leaf _ _), ?_, ⟨.leaf _ _, le_rfl⟩, ?_⟩, ?_⟩
  all_goals norm_num [slot, WeightedTree.Nonnegative, WeightedTree.mass, Icing.decode]

private theorem freshValid : freshLayer.Valid 0 := by
  refine ⟨⟨⟨.leaf _ _, ?_⟩, ⟨.leaf _ _, ?_⟩, ⟨.leaf _ _, ?_⟩⟩, ⟨.leaf _ _, le_rfl⟩, ?_⟩
  all_goals norm_num [slot, WeightedTree.Nonnegative]

private theorem sourceContext : entries.map History.Entry.source = (extract (fun _ => 1) chain).context := by
  norm_num [entries, nilEntry, chain, extract, LeftHeavy, HeavyPath.mass, extend]

private theorem frozenPath : History.PathValid (fun _ => 1) entries frozen := by
  refine ⟨⟨frozenValid, Paired.Results.empty_valid.2⟩, ?_, ?_⟩
  all_goals norm_num [entries, nilEntry, History.lower, History.upper, History.Entry.slot, frameMass,
    HeavyPath.mass, frozen, frozenLayer, slot, Stacks.empty, Layer.decode, Regulars.attach,
    Icing.decode, WeightedTree.fringe, WeightedTree.mirror, Tree.mirror]

private theorem freshPath : History.PathValid (fun _ => 1) entries fresh := by
  refine ⟨⟨freshValid, Paired.Results.empty_valid.2⟩, ?_, ?_⟩
  all_goals norm_num [entries, nilEntry, History.lower, History.upper, History.Entry.slot, frameMass,
    HeavyPath.mass, fresh, freshLayer, slot, Stacks.empty, Layer.decode, Regulars.attach,
    Icing.decode, WeightedTree.fringe, WeightedTree.mirror, Tree.mirror]

private theorem nilChildren : ∀ e ∈ entries,
    History.Layout (fun _ => 1) (framePayload e.source) e.shape e.credit := by
  intro e member
  have same : e = nilEntry := by simpa [entries] using member
  subst e
  exact .nil

private theorem frozenHistory : History.Layout (fun _ => 1) chain frozen.tree frozen.potential := by
  have layout := History.Layout.path (HeavyPath.Results.unit_positive chain) (by decide : chain ≠ .nil)
    sourceContext frozenPath nilChildren
  simpa only [entries, nilEntry, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using layout

private theorem freshHistory : History.Layout (fun _ => 1) chain fresh.tree fresh.potential := by
  have layout := History.Layout.path (HeavyPath.Results.unit_positive chain) (by decide : chain ≠ .nil)
    sourceContext freshPath nilChildren
  simpa only [entries, nilEntry, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using layout

-- Two valid histories of the same labelled source have different shapes.
example : frozen.tree ≠ fresh.tree := by decide

-- The depth theorem covers all four repeated-key occurrences in either shape.
example (rank : Fin 4) : (Tree.depth frozen.tree rank.val : ℝ) ≤ 7 + 15 * Real.logb 2 4 := by
  have bound := History.Results.layout_depth_at frozenHistory (rank := ⟨rank.val, rank.isLt⟩)
  have total : HeavyPath.mass (fun _ => 1) chain = 4 := by norm_num [chain, HeavyPath.mass]
  simpa only [total, div_one] using bound

example : ∃ visited cost, visited.tree = frozen.tree ∧ visited.key? = some 2 ∧
    Pointer.Trace ⟨frozen.tree, []⟩ visited cost ∧ Pointer.Trace visited ⟨frozen.tree, []⟩ cost ∧
    (1 + 2 * cost : ℝ) ≤ 15 + 30 * Real.logb 2 4 := by
  have total : HeavyPath.mass (fun _ => 1) chain = 4 := by norm_num [chain, HeavyPath.mass]
  simpa only [total, div_one] using History.Results.layout_search_walk frozenHistory ⟨2, by decide⟩

private def source : LabelledTree Nat := .node chain 9 chain
private def rootEntry : History.Entry Nat := ⟨.left 9 chain, fresh.tree, fresh.potential⟩
private def mixed : Stacks :=
  ⟨frozen.lower, .last (.one (.leaf fresh.tree.mirror 5)) (.base (.leaf .nil 0))⟩

-- Equal source subtrees coexist with different physical histories. The
-- heavy child retains the frozen path; the light payload retains fresh's
-- independent stack shape and potential.
private theorem mixedHistory : History.Layout (fun _ => 1) source mixed.tree (mixed.potential + fresh.potential) := by
  have valid : History.PathValid (fun _ => 1) (entries ++ [rootEntry]) mixed := by
    refine ⟨⟨frozenValid, ?_⟩, ?_, ?_⟩
    · exact ⟨⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩,
        ⟨.leaf _ _, le_rfl⟩, by intro h; cases h⟩
    · change frozen.lower.decode.fringe = _
      simpa only [entries, rootEntry, nilEntry, History.lower, List.map_cons,
        List.map_nil, List.append_nil, List.nil_append, List.cons_append] using frozenPath.lower
    · norm_num [entries, rootEntry, nilEntry, History.upper, History.Entry.slot,
        frameMass, source, chain, HeavyPath.mass, mixed, Layer.decode, Regulars.attach,
        Icing.decode, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror, Tree.mirror]
  have context : (entries ++ [rootEntry]).map History.Entry.source = (extract (fun _ => 1) source).context := by
    norm_num [entries, rootEntry, nilEntry, source, chain, extract, LeftHeavy, HeavyPath.mass, extend]
  have children : ∀ e ∈ entries ++ [rootEntry],
      History.Layout (fun _ => 1) (framePayload e.source) e.shape e.credit := by
    intro e member
    rcases List.mem_append.mp member with earlier | last
    · exact nilChildren e earlier
    · have same : e = rootEntry := by simpa using last
      subst e
      exact freshHistory
  have layout := History.Layout.path (HeavyPath.Results.unit_positive source) (by decide : source ≠ .nil)
    context valid children
  simpa only [entries, rootEntry, nilEntry, List.map_cons, List.map_nil, List.map_append,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add] using layout

-- Exposure retains both recursively valid children and their actual credits.
example : ∃ a b leftCredit rightCredit cost,
    History.Layout (fun _ => 1) chain a leftCredit ∧ History.Layout (fun _ => 1) chain b rightCredit ∧
    Pointer.Trace ⟨mixed.tree, []⟩ ⟨.node a b, []⟩ cost ∧
    cost + leftCredit + rightCredit ≤ 24 + (mixed.potential + fresh.potential) :=
  History.Results.layout_expose mixedHistory

-- The actual pop in this fixture exposes the two different shapes in four
-- instructions, without rebuilding either subtree.
example : Pointer.Trace ⟨mixed.tree, []⟩ ⟨.node frozen.tree fresh.tree, []⟩ 4 := by
  have trace := Paired.Exposure.Results.upper_trace (p := mixed)
    (crumb := .leaf fresh.tree.mirror 5) (rest := Stacks.empty.upper) rfl
  have rest : Stacks.mk mixed.lower Stacks.empty.upper = frozen := rfl
  rw [rest] at trace
  simpa only [WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
    Tree.mirror_mirror, show mixed.upper.popCost = 0 from rfl, Nat.zero_add] using trace

-- Canonical initialization is included; callers need no new assumptions.
example : ∃ credit, History.Layout (fun _ => 1) source (rebuild (fun _ => 1) source) credit :=
  History.Results.rebuild_history (HeavyPath.Results.unit_positive source)

private def enclosing : Finger.Pair :=
  ⟨.last .zero (.base (.leaf mixed.tree.mirror 9)), Stacks.empty.upper⟩
private theorem enclosingValid : enclosing.Valid :=
  ⟨⟨trivial, ⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩,
    Paired.Results.empty_valid.2⟩

-- The composed move retains both differently represented copies of chain,
-- with all their nested credits counted in the output bound.
example : ∃ a b leftCredit rightCredit cost,
    History.Layout (fun _ => 1) chain a leftCredit ∧ History.Layout (fun _ => 1) chain b rightCredit ∧
    let next := enclosing.downLeft a b 4 11
    Pointer.Trace ⟨enclosing.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
    cost + next.potential + leftCredit + rightCredit ≤
      54 + enclosing.potential + (mixed.potential + fresh.potential) ∧
    next.mass + 1 = enclosing.mass + 7 ∧
    (Pointer.Config.mk next.tree []).key? = some 4 := by
  have stored : enclosing.lower.top = .leaf mixed.tree.mirror (0 + HeavyPath.mass (fun _ => 1) source) := by
    norm_num [enclosing, Layer.top, Icing.decode, source, chain, HeavyPath.mass]
  have result := Finger.Transfer.History.Results.downLeft enclosingValid mixedHistory
    (carry := 0) (fingerWeight := 7) (by norm_num) (by norm_num) stored
  have size : enclosing.lower.decode.tree.mirror.size = 9 := by
    change mixed.tree.mirror.mirror.size = 9
    rw [Tree.mirror_mirror, History.Results.layout_size mixedHistory]
    rfl
  norm_num [source, chain, HeavyPath.mass, size, LabelledTree.erase, Tree.size] at result ⊢
  exact result

private def enclosingRight : Finger.Pair :=
  ⟨Stacks.empty.lower, .last .zero (.base (.leaf mixed.tree 9))⟩
private theorem enclosingRightValid : enclosingRight.Valid :=
  ⟨Paired.Results.empty_valid.1,
    ⟨trivial, ⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩⟩

example : ∃ a b leftCredit rightCredit cost,
    History.Layout (fun _ => 1) chain a leftCredit ∧ History.Layout (fun _ => 1) chain b rightCredit ∧
    let next := enclosingRight.downRight a b 11 4
    Pointer.Trace ⟨enclosingRight.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
    cost + next.potential + leftCredit + rightCredit ≤
      54 + enclosingRight.potential + (mixed.potential + fresh.potential) ∧
    next.mass + 1 = enclosingRight.mass + 7 ∧
    (Pointer.Config.mk next.tree []).key? = some 5 := by
  have stored : enclosingRight.upper.top = .leaf mixed.tree (0 + HeavyPath.mass (fun _ => 1) source) := by
    norm_num [enclosingRight, Layer.top, Icing.decode, source, chain, HeavyPath.mass]
  have result := Finger.Transfer.History.Results.downRight enclosingRightValid mixedHistory
    (carry := 0) (fingerWeight := 7) (by norm_num) (by norm_num) stored
  have size : enclosingRight.lower.decode.tree.mirror.size = 0 := rfl
  norm_num [source, chain, HeavyPath.mass, size, LabelledTree.erase, Tree.size] at result ⊢
  exact result

-- The canonical embedding also retains nonuniform analysis weights.
example : ∃ credit, History.Layout (fun x : Nat => (x : ℝ) + 1) source
      (rebuild (fun x : Nat => (x : ℝ) + 1) source) credit ∧
    (Tree.depth (rebuild (fun x : Nat => (x : ℝ) + 1) source) 4 : ℝ) ≤
      7 + 15 * Real.logb 2 (26 / 10) := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1) source := by
    norm_num [source, chain, Positive]
  obtain ⟨credit, layout⟩ := History.Results.rebuild_history positive
  refine ⟨credit, layout, ?_⟩
  have bound := History.Results.layout_depth layout (before := chain.inorder) (key := 9)
    (after := chain.inorder) rfl
  norm_num [source, chain, HeavyPath.mass, LabelledTree.inorder] at bound ⊢
  exact bound

-- The whole inverted state retains four occurrences of the same source
-- chain: two ancestor payloads and both finger children. Their two distinct
-- physical histories survive independently in both orientations.
private def ancestorEntries : List (History.Entry Nat) :=
  [⟨.right chain 2, frozen.tree, frozen.potential⟩,
   ⟨.left 3 chain, fresh.tree, fresh.potential⟩]

private def ancestorContext : List (LabelledCursor.Frame Nat) := [.right chain 2, .left 3 chain]

private def historyPair : Finger.Pair :=
  ⟨.last (.one (.leaf frozen.tree.mirror 5)) (.base (.leaf frozen.tree.mirror 4)),
   .last (.one (.leaf fresh.tree 5)) (.base (.leaf fresh.tree 4))⟩

private def historyState : Finger.History.State Nat :=
  ⟨ancestorEntries, frozen.tree, fresh.tree, frozen.potential, fresh.potential, historyPair⟩

private theorem historyStateValid : Finger.History.Valid (fun _ => 1) ancestorContext chain 9 chain historyState := by
  refine ⟨HeavyPath.Results.unit_positive _, rfl, ?_, frozenHistory, freshHistory, ?_, ?_, ?_⟩
  · constructor <;>
      exact ⟨⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩,
        ⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, by intro h; cases h⟩
  · intro e he
    change e ∈ ancestorEntries at he
    simp only [ancestorEntries, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact frozenHistory
    · exact freshHistory
  · norm_num [historyState, historyPair, ancestorEntries, History.lower, Finger.History.sideSlots,
      framePayload, frameKey, chain, HeavyPath.mass, Layer.decode, Regulars.attach, Icing.decode,
      WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror]
  · norm_num [historyState, historyPair, ancestorEntries, History.upper, Finger.History.sideSlots,
      framePayload, frameKey, chain, HeavyPath.mass, Layer.decode, Regulars.attach, Icing.decode,
      WeightedTree.fringe]

example : historyState.pair.tree.size = 19 := by
  rw [Finger.History.Results.state_size historyStateValid]
  rfl

example : historyState.pair.mass = 18 := by
  have partition := Finger.History.Results.state_mass historyStateValid
  norm_num [ancestorContext, chain, LabelledCursor.plug, HeavyPath.mass] at partition
  linarith

example : (Pointer.Config.mk historyState.pair.tree []).key? = some 9 := by
  rw [Finger.History.Results.state_root_key historyStateValid]
  rfl

example : historyState.potential = historyPair.potential + 2 * frozen.potential + 2 * fresh.potential := by
  simp only [historyState, Finger.History.State.potential, ancestorEntries,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

-- This bound covers every occurrence, including both ancestor separators.
example (rank : Fin 19) : (Tree.depth historyState.pair.tree rank.val : ℝ) ≤
    15 + 15 * Real.logb 2 19 := by
  have total : HeavyPath.mass (fun _ => 1) (LabelledCursor.plug ancestorContext (.node chain 9 chain)) = 19 := by
    norm_num [ancestorContext, chain, LabelledCursor.plug, HeavyPath.mass]
  simpa only [total, div_one] using
    Finger.History.Results.state_depth_at historyStateValid ⟨rank.val, rank.isLt⟩

example : ∃ visited cost, visited.tree = historyState.pair.tree ∧ visited.key? = some 0 ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ visited cost ∧
    Pointer.Trace visited ⟨historyState.pair.tree, []⟩ cost ∧
    (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2 19 := by
  have total : HeavyPath.mass (fun _ => 1) (LabelledCursor.plug ancestorContext (.node chain 9 chain)) = 19 := by
    norm_num [ancestorContext, chain, LabelledCursor.plug, HeavyPath.mass]
  simpa only [total, div_one] using
    Finger.History.Results.state_search_walk historyStateValid ⟨0, by decide⟩

-- Canonical initialization also constructs the complete state at a non-root
-- source cursor with nonuniform weights.
example : ∃ (s : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain s ∧
    Pointer.Trace ⟨(LabelledCursor.plug ancestorContext source).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
    cost ≤ 16 * 19 := by
  apply Finger.History.Results.state_initialization
  norm_num [ancestorContext, chain, LabelledCursor.plug, Positive]

private def chainTail : LabelledTree Nat := .node .nil 1 (.node .nil 1 (.node .nil 1 .nil))
private def chainTailTail : LabelledTree Nat := .node .nil 1 (.node .nil 1 .nil)

-- A left move retains every ancestor payload, pushes the differently shaped
-- sibling as a new occurrence, and keeps the original source rank.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) (.left 9 chain :: ancestorContext) .nil 1 chainTail next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 54 + historyState.potential ∧
    next.ancestors = ⟨.left 9 chain, fresh.tree, fresh.potential⟩ :: ancestorEntries ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 5 := by
  obtain ⟨next, cost, valid, trace, bound, ancestors⟩ :=
    Finger.History.Down.Results.downLeft historyStateValid
  refine ⟨next, cost, valid, trace, bound, ancestors, ?_⟩
  rw [Finger.History.Results.state_root_key valid]
  rfl

example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) (.right chain 9 :: ancestorContext) .nil 1 chainTail next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 54 + historyState.potential ∧
    next.ancestors = ⟨.right chain 9, frozen.tree, frozen.potential⟩ :: ancestorEntries ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 10 := by
  obtain ⟨next, cost, valid, trace, bound, ancestors⟩ :=
    Finger.History.Down.Results.downRight historyStateValid
  refine ⟨next, cost, valid, trace, bound, ancestors, ?_⟩
  rw [Finger.History.Results.state_root_key valid]
  rfl

-- The returned state can be used immediately by the opposite move. The
-- complete potentials telescope and the global depth guarantee still holds.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) (.right .nil 1 :: .left 9 chain :: ancestorContext)
      .nil 1 chainTailTail next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 108 + historyState.potential ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 6 ∧
    ∀ rank : Fin 19, (Tree.depth next.pair.tree rank.val : ℝ) ≤ 15 + 15 * Real.logb 2 19 := by
  obtain ⟨middle, firstCost, middleValid, firstTrace, firstBound, _⟩ :=
    Finger.History.Down.Results.downLeft historyStateValid
  obtain ⟨next, secondCost, nextValid, secondTrace, secondBound, _⟩ :=
    Finger.History.Down.Results.downRight middleValid
  refine ⟨next, firstCost + secondCost, nextValid, firstTrace.append secondTrace, by omega, ?_, ?_⟩
  · rw [Finger.History.Results.state_root_key nextValid]
    rfl
  · intro rank
    have total : HeavyPath.mass (fun _ => 1)
        (LabelledCursor.plug (.right .nil 1 :: .left 9 chain :: ancestorContext)
          (.node .nil 1 (.node .nil 1 (.node .nil 1 .nil)))) = 19 := by
      norm_num [ancestorContext, chain, LabelledCursor.plug, HeavyPath.mass]
    simpa only [total, div_one] using
      Finger.History.Results.state_depth_at nextValid ⟨rank.val, rank.isLt⟩

-- The departing finger weighs ten and the arriving key weighs two. The
-- whole-state mass identity tracks that shift through the actual move.
example : ∃ (start next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain start ∧
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) (.left 9 chain :: ancestorContext)
      .nil 1 chainTail next ∧
    Pointer.Trace ⟨start.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 54 + start.potential ∧ next.pair.mass = 47 := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1)
      (LabelledCursor.plug ancestorContext source) := by
    norm_num [ancestorContext, source, chain, LabelledCursor.plug, Positive]
  obtain ⟨start, startValid, _⟩ := Finger.History.Results.build_state positive
  obtain ⟨next, cost, nextValid, trace, bound, _⟩ := Finger.History.Down.Results.downLeft startValid
  refine ⟨start, next, cost, startValid, nextValid, trace, bound, ?_⟩
  have partition := Finger.History.Results.state_mass nextValid
  norm_num [ancestorContext, chain, LabelledCursor.plug, HeavyPath.mass] at partition
  linarith

-- Joining accepts distinct histories of equal source trees, and covers both
-- a right-heavy source root and the terminal singleton boundary.
example : ∃ shape credit cost, History.Layout (fun _ => 1) source shape credit ∧
    Pointer.Trace ⟨.node frozen.tree fresh.tree, []⟩ ⟨shape, []⟩ cost ∧
    cost + credit ≤ 24 + frozen.potential + fresh.potential :=
  History.Results.layout_join frozenHistory freshHistory (by norm_num)

example : ∃ shape credit cost, History.Layout (fun _ => 1) (.node .nil 7 chain) shape credit ∧
    Pointer.Trace ⟨.node .nil frozen.tree, []⟩ ⟨shape, []⟩ cost ∧
    cost + credit ≤ 24 + 0 + frozen.potential :=
  History.Results.layout_join .nil frozenHistory (by norm_num)

example : ∃ shape credit cost, History.Layout (fun _ => 1) (.node .nil 7 .nil) shape credit ∧
    Pointer.Trace ⟨.node .nil .nil, []⟩ ⟨shape, []⟩ cost ∧ cost + credit ≤ 24 + 0 + 0 :=
  History.Results.layout_join .nil .nil (by norm_num)

-- Climb through an ancestor already present in the noncanonical fixture.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [.left 3 chain] chain 2 source next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 62 + historyState.potential ∧
    next.ancestors = ancestorEntries.tail ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 4 := by
  obtain ⟨next, cost, valid, trace, bound, ancestors⟩ :=
    Finger.History.Up.Results.upRight historyStateValid
  refine ⟨next, cost, valid, trace, bound, ancestors, ?_⟩
  rw [Finger.History.Results.state_root_key valid]
  rfl

-- Opposite upward directions compose without resetting any recursive credit.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [] (.node chain 2 source) 3 chain next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 124 + historyState.potential ∧ next.ancestors = [] ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 14 ∧
    ∀ rank : Fin 19, (Tree.depth next.pair.tree rank.val : ℝ) ≤ 15 + 15 * Real.logb 2 19 := by
  obtain ⟨middle, firstCost, middleValid, firstTrace, firstBound, firstAncestors⟩ :=
    Finger.History.Up.Results.upRight historyStateValid
  obtain ⟨next, secondCost, nextValid, secondTrace, secondBound, secondAncestors⟩ :=
    Finger.History.Up.Results.upLeft middleValid
  refine ⟨next, firstCost + secondCost, nextValid, firstTrace.append secondTrace, by omega, ?_, ?_, ?_⟩
  · rw [secondAncestors, firstAncestors]
    rfl
  · rw [Finger.History.Results.state_root_key nextValid]
    rfl
  · intro rank
    have bound := Finger.History.Results.state_depth_at nextValid ⟨rank.val, rank.isLt⟩
    norm_num [HeavyPath.Results.unit_mass, LabelledCursor.plug,
      chain, LabelledTree.erase, Tree.size] at bound ⊢
    exact bound

-- Moving down and back up returns to the same source cursor while allowing
-- the payload's physical repair history to change. All other entries survive.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) ancestorContext chain 9 chain next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 116 + historyState.potential ∧ next.ancestors = ancestorEntries := by
  obtain ⟨middle, firstCost, middleValid, firstTrace, firstBound, firstAncestors⟩ :=
    Finger.History.Down.Results.downLeft historyStateValid
  obtain ⟨next, secondCost, nextValid, secondTrace, secondBound, secondAncestors⟩ :=
    Finger.History.Up.Results.upLeft middleValid
  refine ⟨next, firstCost + secondCost, nextValid, firstTrace.append secondTrace, by omega, ?_⟩
  rw [secondAncestors, firstAncestors]
  rfl

example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) ancestorContext chain 9 chain next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 116 + historyState.potential ∧ next.ancestors = ancestorEntries := by
  obtain ⟨middle, firstCost, middleValid, firstTrace, firstBound, firstAncestors⟩ :=
    Finger.History.Down.Results.downRight historyStateValid
  obtain ⟨next, secondCost, nextValid, secondTrace, secondBound, secondAncestors⟩ :=
    Finger.History.Up.Results.upRight middleValid
  refine ⟨next, firstCost + secondCost, nextValid, firstTrace.append secondTrace, by omega, ?_⟩
  rw [secondAncestors, firstAncestors]
  rfl

-- A nonuniform upward move removes the arriving parent's weight three
-- from the represented pair and restores the departing weight ten.
example : ∃ (start next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain start ∧
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) [.left 3 chain] chain 2 source next ∧
    Pointer.Trace ⟨start.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 62 + start.potential ∧ next.pair.mass = 46 := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1)
      (LabelledCursor.plug ancestorContext source) := by
    norm_num [ancestorContext, source, chain, LabelledCursor.plug, Positive]
  obtain ⟨start, startValid, _⟩ := Finger.History.Results.build_state positive
  obtain ⟨next, cost, nextValid, trace, bound, _⟩ := Finger.History.Up.Results.upRight startValid
  refine ⟨start, next, cost, startValid, nextValid, trace, bound, ?_⟩
  have partition := Finger.History.Results.state_mass nextValid
  norm_num [chain, LabelledCursor.plug, HeavyPath.mass] at partition
  linarith

-- Source rotations merge only the adjacent payloads and keep the same
-- represented key at the physical root.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [.left 3 chain] (.node chain 2 chain) 9 chain next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 50 + historyState.potential ∧
    next.ancestors = ancestorEntries.tail ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 9 := by
  obtain ⟨next, cost, valid, trace, bound, ancestors⟩ :=
    Finger.History.Rotation.Results.rotateRightChild historyStateValid
  refine ⟨next, cost, valid, trace, bound, ancestors, ?_⟩
  rw [Finger.History.Results.state_root_key valid]
  rfl

-- Two opposite source rotations raise the original finger to the source
-- root. Every occurrence still has the global depth bound in the final state.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [] (.node chain 2 chain) 9 (.node chain 3 chain) next ∧
    Pointer.Trace ⟨historyState.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 100 + historyState.potential ∧ next.ancestors = [] ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 9 ∧
    ∀ rank : Fin 19, (Tree.depth next.pair.tree rank.val : ℝ) ≤ 15 + 15 * Real.logb 2 19 := by
  obtain ⟨middle, firstCost, middleValid, firstTrace, firstBound, firstAncestors⟩ :=
    Finger.History.Rotation.Results.rotateRightChild historyStateValid
  obtain ⟨next, secondCost, nextValid, secondTrace, secondBound, secondAncestors⟩ :=
    Finger.History.Rotation.Results.rotateLeftChild middleValid
  refine ⟨next, firstCost + secondCost, nextValid, firstTrace.append secondTrace, by omega, ?_, ?_, ?_⟩
  · rw [secondAncestors, firstAncestors]
    rfl
  · rw [Finger.History.Results.state_root_key nextValid]
    rfl
  · intro rank
    have bound := Finger.History.Results.state_depth_at nextValid ⟨rank.val, rank.isLt⟩
    norm_num [HeavyPath.Results.unit_mass, LabelledCursor.plug,
      chain, LabelledTree.erase, Tree.size] at bound ⊢
    exact bound

-- With two ancestors on the same side, another separator remains beyond
-- the joined pair. This exercises collection with a nonempty outer suffix.
example : ∃ (start next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [.left 2 chain, .left 3 chain] chain 9 chain start ∧
    Finger.History.Valid (fun _ => 1) [.left 3 chain] chain 9 (.node chain 2 chain) next ∧
    Pointer.Trace ⟨start.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 50 + start.potential ∧
    (Pointer.Config.mk next.pair.tree []).key? = some 4 := by
  obtain ⟨start, startValid, _⟩ := Finger.History.Results.build_state
    (HeavyPath.Results.unit_positive (LabelledCursor.plug [.left 2 chain, .left 3 chain] source))
  obtain ⟨next, cost, nextValid, trace, bound, _⟩ :=
    Finger.History.Rotation.Results.rotateLeftChild startValid
  refine ⟨start, next, cost, startValid, nextValid, trace, bound, ?_⟩
  rw [Finger.History.Results.state_root_key nextValid]
  rfl

-- Rotations retain the same finger weight, so nonuniform pair mass stays
-- thirty-nine rather than shifting as it does during navigation.
example : ∃ (start next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain start ∧
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) [.left 3 chain] (.node chain 2 chain) 9 chain next ∧
    Pointer.Trace ⟨start.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 50 + start.potential ∧ next.pair.mass = 39 := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1)
      (LabelledCursor.plug ancestorContext source) := by
    norm_num [ancestorContext, source, chain, LabelledCursor.plug, Positive]
  obtain ⟨start, startValid, _⟩ := Finger.History.Results.build_state positive
  obtain ⟨next, cost, nextValid, trace, bound, _⟩ := Finger.History.Rotation.Results.rotateRightChild startValid
  refine ⟨start, next, cost, startValid, nextValid, trace, bound, ?_⟩
  have partition := Finger.History.Results.state_mass nextValid
  norm_num [chain, LabelledCursor.plug, HeavyPath.mass] at partition
  linarith

-- Empty payloads are valid: a two-key rotation uses the singleton join.
example : ∃ (start next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [.left 2 .nil] .nil 1 .nil start ∧
    Finger.History.Valid (fun _ => 1) [] .nil 1 (.node .nil 2 .nil) next ∧
    Pointer.Trace ⟨start.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 50 + start.potential ∧
    ∃! labelled : LabelledTree Nat, labelled.erase = next.pair.tree ∧
      labelled.inorder = [1, 2] ∧ labelled.Ordered := by
  obtain ⟨start, startValid, _⟩ := Finger.History.Results.build_state
    (HeavyPath.Results.unit_positive (LabelledCursor.plug [.left 2 .nil] (.node .nil 1 .nil)))
  obtain ⟨next, cost, nextValid, trace, bound, _⟩ := Finger.History.Rotation.Results.rotateLeftChild startValid
  refine ⟨start, next, cost, startValid, nextValid, trace, bound, ?_⟩
  apply Finger.History.Results.state_labels nextValid
  exact (Representation.ordered_iff _).mpr (by decide)

-- Canonical initialization bounds every nested credit, including repeated
-- payload occurrences and arbitrary positive analysis weights.
example : ∃ credit, History.Layout (fun _ : Nat => 1) .nil .nil credit ∧ credit = 0 := by
  obtain ⟨credit, layout, bound⟩ := History.Results.rebuild_history_bounded
    (HeavyPath.Results.unit_positive (LabelledTree.nil : LabelledTree Nat))
  exact ⟨credit, layout, by simpa only [LabelledTree.erase, Tree.size, Nat.mul_zero, Nat.le_zero] using bound⟩

example : ∃ credit, History.Layout (fun _ => 1) source (rebuild (fun _ => 1) source) credit ∧
    credit ≤ 23 * 9 :=
  History.Results.rebuild_history_bounded (HeavyPath.Results.unit_positive source)

example : ∃ s : Finger.History.State Nat,
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain s ∧
    s.pair = Finger.build (fun x : Nat => (x : ℝ) + 1) ancestorContext chain chain ∧
    s.potential ≤ 23 * 19 := by
  apply Finger.History.Results.build_state_bounded
  norm_num [ancestorContext, chain, LabelledCursor.plug, Positive]

example : ∃ (s : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun x : Nat => (x : ℝ) + 1) ancestorContext chain 9 chain s ∧
    Pointer.Trace ⟨(LabelledCursor.plug ancestorContext source).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
    cost ≤ 16 * 19 ∧ s.potential ≤ 23 * 19 ∧ cost + s.potential ≤ 39 * 19 := by
  apply Finger.History.Results.state_initialization_bounded
  norm_num [ancestorContext, chain, LabelledCursor.plug, Positive]

-- Startup accounting composes with real operations, beginning at the
-- original source tree. No unbounded initial potential is left in this bound.
example : ∃ (next : Finger.History.State Nat) (cost : Nat),
    Finger.History.Valid (fun _ => 1) [.left 3 chain] (.node chain 2 chain) 9 chain next ∧
    Pointer.Trace ⟨(LabelledCursor.plug ancestorContext source).erase, []⟩ ⟨next.pair.tree, []⟩ cost ∧
    cost + next.potential ≤ 39 * 19 + 54 + 62 + 50 := by
  obtain ⟨start, startupCost, startValid, startupTrace, _, _, startupBound⟩ :=
    Finger.History.Results.state_initialization_bounded
      (HeavyPath.Results.unit_positive (LabelledCursor.plug ancestorContext source))
  obtain ⟨down, downCost, downValid, downTrace, downBound, _⟩ :=
    Finger.History.Down.Results.downLeft startValid
  obtain ⟨up, upCost, upValid, upTrace, upBound, _⟩ :=
    Finger.History.Up.Results.upLeft downValid
  obtain ⟨next, rotateCost, nextValid, rotateTrace, rotateBound, _⟩ :=
    Finger.History.Rotation.Results.rotateRightChild upValid
  refine ⟨next, startupCost + downCost + upCost + rotateCost, nextValid,
    ((startupTrace.append downTrace).append upTrace).append rotateTrace, ?_⟩
  have nodes : (LabelledCursor.plug ancestorContext (.node chain 9 chain)).erase.size = 19 := rfl
  rw [nodes] at startupBound
  omega

-- A right-heavy join pushes into the full lower stack of a noncanonical
-- history. Its amortized and worst-case bounds apply to the same trace.
example : ∃ shape credit cost, History.Layout (fun _ => 1) (.node .nil 7 chain) shape credit ∧
    Pointer.Trace ⟨.node .nil fresh.tree, []⟩ ⟨shape, []⟩ cost ∧
    cost + credit ≤ 24 + fresh.potential ∧ (cost : ℝ) ≤ 10 + 14 * Real.logb 2 5 := by
  simpa only [Nat.add_zero, Nat.zero_add, show (Tree.node .nil fresh.tree).size = 5 from rfl, Nat.cast_ofNat] using
    History.Results.layout_join_bounded (x := 7) History.Layout.nil freshHistory (by norm_num)

-- Expose and rejoin the same repeated-payload source without rebuilding its
-- children. The shared code satisfies both cost analyses and a depth bound
-- at every physical interruption, including cuts inside either operation.
example : ∃ (shape : Tree) (credit : Nat) (ops : List Multifinger.Opcode),
    History.Layout (fun _ => 1) source shape credit ∧
    Multifinger.replay ops ⟨mixed.tree, []⟩ = some ⟨shape, []⟩ ∧
    ops.length + credit ≤ 48 + (mixed.potential + fresh.potential) ∧
    (ops.length : ℝ) ≤ 20 + 24 * Real.logb 2 9 ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨mixed.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨shape, []⟩ ∧
      ∀ rank : Fin 9, (Tree.depth middle.tree rank.val : ℝ) ≤ 27 + 39 * Real.logb 2 9 := by
  obtain ⟨a, b, lc, rc, first, left, right, firstReplay, firstBound, firstWorst, _⟩ :=
    History.Interruption.Results.expose_uniform mixedHistory
  obtain ⟨shape, credit, last, joined, lastReplay, lastBound, lastWorst, _⟩ :=
    History.Interruption.Results.join_uniform (key := 9) left right
  have leftSize : a.size = 4 := History.Results.layout_size left
  have rightSize : b.size = 4 := History.Results.layout_size right
  have size : (Tree.node a b).size = 9 := by simp only [Tree.size, leftSize, rightSize]
  have startSize : mixed.tree.size = 9 := rfl
  rw [size] at lastWorst
  rw [startSize] at firstWorst
  norm_num only [Nat.cast_ofNat] at firstWorst lastWorst
  have replay : Multifinger.replay (first ++ last) ⟨mixed.tree, []⟩ = some ⟨shape, []⟩ := by
    simp only [Multifinger.replay_append, firstReplay, Option.bind_some, lastReplay]
  have budget : ((first ++ last).length : ℝ) ≤ 20 + 24 * Real.logb 2 9 := by
    simp only [List.length_append, Nat.cast_add]
    linarith
  refine ⟨shape, credit, first ++ last, joined, replay, ?_, budget, ?_⟩
  · simp only [List.length_append]
    omega
  · intro cut
    obtain ⟨middle, prefixRun, suffixRun, depths⟩ :=
      StaticTree.Trace.Results.replay_prefix_bound replay budget cut
    refine ⟨middle, prefixRun, suffixRun, ?_⟩
    intro rank
    have drift := depths rank.val
    change (Tree.depth middle.tree rank.val : ℝ) ≤
      Tree.depth mixed.tree rank.val + (20 + 24 * Real.logb 2 9) at drift
    have original := History.Results.layout_depth_at mixedHistory (rank := ⟨rank.val, rank.isLt⟩)
    have total : HeavyPath.mass (fun _ => 1) source = 9 := by norm_num [source, chain, HeavyPath.mass]
    simp only [total, div_one] at original
    linarith

-- Nonuniform weights retain their weighted term at every interruption of
-- source exposure from a canonical recursive layout.
example : ∃ (credit : Nat) (shape a b : Tree) (lc rc : Nat) (ops : List Multifinger.Opcode),
    History.Layout (fun x : Nat => (x : ℝ) + 1) source shape credit ∧
    Multifinger.replay ops ⟨shape, []⟩ = some ⟨.node a b, []⟩ ∧
    ops.length + lc + rc ≤ 24 + credit ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨shape, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨.node a b, []⟩ ∧
      (Tree.depth middle.tree 4 : ℝ) ≤ 17 + 15 * Real.logb 2 (26 / 10) + 10 * Real.logb 2 9 := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1) source := by norm_num [source, chain, Positive]
  obtain ⟨credit, layout⟩ := History.Results.rebuild_history positive
  obtain ⟨a, b, lc, rc, ops, _, _, replay, amortized, _, prefixes⟩ := History.Interruption.Results.expose layout
  refine ⟨credit, _, a, b, lc, rc, ops, layout, replay, amortized, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  have bound := bounds ⟨4, by decide⟩
  have size : (rebuild (fun x : Nat => (x : ℝ) + 1) source).size = 9 := History.Results.layout_size layout
  rw [size] at bound
  refine ⟨middle, first, last, ?_⟩
  norm_num [source, chain, HeavyPath.mass, LabelledTree.erase, Tree.size, LabelledTree.inorder] at bound ⊢
  exact bound

-- The weighted certificates compose across exposure and rejoining. The root
-- has weight ten among total mass twenty-six; no population term is needed.
example : ∃ (initialCredit finalCredit : Nat) (initial final : Tree)
    (ops : List Multifinger.Opcode),
    History.Layout (fun x : Nat => (x : ℝ) + 1) source initial initialCredit ∧
    History.Layout (fun x : Nat => (x : ℝ) + 1) source final finalCredit ∧
    Multifinger.replay ops ⟨initial, []⟩ = some ⟨final, []⟩ ∧
    ops.length + finalCredit ≤ 48 + initialCredit ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨initial, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨final, []⟩ ∧
      (Tree.depth middle.tree 4 : ℝ) ≤ 48 + 60 * Real.logb 2 (26 / 10) := by
  have positive : Positive (fun x : Nat => (x : ℝ) + 1) source := by
    norm_num [source, chain, Positive]
  obtain ⟨initialCredit, layout⟩ := History.Results.rebuild_history positive
  obtain ⟨a, b, lc, rc, first, left, right, firstReplay, firstCost, _, firstPrefixes⟩ :=
    History.Interruption.Results.expose_weighted layout
  obtain ⟨final, finalCredit, last, joined, lastReplay, lastCost, _, lastPrefixes⟩ :=
    History.Interruption.Results.join_weighted (key := 9) left right (by norm_num)
  refine ⟨initialCredit, finalCredit, _, final, first ++ last, layout, joined, ?_, ?_, ?_⟩
  · simp only [Multifinger.replay_append, firstReplay, Option.bind_some, lastReplay]
  · simp only [List.length_append]
    omega
  · intro cut
    by_cases early : cut ≤ first.length
    · obtain ⟨middle, before, after, bounds⟩ := firstPrefixes cut
      refine ⟨middle, ?_, ?_, ?_⟩
      · simpa only [List.take_append_of_le_length early] using before
      · rw [List.drop_append_of_le_length early, Multifinger.replay_append, after]
        exact lastReplay
      · have bound := bounds ⟨4, by decide⟩
        norm_num [source, chain, HeavyPath.mass, LabelledTree.inorder] at bound
        linarith
    · obtain ⟨middle, before, after, bounds⟩ := lastPrefixes (cut - first.length)
      refine ⟨middle, ?_, ?_, ?_⟩
      · rw [List.take_append, List.take_of_length_le (by omega),
          Multifinger.replay_append, firstReplay]
        exact before
      · simpa only [List.drop_append, List.drop_eq_nil_of_le (by omega : first.length ≤ cut),
          List.nil_append] using after
      · have bound := bounds ⟨4, by decide⟩
        norm_num [source, chain, HeavyPath.mass, LabelledTree.inorder] at bound ⊢
        exact bound

-- Complete-stream interruption bounds also cover the nineteen-node inverted
-- state with frozen and fresh histories for equal source payloads. All six
-- instruction kinds occur, and the source cursor returns to its initial place.
private def fingerCommands : List Multifinger.Opcode :=
  [.downLeft, .upLeft, .downRight, .upRight, .downLeft,
    .rotateLeftChild, .downRight, .rotateRightChild]

example : ∃ (p : Finger.History.Simulation.Policy Nat) (out : Finger.History.Simulation.Output Nat),
    Finger.History.Simulation.PolicyBounded (fun _ => 1) p ∧
    Finger.History.Simulation.run p ⟨source, ancestorContext⟩ historyState fingerCommands = some out ∧
    out.source = ⟨source, ancestorContext⟩ ∧
    out.cost + out.state.potential ≤ 496 + historyState.potential ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨historyState.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < 19, (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 19 := by
  obtain ⟨p, bounded⟩ := Finger.History.Simulation.Results.policy_bounded_exists (fun _ : Nat => (1 : ℝ))
  have valid : Finger.History.Simulation.ConfigValid (fun _ => 1) ⟨source, ancestorContext⟩ historyState :=
    historyStateValid
  have legal : Finger.History.Simulation.sourceRun ⟨source, ancestorContext⟩ fingerCommands =
      some ⟨source, ancestorContext⟩ := rfl
  obtain ⟨out, completed, final, _, _, amortized⟩ := Finger.History.Simulation.Results.run_spec bounded.1 valid legal
  have size : historyState.pair.tree.size = 19 := Finger.History.Results.state_size historyStateValid
  refine ⟨p, out, bounded, completed, final, amortized, ?_⟩
  intro cut
  have prefixes := Finger.History.Simulation.Interruption.Results.run_uniform_prefix bounded valid completed cut
  norm_num only [size, Nat.cast_ofNat] at prefixes
  exact prefixes

-- Credit caps apply to these distinct valid histories and to the nested
-- payload occurrence; no canonical reconstruction premise is introduced.
example : frozen.potential ≤ 20 * chain.erase.size :=
  History.Results.layout_potential_bound frozenHistory

example : mixed.potential + fresh.potential ≤ 20 * source.erase.size :=
  History.Results.layout_potential_bound mixedHistory

end RotationBST.Tests.RecursiveHistory
