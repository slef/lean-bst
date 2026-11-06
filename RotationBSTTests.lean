module

public import RotationBST
public import RotationBSTTests.AbstractBoundary
public import RotationBSTTests.Axioms
public import RotationBSTTests.Arboral

-- Lazy Finger and GreedyASS paper regressions.
public import RotationBSTTests.ConditionalEntropy
public import RotationBSTTests.DynamicLazyFinger
public import RotationBSTTests.GreedyAccessedPotential
public import RotationBSTTests.GreedyAmortized
public import RotationBSTTests.GreedyBarrier
public import RotationBSTTests.GreedyColorCounts
public import RotationBSTTests.GreedyGreenAccess
public import RotationBSTTests.GreedyItems
public import RotationBSTTests.GreedyPerformance
public import RotationBSTTests.GreedyPhaseOne
public import RotationBSTTests.GreedyPhaseTwo
public import RotationBSTTests.GreedyPotential
public import RotationBSTTests.GreedyReference
public import RotationBSTTests.GreedyReferenceDistance
public import RotationBSTTests.GreedyReferenceTransitions
public import RotationBSTTests.GreedySnapshotCorners
public import RotationBSTTests.GreedyUnaccessedPotential
public import RotationBSTTests.GreedyVirgin
public import RotationBSTTests.GreedyVirginTransitions
public import RotationBSTTests.LazyFingerConsequences
public import RotationBSTTests.LazyFingerSeparation
public import RotationBSTTests.LazyFingerWeights
public import RotationBSTTests.MultipleTrees
public import RotationBSTTests.OptimalLazyFinger

-- Abstract deamortization, representation, and Splay regressions.
public import RotationBSTTests.DeamortizedSplay
public import RotationBSTTests.PopTart
public import RotationBSTTests.CherryPopTart
public import RotationBSTTests.CherryWeighted
public import RotationBSTTests.ChocolatePopTart
public import RotationBSTTests.ChocolateDepth
public import RotationBSTTests.TraceDepth
public import RotationBSTTests.PointerDetour
public import RotationBSTTests.DeamortizationScheduler
public import RotationBSTTests.ChocolatePop
public import RotationBSTTests.HeavyPath
public import RotationBSTTests.PairedHeavyPath
public import RotationBSTTests.RecursiveHeavyPath
public import RotationBSTTests.LocatedPopTart
public import RotationBSTTests.HeavyPathDepthStep
public import RotationBSTTests.HeavyPathDepth
public import RotationBSTTests.HeavyPathExposure
public import RotationBSTTests.RecursiveHistory
public import RotationBSTTests.FingerSimulation
public import RotationBSTTests.FingerRequests
public import RotationBSTTests.FingerHeavyPath
public import RotationBSTTests.FingerTransfer
public import RotationBSTTests.FingerRecursiveTransfer

-- ComboBST controller, snapshots, and finite-family regressions.
public import RotationBSTTests.WorkerPair
public import RotationBSTTests.ComboAnalysis
public import RotationBSTTests.ComboController
public import RotationBSTTests.ComboRounds
public import RotationBSTTests.ComboWorker
public import RotationBSTTests.ComboRefinement
public import RotationBSTTests.ComboCertificates
public import RotationBSTTests.TreeBuffer
public import RotationBSTTests.Snapshot
public import RotationBSTTests.StreamingSnapshot
public import RotationBSTTests.RecordingSnapshot

@[expose] public section

namespace RotationBST.Tests
open RotationBST

variable {t : Tree} {x k : Nat}

private def leaf : Tree := .node .nil .nil
private def two : Tree := .node leaf .nil
private def promoted : Tree := .node .nil leaf

-- Rank 0 becomes root in one rotation; rank 1 is already the root.
example : Access two promoted 0 1 := ⟨.step .right .refl, rfl⟩
example : Access two two 1 0 := ⟨.refl, rfl⟩
example : ¬ Access two .nil x k := fun h => h.2
example : ¬ Access two t 2 k := by
  intro h
  have := h.in_range
  change 2 < 2 at this
  omega

-- A rotation deep inside a subtree still costs exactly one.
example : Rotations (.node leaf two) (.node leaf promoted) 1 :=
  .step (.inRight .right) .refl

-- A complete two-request execution.
example : Execution two [0, 1] two 2 :=
  .cons ⟨.step .right .refl, rfl⟩
    (.cons ⟨.step .left .refl, rfl⟩ .nil)

example : workingSetNumber 5 [] 2 = 5 := by decide
example : workingSetNumber 5 [2] 2 = 1 := by decide
example : workingSetNumber 5 [2, 0, 1, 0] 2 = 3 := by decide

-- The online rule produces a legal offline execution on every valid input.
example (a : Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Execution t xs (a.runFrom past t xs).1 (a.runFrom past t xs).2 := by
  exact a.execution past t xs valid

/-- info: 'RotationBST.Rotate.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rotate.size_eq
/-- info: 'RotationBST.Access.in_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Access.in_range

-- Test the public correspondence, not just the implementation lemmas.
example : (two.labelFrom 0).inorder = [0, 1] := by decide
example : LabelledTree.Access (two.labelFrom 0) (promoted.labelFrom 0) 0 1 :=
  (Representation.access_iff two promoted 0 1).mp ⟨.step .right .refl, rfl⟩

-- Inorder keys alone do not determine shape: this distinction matters to the abstract.
example : two ≠ promoted ∧ (two.labelFrom 0).inorder = (promoted.labelFrom 0).inorder := by
  decide

example : ¬ ∃ u k, Execution .nil [0] u k := by
  rw [execution_exists_iff]
  simp [Tree.size]

example : ∃ u k, Execution .nil [] u k := ⟨.nil, 0, .nil⟩

-- Requests cannot be discarded from conventional cost, even up to a constant factor.
example (C : Nat) :
    moveToRootAlgorithm.totalCost leaf [0] > C * moveToRootAlgorithm.cost leaf [0] := by
  simp [Algorithm.totalCost, Algorithm.cost, Algorithm.runFrom,
    moveToRootAlgorithm, moveToRoot, leaf, Tree.size]

-- Kernel dependency audit: unexpected axioms (including sorryAx) fail the build.
/-- info: 'RotationBST.Representation.reconstruct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Representation.reconstruct

/-- info: 'RotationBST.Representation.access_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Representation.access_iff

/-- info: 'RotationBST.access_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms access_exists_iff

/-- info: 'RotationBST.execution_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execution_exists_iff

/-- info: 'RotationBST.workingSet_totalCost_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms workingSet_totalCost_iff

/-- info: 'RotationBST.Geometry.reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geometry.reset

-- Zig-zig must differ from repeated single rotations of the accessed node.
private def threeLeft : Tree := .node two .nil
private def threeRight : Tree := .node .nil (.node .nil leaf)
example : Splay.run threeLeft 0 = (threeRight, 2) := by decide
example : (Splay.run threeLeft 0).1 ≠ (moveToRoot threeLeft 0).1 := by decide
example : Splay.run threeRight 2 = (threeLeft, 2) := by decide

-- Both zig-zag orientations expose the middle key as a balanced root.
example : Splay.run (.node (.node .nil leaf) .nil) 1 = (.node leaf leaf, 2) := by decide
example : Splay.run (.node .nil (.node leaf .nil)) 1 = (.node leaf leaf, 2) := by decide
example : Splay.run leaf 0 = (leaf, 0) := by decide
example : Splay.run .nil 0 = (.nil, 0) := by decide
example : Splay.run two 2 = (two, 0) := by decide
example : Splay.algorithm.cost leaf [0, 0, 0] = 0 := by decide
example : Splay.algorithm.totalCost leaf [0, 0, 0] = 3 := by decide
example : workingSetSum 2 [] [0, 1, 0] = 6 := by decide

-- Arbitrary key types and arbitrary key spacings are covered.
example : ∃ u : LabelledTree String, u.erase = two ∧ u.inorder = ["alpha", "omega"] :=
  Representation.labels_exist two ["alpha", "omega"] rfl

-- Public theorem applications include the empty domain, rather than assuming n > 0.
example : Splay.algorithm.cost .nil [] ≤ 10 * workingSetSum 0 [] [] := by decide
example : HasWorkingSetBound Splay.algorithm := Splay.Results.hasWorkingSetBound
example : HasStaticOptimalityBound Splay.algorithm := Splay.Results.staticOptimality
example : HasStaticFingerBound Splay.algorithm := Splay.Results.staticFinger

example : ∃ k, k ≤ 3 * Splay.algorithm.totalCost two [0, 1] ∧
    Pointer.Execution two [0, 1] (Splay.algorithm.runFrom [] two [0, 1]).1 k :=
  Splay.Results.pointer_execution two [0, 1] (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)

/-- info: 'RotationBST.Splay.Results.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.correct
/-- info: 'RotationBST.Splay.Results.access_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.access_lemma
/-- info: 'RotationBST.Splay.Results.balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.balance
/-- info: 'RotationBST.Splay.Results.workingSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.workingSet
/-- info: 'RotationBST.Splay.Results.staticOptimality_all_accessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.staticOptimality_all_accessed
/-- info: 'RotationBST.Splay.Results.unified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.unified
/-- info: 'RotationBST.Splay.Results.pointer_workingSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.pointer_workingSet
/-- info: 'RotationBST.Bounds.workingSet_implies_staticOptimality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bounds.workingSet_implies_staticOptimality
/-- info: 'RotationBST.Bounds.staticOptimality_implies_staticFinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bounds.staticOptimality_implies_staticFinger
/-- info: 'RotationBST.Pointer.Results.to_rotations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pointer.Results.to_rotations
/-- info: 'RotationBST.Pointer.Results.to_pointer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pointer.Results.to_pointer
/-- info: 'RotationBST.Representation.arbitrary_rotations_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Representation.arbitrary_rotations_iff
/-- info: 'RotationBST.Representation.labels_exist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Representation.labels_exist

-- Update boundaries: splitting at a gap, joining ordered sets, rank renumbering.
example : Splay.Updates.split threeLeft 1 = ⟨leaf, promoted, 2⟩ := by decide
example : Splay.Updates.split two 0 = ⟨.nil, two, 0⟩ := by decide
example : Splay.Updates.join leaf leaf = (promoted, 0) := by decide
example : Splay.Updates.insert leaf 1 = (two, 0) := by decide
example : Splay.Updates.delete two 0 = (leaf, 1) := by decide
example : Splay.Updates.delete two 1 = (leaf, 0) := by decide
example : Splay.Updates.Execution 1 [.nil] 2 [.nil] 2 :=
  .cons (by decide) (.insert (t := .nil) (k := 0) (by decide))
    (.cons (by decide) (.delete (t := leaf) (x := 0) (by decide)) (.nil (by decide)))

-- Conditional splaying must actually leave a short nonroot search unchanged.
example : Splay.conditionalStep (fun _ => 1) two 0 = (two, 0) := by
  norm_num [Splay.conditionalStep, Splay.mass_unit, two, leaf, Tree.size,
    Splay.run, Splay.locate, Splay.splayAt, Real.logb_self_eq_one]

-- A deterministic one-key distribution has static search cost exactly one.
example (j : Nat) : Splay.snapshotAt 1 (fun _ => 1) leaf j = 1 := by
  induction j with
  | zero => norm_num [Splay.snapshotAt, Splay.meanSearch, Splay.run, Splay.locate,
      leaf, Tree.size, Splay.splayAt]
  | succ j ih => simpa [Splay.snapshotAt, Splay.run, Splay.locate, leaf, Tree.size,
      Splay.splayAt] using ih

/-- info: 'RotationBST.Splay.Results.access_lemma_subtree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.access_lemma_subtree
/-- info: 'RotationBST.Splay.Results.long_splay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.long_splay
/-- info: 'RotationBST.Splay.Results.snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.snapshot
/-- info: 'RotationBST.Splay.Updates.Results.balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Updates.Results.balance
/-- info: 'RotationBST.Splay.Updates.Results.split_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Updates.Results.split_spec
/-- info: 'RotationBST.Splay.Results.staticFinger_all_accessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Results.staticFinger_all_accessed

private def stringTwo : LabelledTree String :=
  .node (.node .nil "alpha" .nil) "omega" .nil
private def stringPromoted : LabelledTree String :=
  .node .nil "alpha" (.node .nil "omega" .nil)

example : LabelledTree.Access stringTwo stringPromoted "alpha" 1 :=
  (Representation.arbitrary_access_iff stringTwo stringPromoted
    (by decide) (by decide) 0 1 (by decide)).mp ⟨.step .right .refl, rfl⟩

example : LabelledTree.Execution stringTwo ["alpha", "omega"] stringTwo 2 :=
  (Representation.execution_on_keys_iff ["alpha", "omega"] (by decide)
    [0, 1] stringTwo stringTwo rfl rfl 2).mp
      (.cons ⟨.step .right .refl, rfl⟩ (.cons ⟨.step .left .refl, rfl⟩ .nil))

example : Representation.fromBinaryTree (Representation.toBinaryTree two) = two :=
  Representation.binaryTreeEquiv.left_inv two
example : (Representation.toBinaryTree two).numNodes = 2 := by decide

example : Splay.Updates.LocalExecution [.nil] [0, 1] [.nil] 2 :=
  .cons (.insert (t := .nil) (k := 0) (by decide))
    (.cons (.delete (t := leaf) (x := 0) (by decide)) .nil)

/-- info: 'RotationBST.Representation.arbitrary_access_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Representation.arbitrary_access_iff
/-- info: 'RotationBST.Representation.execution_on_keys_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Representation.execution_on_keys_iff
/-- info: 'RotationBST.Representation.binaryTreeEquiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Representation.binaryTreeEquiv
/-- info: 'RotationBST.Splay.Updates.Results.balance_initially_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Splay.Updates.Results.balance_initially_empty

/-- info: 'RotationBST.Pointer.Lazy.Results.commute' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pointer.Lazy.Results.commute
/-- info: 'RotationBST.Pointer.Lazy.Results.postpone_access' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pointer.Lazy.Results.postpone_access

end RotationBST.Tests

/-- info: 'RotationBST.Pointer.Results.to_pointer_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationBST.Pointer.Results.to_pointer_lazy

/-- info: 'RotationBST.Pointer.Lazy.Online.Results.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationBST.Pointer.Lazy.Online.Results.simulation

/-- info: 'RotationBST.Splay.Results.scanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationBST.Splay.Results.scanning
/-- info: 'RotationBST.Splay.Results.pointer_scanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationBST.Splay.Results.pointer_scanning

/-- info: 'RotationBST.Splay.Results.staticOptimality_fixedTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationBST.Splay.Results.staticOptimality_fixedTree

namespace RotationBST.Tests.Scanning

private def leftVine : Nat → Tree
  | 0 => .nil
  | n + 1 => .node (leftVine n) .nil

-- A long initial left path exercises repeated zig-zig pairs and later successors.
example : Splay.algorithm.cost (leftVine 10) (List.range 10) = 28 := by decide
example : (Splay.algorithm.runFrom [] (leftVine 10) (List.range 10)).1 = leftVine 10 := by decide
example : Splay.algorithm.cost (spine 10 .nil) (List.range 10) = 9 := by decide
example : StaticTree.cost (leftVine 10) (List.range 10) = 55 := by decide

end RotationBST.Tests.Scanning

namespace RotationBST.Tests.Ordering

-- An arbitrary labelling need not be a BST; canonical ranks always are.
example : ¬ (LabelledTree.node (LabelledTree.node .nil (2 : Nat) .nil) 1 .nil).Ordered := by
  simp [LabelledTree.Ordered, LabelledTree.inorder]

example : (Tree.node (Tree.node .nil .nil) .nil |>.labelFrom 7).Ordered :=
  Representation.ordered_label _ _

end RotationBST.Tests.Ordering
