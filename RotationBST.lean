module

-- Part I: models and their equivalences.
public import RotationBST.Models.Rotation.Abstract
public import RotationBST.Models.Rotation.Rotations
public import RotationBST.Models.Rotation.Connectivity.Abstract
public import RotationBST.Models.Rotation.Existence.Abstract
public import RotationBST.Models.Labelled.Abstract
public import RotationBST.Models.Labelled.Ordering.Abstract
public import RotationBST.Models.Labelled.Mathlib.Abstract
public import RotationBST.Models.Online.Abstract
public import RotationBST.Models.Pointer.Abstract
public import RotationBST.Models.Region.View.Abstract
public import RotationBST.Models.Geometric.Abstract
public import RotationBST.Models.Equivalence.Abstract

public import RotationBST.Models.Labelled.Search.Abstract
public import RotationBST.Models.LinkedSearch.Abstract
public import RotationBST.Models.Pointer.Detour.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import RotationBST.Models.Pointer.Walk.Abstract

-- Part II: bounds and their relations.
public import RotationBST.Bounds.WorkingSet.Abstract
public import RotationBST.Bounds.Abstract
public import RotationBST.Bounds.Unified.Abstract
public import RotationBST.Bounds.Implications.Abstract
public import RotationBST.Bounds.DynamicFinger.Abstract
public import RotationBST.Bounds.Logarithmic.Abstract
public import RotationBST.Bounds.StaticTree.Abstract
public import RotationBST.Bounds.Interleave.Abstract
public import RotationBST.Bounds.Normalization.Abstract

public import RotationBST.Bounds.LazyFinger.Abstract
public import RotationBST.Bounds.LazyFinger.Random.Abstract
public import RotationBST.Bounds.LazyFinger.Dynamic.Abstract
public import RotationBST.Bounds.LazyFinger.Sequential.Abstract
public import RotationBST.Bounds.LazyFinger.Separation.Abstract
public import RotationBST.Bounds.LazyFinger.Consequences.Abstract
public import RotationBST.Bounds.ConditionalEntropy.Abstract

public import RotationBST.Bounds.Interleave.BitReversal.Abstract
public import RotationBST.Bounds.LazyFinger.Edges.Abstract
public import RotationBST.Bounds.LazyFinger.Neighborhood.Abstract
public import RotationBST.Bounds.StaticTree.Trace.Abstract

-- Classical search trees (Part III of the book).
public import RotationBST.Classical.Static.Abstract

-- Part III: algorithms.
public import RotationBST.Algorithms.MoveToRoot.Abstract
public import RotationBST.Algorithms.Splay.Abstract
public import RotationBST.Algorithms.GreedyASS.Abstract
public import RotationBST.Algorithms.Simulation.Abstract
public import RotationBST.Algorithms.Tango.Abstract

public import RotationBST.Algorithms.OptimalLazyFinger.Work.Abstract
public import RotationBST.Algorithms.MultipleTrees.Abstract
public import RotationBST.Algorithms.GreedyASS.Performance.Abstract
public import RotationBST.Algorithms.GreedyASS.Combination.Deamortized.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Abstract
public import RotationBST.Algorithms.Tango.Preferences.Initialization.Abstract
public import RotationBST.Algorithms.Tango.Combination.Abstract

public import RotationBST.Algorithms.GreedyASS.Barrier.Abstract
public import RotationBST.Algorithms.GreedyASS.Items.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Virgin.Abstract
public import RotationBST.Algorithms.OptimalLazyFinger.Abstract
public import RotationBST.Algorithms.Deamortization.Window.Abstract
public import RotationBST.Algorithms.Deamortization.Scheduler.Abstract
public import RotationBST.Algorithms.Deamortization.Weighted.Abstract
public import RotationBST.Algorithms.Deamortization.Finger.Abstract
public import RotationBST.Algorithms.Deamortization.Algorithm.Abstract
public import RotationBST.Algorithms.Splay.Deamortization.Abstract
public import RotationBST.Algorithms.Combination.Analysis.Abstract
public import RotationBST.Algorithms.Combination.Controller.Abstract
public import RotationBST.Algorithms.Combination.Family.Abstract
public import RotationBST.Algorithms.Combination.Family.Physical.Abstract
public import RotationBST.Algorithms.Combination.Online.Abstract
public import RotationBST.Algorithms.Combination.Online.Replay.Abstract
public import RotationBST.Algorithms.Combination.Refinement.Abstract
public import RotationBST.Algorithms.Combination.Rounds.Abstract
public import RotationBST.Algorithms.Combination.Rounds.Certificates.Abstract
public import RotationBST.Algorithms.Combination.Worker.Abstract
public import RotationBST.Algorithms.Combination.Worker.Pair.Abstract

-- Appendix: supporting structures.
public import RotationBST.Structures.Treap.Abstract
public import RotationBST.Structures.SplitTree.Abstract

public import RotationBST.Structures.PrefixSum.Abstract
public import RotationBST.Structures.PopTart.Abstract
public import RotationBST.Structures.PopTart.Vanilla.Abstract
public import RotationBST.Structures.PopTart.Cherry.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Abstract
public import RotationBST.Structures.PopTart.Located.Abstract
public import RotationBST.Structures.HeavyPath.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.History.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.History.Interruption.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Down.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Up.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Rotation.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Abstract
public import RotationBST.Structures.TreeBuffer.Cells.Abstract
public import RotationBST.Structures.TreeBuffer.Scan.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Abstract

@[expose] public section

/-! Entry point importing the complete library. The `Abstract.lean` modules
listed above are the reading interface; see `docs/organization.md`. -/
