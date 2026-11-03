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

-- Part II: bounds and their relations.
public import RotationBST.Bounds.WorkingSet.Abstract
public import RotationBST.Bounds.Abstract
public import RotationBST.Bounds.Unified.Abstract
public import RotationBST.Bounds.Implications.Abstract
public import RotationBST.Bounds.StaticTree.Abstract
public import RotationBST.Bounds.Interleave.Abstract
public import RotationBST.Bounds.Normalization.Abstract

-- Part III: algorithms.
public import RotationBST.Algorithms.MoveToRoot.Abstract
public import RotationBST.Algorithms.Splay.Abstract
public import RotationBST.Algorithms.GreedyASS.Abstract
public import RotationBST.Algorithms.Simulation.Abstract
public import RotationBST.Algorithms.Tango.Abstract

-- Appendix: supporting structures.
public import RotationBST.Structures.Treap.Abstract
public import RotationBST.Structures.SplitTree.Abstract

@[expose] public section

/-! Entry point importing the complete library. The `Abstract.lean` modules
listed above are the reading interface; see `docs/organization.md`. -/
