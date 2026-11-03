module

public import RotationBST.Algorithms.Splay.Scanning.Pairing
public import RotationBST.Algorithms.Splay.Correctness

@[expose] public section

namespace RotationBST.Splay.Scanning.Marked

theorem plug_append (cs ds : List Marked) (t : Marked) :
    plug (cs ++ ds) t = plug ds (plug cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons b cs ih => exact ih (.node t b)

/-- The exposed minimum and its nearest-first list of red ancestors. -/
theorem decompose (t : Marked) (ready : t.Ready) (nonempty : t.tree ≠ .nil) :
    ∃ r cs, t = plug cs (.node (.hole .nil) r) ∧
      locate t.tree 0 = ⟨.node .nil r.tree, cs.map fun b => Pointer.Frame.left b.tree⟩ := by
  induction t with
  | hole u => exact False.elim (nonempty ready)
  | node l r il _ =>
      cases l with
      | hole u =>
          change u = .nil at ready
          subst u
          exact ⟨r, [], rfl, by simp [tree, locate, Tree.size]⟩
      | node a b =>
          obtain ⟨q, cs, htree, hloc⟩ := il ready (by simp [tree])
          refine ⟨q, cs ++ [r], ?_, ?_⟩
          · rw [plug_append]; exact congrArg (fun z => Marked.node z r) htree
          · have hl : 0 < (Marked.node a b).tree.size := by simp [tree, Tree.size]
            change locate (.node (Marked.node a b).tree r.tree) 0 = _
            rw [locate, ite_eq_left hl, hloc]
            simp only [List.map_append, List.map_cons, List.map_nil]

end RotationBST.Splay.Scanning.Marked

namespace RotationBST.Splay.Scanning
open Marked

/-- A black right spine is represented by the red left subtree at each node. -/
def spine : List Marked → Tree
  | [] => .nil
  | l :: ls => .node l.tree (spine ls)

def initialSpine : Tree → List Marked
  | .nil => []
  | .node l r => .hole l :: initialSpine r

theorem initialSpine_tree (t : Tree) : spine (initialSpine t) = t := by
  induction t with
  | nil => rfl
  | node l r _ ih => simp [initialSpine, spine, Marked.tree, ih]

theorem initialSpine_valid (t : Tree) : AllValid (initialSpine t) := by
  induction t with
  | nil => simp [AllValid, initialSpine]
  | node l r _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · trivial
      · exact ih a ha

theorem initialSpine_potential (t : Tree) : totalPotential (initialSpine t) ≤ 18 * t.size := by
  induction t with
  | nil => simp [initialSpine, totalPotential, Tree.size]
  | node l r _ ih =>
      change 18 * l.size + totalPotential (initialSpine r) ≤ 18 * (l.size + 1 + r.size)
      omega

theorem spine_append (ls rs : List Marked) :
    spine (ls ++ rs) =
      ls.foldr (fun l rest => Tree.node l.tree rest) (spine rs) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [spine, ih]

/-- The ghost pairing operation has exactly the shape produced by ordinary
bottom-up splaying of the successor of the current root. -/
theorem consume_splay (r : Marked) (cs : List Marked) (rest : List Marked) (before : Tree) :
    splayAt .nil r.tree ((cs.map fun b => Pointer.Frame.left b.tree) ++
      [.left (spine rest), .right before]) =
      .node (.node before .nil) (spine (consume r cs ++ rest)) := by
  match cs with
  | [] => rfl
  | [b] => rfl
  | b :: c :: cs =>
      exact consume_splay (.node r (.node b c)) cs rest before
termination_by cs.length

end RotationBST.Splay.Scanning
