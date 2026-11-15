module

public import RotationBST.Models.RealWorld.Linked.Preservation
public import RotationBST.Models.Labelled.Cursor.Map.Basic

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Pointer)
variable {w e regs : Nat}

theorem effect_in_context (s : State w e regs) (side other : Fin 3) (x y : Nat)
    (rx ry : Record w e regs) (cs : List (LabelledCursor.Frame (Label w e)))
    (cur : s.ptr 0 = some x) (hx : s.heap[x]? = some rx) (hy : s.heap[y]? = some ry)
    (px : rx.ptr 2 = some y) (py : ry.ptr 2 = parent cs)
    (ctx : Context s.heap (some y) cs)
    (apart : ∀ z ∈ outside cs, z ≠ x ∧ z ≠ y ∧ rx.ptr other ≠ some z) :
    let t := run (rotate side other) 18 (start s)
    t.heap = reconnected s.heap x y (rx.ptr other) cs side other ∧
      t.ptr 0 = some x ∧ t.ptr 1 = if parent cs = none then some x else s.ptr 1 := by
  cases cs with
  | nil => simpa [reconnected, parent, write] using
      rotate_root_effect s side other x y rx ry cur hx hy px py
  | cons f cs =>
    cases f with
    | left g r =>
      have sep := apart g.1 (by simp [outside])
      have hh := rotate_inner_effect s side other x y g.1 rx ry
        (node (some y) (root r) (parent cs) g) cur hx hy ctx.1 px py sep.1 sep.2.1 sep.2.2
      simpa [reconnected, parent, contextSide, node] using hh
    | right l g =>
      have sep := apart g.1 (by simp [outside])
      have ne : root l ≠ some y := by
        intro heq
        have mem := root_mem heq
        have := apart y (by simp [outside, mem])
        simp at this
      have hh := rotate_inner_effect s side other x y g.1 rx ry
        (node (root l) (some y) (parent cs) g) cur hx hy ctx.1 px py sep.1 sep.2.1 sep.2.2
      simpa [reconnected, parent, contextSide, node, ne] using hh

theorem root_plug_congr (cs : List (LabelledCursor.Frame (Label w e)))
    {s t : Tree w e} (eq : root s = root t) :
    root (LabelledCursor.plug cs s) = root (LabelledCursor.plug cs t) := by
  induction cs generalizing s t with
  | nil => exact eq
  | cons f cs ih => cases f <;> exact ih rfl

theorem root_after_rotation (cs : List (LabelledCursor.Frame (Label w e)))
    (a b c : Tree w e) (x y : Label w e) :
    root (LabelledCursor.plug cs (.node a x (.node b y c))) =
      if parent cs = none then some x.1 else
        root (LabelledCursor.plug cs (.node (.node a x b) y c)) := by
  cases cs with
  | nil => rfl
  | cons f cs => cases f <;> exact root_plug_congr cs rfl

theorem keys_inorder (t : Tree w e) :
    (keys t).inorder = t.inorder.map (fun x => (x.2 0).toNat) := by
  induction t <;> simp_all [keys, LabelledTree.inorder]

set_option maxHeartbeats 800000 in
theorem rotateLeftChild {s : State w e regs} {a b c : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node a x b, .left y c :: cs⟩) :
    Realizes (run (rotate 0 1) 18 (start s)) ⟨.node a x (.node b y c), cs⟩ := by
  have nd : (addresses a ++ x.1 :: addresses b ++ y.1 :: addresses c ++ outside cs).Nodup := by
    have := (nodup_plug (.left y c :: cs) (.node a x b)).mp h.distinct
    simpa [outside, List.append_assoc] using this
  have hn := nd
  simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hn
  have apart : ∀ z ∈ outside cs, z ≠ x.1 ∧ z ≠ y.1 ∧ root b ≠ some z := by
    intro z hz
    refine ⟨by grind, by grind, ?_⟩
    intro heq; have := root_mem heq; grind
  have eff := effect_in_context s 0 1 x.1 y.1
    (node (root a) (root b) (some y.1) x)
    (node (some x.1) (root c) (parent cs) y) cs h.cursor h.focus.1 h.context.1
    (by simp [node]) (by simp [node]) h.context.2.2 (by simpa [node] using apart)
  have localRep := pivot_left h.focus h.context.1 h.context.2.1
    (List.Nodup.of_append_left nd)
  have nd' : (addresses (.node a x (.node b y c)) ++ outside cs).Nodup := by
    simpa [List.append_assoc] using nd
  obtain ⟨rep, ctx⟩ := reconnect localRep h.context.2.2 nd'
    (by simp) (by simp) (fun z hz => by have := root_mem hz; simp [this]) rfl
  have trace : LabelledCursor.perform .rotateLeftChild
      ⟨.node a x b, .left y c :: cs⟩ = some ⟨.node a x (.node b y c), cs⟩ := rfl
  have inorder := LabelledCursor.perform_inorder trace
  have ad : addresses (LabelledCursor.plug cs (.node a x (.node b y c))) =
      addresses (LabelledCursor.plug (.left y c :: cs) (.node a x b)) := by
    exact congrArg (List.map Prod.fst) inorder.symm
  have len : (run (rotate 0 1) 18 (start s)).heap.length = s.heap.length := by
    rw [eff.1]
    simp [reconnected, pivot]
  obtain ⟨time, _, exec⟩ := rotate_time s 0 1
  refine ⟨exec.valid h.valid, ?_, ?_, ?_, ?_, ?_, eff.2.1, ?_, by simp⟩
  · rw [eff.1]; exact rep
  · rw [eff.1]; exact ctx
  · change (addresses (LabelledCursor.plug cs _)).Nodup
    rw [ad]; exact h.distinct
  · intro z; rw [len]; simpa only [LabelledCursor.Config.tree, ad] using h.covers z
  · rw [Representation.ordered_iff, keys_inorder, ← inorder]
    simpa only [keys_inorder] using (Representation.ordered_iff _).mp h.ordered
  · rw [eff.2.2, h.rootReg]
    exact (root_after_rotation cs a b c x y).symm

theorem root_after_rotation_right (cs : List (LabelledCursor.Frame (Label w e)))
    (a b c : Tree w e) (x y : Label w e) :
    root (LabelledCursor.plug cs (.node (.node a y b) x c)) =
      if parent cs = none then some x.1 else
        root (LabelledCursor.plug cs (.node a y (.node b x c))) := by
  cases cs with
  | nil => rfl
  | cons f cs => cases f <;> exact root_plug_congr cs rfl

set_option maxHeartbeats 800000 in
theorem rotateRightChild {s : State w e regs} {a b c : Tree w e} {x y : Label w e}
    {cs : List (LabelledCursor.Frame (Label w e))}
    (h : Realizes s ⟨.node b x c, .right a y :: cs⟩) :
    Realizes (run (rotate 1 0) 18 (start s)) ⟨.node (.node a y b) x c, cs⟩ := by
  have nd : (addresses a ++ y.1 :: addresses b ++ x.1 :: addresses c ++ outside cs).Nodup := by
    have := (nodup_plug (.right a y :: cs) (.node b x c)).mp h.distinct
    simp only [outside, addresses_node, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at this ⊢
    grind
  have hn := nd
  simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hn
  have apart : ∀ z ∈ outside cs, z ≠ x.1 ∧ z ≠ y.1 ∧ root b ≠ some z := by
    intro z hz
    refine ⟨by grind, by grind, ?_⟩
    intro heq; have := root_mem heq; grind
  have eff := effect_in_context s 1 0 x.1 y.1
    (node (root b) (root c) (some y.1) x)
    (node (root a) (some x.1) (parent cs) y) cs h.cursor h.focus.1 h.context.1
    (by simp [node]) (by simp [node]) h.context.2.2 (by simpa [node] using apart)
  have localRep := pivot_right h.focus h.context.1 h.context.2.1
    (List.Nodup.of_append_left nd)
  have nd' : (addresses (.node (.node a y b) x c) ++ outside cs).Nodup := by
    simpa [List.append_assoc] using nd
  obtain ⟨rep, ctx⟩ := reconnect localRep h.context.2.2 nd'
    (by simp) (by simp) (fun z hz => by have := root_mem hz; simp [this]) rfl
  have trace : LabelledCursor.perform .rotateRightChild
      ⟨.node b x c, .right a y :: cs⟩ = some ⟨.node (.node a y b) x c, cs⟩ := rfl
  have inorder := LabelledCursor.perform_inorder trace
  have ad : addresses (LabelledCursor.plug cs (.node (.node a y b) x c)) =
      addresses (LabelledCursor.plug (.right a y :: cs) (.node b x c)) := by
    exact congrArg (List.map Prod.fst) inorder.symm
  have len : (run (rotate 1 0) 18 (start s)).heap.length = s.heap.length := by
    rw [eff.1]
    simp [reconnected, pivot]
  obtain ⟨time, _, exec⟩ := rotate_time s 1 0
  refine ⟨exec.valid h.valid, ?_, ?_, ?_, ?_, ?_, eff.2.1, ?_, by simp⟩
  · rw [eff.1]; exact rep
  · rw [eff.1]; exact ctx
  · change (addresses (LabelledCursor.plug cs _)).Nodup
    rw [ad]; exact h.distinct
  · intro z; rw [len]; simpa only [LabelledCursor.Config.tree, ad] using h.covers z
  · rw [Representation.ordered_iff, keys_inorder, ← inorder]
    simpa only [keys_inorder] using (Representation.ordered_iff _).mp h.ordered
  · rw [eff.2.2, h.rootReg]
    exact (root_after_rotation_right cs a b c x y).symm

end RotationBST.RealWorld.Linked
