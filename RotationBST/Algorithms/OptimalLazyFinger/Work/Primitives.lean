module

public import RotationBST.Algorithms.OptimalLazyFinger.Work.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work
open Cslib.Algorithms.Lean

@[simp] theorem charge_ret {α : Type} (n : Nat) (x : α) : (charge n x).ret = x := rfl
@[simp] theorem charge_time {α : Type} (n : Nat) (x : α) : (charge n x).time = n := rfl

@[simp] theorem mapList_ret {α β : Type} (f : α → Computation β) (xs : List α) :
    (mapList f xs).ret = xs.map (fun x => (f x).ret) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapList, ih]

theorem mapList_time_le {α β : Type} (f : α → Computation β) (xs : List α) (C : Nat)
    (hf : ∀ x ∈ xs, (f x).time ≤ C) : (mapList f xs).time ≤ xs.length * (C + 1) + 1 := by
  induction xs with
  | nil => simp [mapList]
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [mapList, TimeM.time_bind, charge_time, List.length_cons]
    nlinarith

@[simp] theorem arrayOfFn_ret {α : Type} (n : Nat) (f : Fin n → Computation α) :
    (arrayOfFn n f).ret = Array.ofFn (fun i => (f i).ret) := by
  simp only [arrayOfFn, TimeM.ret_bind, charge_ret, mapList_ret]
  apply Array.ext
  · simp
  · intro i hi hj
    simp [List.getElem_map, List.getElem_finRange]

theorem arrayOfFn_time_le {α : Type} (n : Nat) (f : Fin n → Computation α) (C : Nat)
    (hf : ∀ i, (f i).time ≤ C) : (arrayOfFn n f).time ≤ n * (C + 3) + 3 := by
  have h := mapList_time_le f (List.finRange n) C (fun i _ => hf i)
  simp only [List.length_finRange] at h
  simp only [arrayOfFn, TimeM.time_bind, charge_ret, charge_time]
  nlinarith

@[simp] theorem ofFn_constant {α : Type} (n : Nat) (x : α) :
    Array.ofFn (fun _ : Fin n => x) = Array.replicate n x := by
  apply Array.ext
  · simp
  · intros; simp

@[simp] theorem replicate_ret {α : Type} (n : Nat) (x : α) :
    (replicate n x).ret = Array.replicate n x := rfl

@[simp] theorem replicate_time {α : Type} (n : Nat) (x : α) :
    (replicate n x).time = n + 1 := rfl

end RotationBST.OptimalLazyFinger.Work
