module

public import RotationBST.Algorithms.Combination.Worker.Pair.Transport

@[expose] public section
namespace RotationBST.Combo.Worker.Pair

variable {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool)

theorem attempt_left (x fuel : Nat) (state : α) :
    Controller.attempt (worker left right leftSide rightSide) false x fuel (.inl state) =
      let result := Controller.attempt left leftSide x fuel state
      ⟨.inl result.state, result.left, result.done⟩ :=
  attempt_map left (worker left right leftSide rightSide) leftSide false Sum.inl (fun _ _ => rfl) x fuel state

theorem access_left {state : α} {final : Sum α β} {x cost : Nat} :
    Worker.Access (worker left right leftSide rightSide) false (.inl state) x final cost ↔
      ∃ next, final = .inl next ∧ Worker.Access left leftSide state x next cost := by
  constructor
  · exact access_pullback Sum.inl (fun _ _ => rfl)
  · rintro ⟨next, rfl, ran⟩
    exact access_map Sum.inl (fun _ _ => rfl) ran

theorem requests_left {state : α} {final : Sum α β} {xs : List Nat} {cost : Nat} :
    Worker.Requests (worker left right leftSide rightSide) false (.inl state) xs final cost ↔
      ∃ next, final = .inl next ∧ Worker.Requests left leftSide state xs next cost := by
  constructor
  · exact requests_pullback Sum.inl (fun _ _ => rfl)
  · rintro ⟨next, rfl, ran⟩
    exact requests_map Sum.inl (fun _ _ => rfl) ran

theorem attempt_right (x fuel : Nat) (state : β) :
    Controller.attempt (worker left right leftSide rightSide) true x fuel (.inr state) =
      let result := Controller.attempt right rightSide x fuel state
      ⟨.inr result.state, result.left, result.done⟩ :=
  attempt_map right (worker left right leftSide rightSide) rightSide true Sum.inr (fun _ _ => rfl) x fuel state

theorem access_right {state : β} {final : Sum α β} {x cost : Nat} :
    Worker.Access (worker left right leftSide rightSide) true (.inr state) x final cost ↔
      ∃ next, final = .inr next ∧ Worker.Access right rightSide state x next cost := by
  constructor
  · exact access_pullback Sum.inr (fun _ _ => rfl)
  · rintro ⟨next, rfl, ran⟩
    exact access_map Sum.inr (fun _ _ => rfl) ran

theorem requests_right {state : β} {final : Sum α β} {xs : List Nat} {cost : Nat} :
    Worker.Requests (worker left right leftSide rightSide) true (.inr state) xs final cost ↔
      ∃ next, final = .inr next ∧ Worker.Requests right rightSide state xs next cost := by
  constructor
  · exact requests_pullback Sum.inr (fun _ _ => rfl)
  · rintro ⟨next, rfl, ran⟩
    exact requests_map Sum.inr (fun _ _ => rfl) ran

end RotationBST.Combo.Worker.Pair
