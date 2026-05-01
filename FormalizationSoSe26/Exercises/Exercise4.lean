import Mathlib.Tactic

section set_theory

example (X : Type) (a : X) : a ∈ (∅ : Set X) → False := by
  sorry

example (X : Type) (A B : Set X) (hAinB : A ⊆ B) : A ∪ B = B := by
  sorry

example (X : Type) (A B : Set X) (hab : A ∩ B = ∅) : A \ B = A := by
  sorry


example (X : Type) (A B C : Set X) : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  sorry

example (X : Type) (A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  sorry

example (X : Type) (A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  sorry

end set_theory

section indexed_operations

-- For the exercises in this section you will need to use:
#check Set.mem_iUnion
#check Set.mem_inter_iff

/- You can use them directly, but it's probably easier to use:
`simp only [Set.mem_iUnion]`
`simp only [Set.mem_iInter]`
`simp only [Set.mem_inter_iff]`
-/

example {α I : Type} (A : I → Set α) (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  sorry

example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

example {α I : Type} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

end indexed_operations

section functions_basics

/- The `Empty` type is a type with no elements.
That means if I have `x : Empty`, then `cases x` will close every goal!
Let's prove that every function out of `Empty` is injective. -/
example (X : Type) (f : Empty → X) : Function.Injective f := by
  sorry

/- The `Unit` type is a type with one element.
That means if `x : Unit`, then `x = Unit.unit`.
We obtain that via `cases x`.
Let's use that to prove that every function out of `Unit` is injective. -/
example (X : Type) (f : Unit → X) : Function.Injective f := by
  sorry

-- Recall that if a type `X` is inhabited, then there is a default element `default : X`.
example (X : Type) [Inhabited X] (f : X → Unit) : Function.Surjective f := by
  sorry

example (X Y : Type) (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := by
  sorry

example {X Y : Type} {f : X → Y} (A : Set X) (h : Function.Injective f) : f ⁻¹' (f '' A) ⊆ A := by
  sorry

example {X Y : Type} {f : X → Y} (B : Set Y) : f '' (f ⁻¹' B) ⊆ B := by
  sorry

example {X Y : Type} {f : X → Y} (B : Set Y) (h : Function.Surjective f) : B ⊆ f '' (f ⁻¹' B) := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  sorry


example {X Y : Type} {A B : Set Y} (f : X → Y) (h : A ⊆ B) : f ⁻¹' A ⊆ f ⁻¹' B := by
  sorry

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) (h : Function.Injective f) :
  f '' A ∩ f '' B ⊆ f '' (A ∩ B) := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) : f '' A \ f '' B ⊆ f '' (A \ B) := by
  sorry

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' A \ f ⁻¹' B ⊆ f ⁻¹' (A \ B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' A ∩ B = f '' (A ∩ f ⁻¹' B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' (A ∩ f ⁻¹' B) ⊆ f '' A ∩ B := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∩ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∩ B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∪ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∪ B) := by
  sorry

end functions_basics


section squares_and_roots
/- For the next exercises we need to know some facts about
squares and square roots.-/
#check Real.sq_sqrt
#check Real.sqrt_sq
#check sq_nonneg

-- You also want to benefit from the `calc` tactic.
example : Set.InjOn Real.sqrt { x | x ≥ 0 } := by
  sorry

example : Set.InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : (Set.range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end squares_and_roots
