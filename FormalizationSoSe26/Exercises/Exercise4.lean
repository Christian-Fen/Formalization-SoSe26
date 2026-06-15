import Mathlib.Tactic

section set_theory

example (X : Type) (a : X) : a ∈ (∅ : Set X) → False := by
  intro f
  exact f

example (X : Type) (A B : Set X) (hAinB : A ⊆ B) : A ∪ B = B := by
  ext f
  constructor
  · intro g
    rcases g with ga|gb
    · exact hAinB ga
    · exact gb
  · intro h
    right
    exact h

example (X : Type) (A B : Set X) (hab : A ∩ B = ∅) : A \ B = A := by
  ext f
  constructor
  · intro g
    obtain ⟨ga,gb⟩ := g
    exact ga
  · intro h
    constructor
    · exact h
    · intro i
      have j : f ∈ A ∩ B := ⟨h,i⟩
      --by {
      --  constructor
      --  · exact h
      --  · exact i
      --}
      rw[hab] at j
      contradiction


example (X : Type) (A B C : Set X) : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext f
  constructor
  · intro g
    obtain ⟨ga, gbc⟩ := g
    rcases gbc with gb|gc
    · left
      constructor
      · exact ga
      · exact gb
    · right
      constructor
      · exact ga
      · exact gc
  · intro h
    rcases h with hab|hac
    · obtain ⟨ha,hb⟩ := hab
      constructor
      · exact ha
      · left
        exact hb
    · obtain ⟨ha,hc⟩ := hac
      constructor
      · exact ha
      · right
        exact hc

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
  ext f
  simp only [Set.mem_iUnion,Set.mem_inter_iff]
  constructor
  · intro g
    obtain ⟨gs,⟨i,gi⟩⟩ := g
    use i
  · intro h
    obtain ⟨i,⟨hAi,hs⟩⟩ := h
    constructor
    · exact hs
    · use i

example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext f
  simp only [Set.mem_iInter,Set.mem_inter_iff]
  constructor
  · intro g
    constructor
    · intro i
      have gab := g i
      obtain ⟨ga,gb⟩ := gab
      exact ga
    · intro i
      have gab := g i
      obtain ⟨ga,gb⟩ := gab
      exact gb
  · intro h
    obtain ⟨hA,hB⟩ := h
    intro hi
    constructor
    · have hiA := hA hi
      exact hiA
    · have hiB := hB hi
      exact hiB

example {α I : Type} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

end indexed_operations

section functions_basics

/- The `Empty` type is a type with no elements.
That means if I have `x : Empty`, then `cases x` will close every goal!
Let's prove that every function out of `Empty` is injective. -/
example (X : Type) (f : Empty → X) : Function.Injective f := by
  unfold Function.Injective
  intro g
  cases g

/- The `Unit` type is a type with one element.
That means if `x : Unit`, then `x = Unit.unit`.
We obtain that via `cases x`.
Let's use that to prove that every function out of `Unit` is injective. -/
example (X : Type) (f : Unit → X) : Function.Injective f := by
  unfold Function.Injective
  intro g h i
  cases g
  cases h
  rfl

-- Recall that if a type `X` is inhabited, then there is a default element `default : X`.
example (X : Type) [Inhabited X] (f : X → Unit) : Function.Surjective f := by
  unfold Function.Surjective
  intro g
  use default

example (X Y : Type) (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := by
  ext g
  unfold Set.preimage
  rfl

example {X Y : Type} {f : X → Y} (A : Set X) (h : Function.Injective f) : f ⁻¹' (f '' A) ⊆ A := by
  intro g i
  unfold Set.preimage Set.image at i
  obtain ⟨j,k,l⟩ := i
  have m := h l
  rw[← m]
  exact k

example {X Y : Type} {f : X → Y} (B : Set Y) : f '' (f ⁻¹' B) ⊆ B := by
  intro g h
  unfold Set.preimage Set.image at h
  obtain ⟨i,j,k⟩ := h
  rw[← k]
  exact j

example {X Y : Type} {f : X → Y} (B : Set Y) (h : Function.Surjective f) : B ⊆ f '' (f ⁻¹' B) := by
  intro g i
  unfold Set.preimage Set.image
  have x := h g
  obtain ⟨j,k⟩ := x
  use j
  constructor
  · simp only [Set.mem_setOf_eq]
    rw[k]
    exact i
  · exact k

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
