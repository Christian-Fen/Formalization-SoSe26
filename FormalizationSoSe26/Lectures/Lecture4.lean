import Mathlib.Tactic


section review

/-
Last time we saw a long list of tactics.

1. `rfl` - to close goals that are literally equal.
2. `rw` - to rewrite terms along equalities.
3. `intro` - to introduce assumptions.
4. `exact` - to provide exact matches for goals.
5. `apply` - to apply functions to goals.
6. `have` - to introduce new assumptions.
7. `constructor` - to prove equivalences and conjunctions.
8. `obtain` - to split assumptions in conjunctions and existential quantifiers.
9. `left` - to prove disjunctions.
10. `right` - to prove disjunctions.
11. `rcases` - to split disjunctions.
12. `use` - to provide witnesses for existential quantifiers.
13. `revert` - to revert assumptions back to the goal.
14. `specialize` - to specialize a function to a particular input.
15. `calc` - to do calculations step by step.
16. `ring` - to simplify computational expressions in rings.
17. `linarith` - to solve linear inequalities and contradictions.
18. `decide` - to solve decidable propositions.
19. `tauto` - to solve tautologies.
20. `norm_num` - to solve numerical equations.
21. `simp` - to simplify expressions.
22. `simp only` - to simplify expressions with specific rules.
23. `refine` - to break down goals into smaller steps.
24. `unfold` - to unfold definitions.
25. `exfalso` - to finish a proof by showing a contradiction.
26. `by_contra` - to prove a goal by contradiction.
27. `contradiction` - to finish a proof by showing a contradiction.
28. `by_cases` - to do case analysis on a proposition.
29. `#loogle` - to search for lemmas and theorems in the library.
30. `#check` - to check the type of an expression.
31. `unfold` - to unfold definitions.
32. `simp?` - to see what `simp` would do without actually simplifying.
33. `apply?` - to see what `apply` would do without actually applying.
34. `exact?` - to see what `exact` would do without actually providing an exact match.
-/

end review

section set_theory_basics
/-
We want to able to talk about sets, subsets, unions, intersection, etc. in Lean.
Herein lies a major problem!
In set theory we often write the following:
If `x ∈ A` and `A ⊆ B`, then `x ∈ B`. In Lean that *unacceptable*! Every term has a *unique* type.
Hence, to define subsets of a type `X`, we need additional data.
-/
variable (X : Type)

-- `Set X` denotes the type of subsets of the type `X`
#check (Set X)

variable (A B C : Set X)

-- Notice `Set X` is just notation for `X → Prop`
-- This means `A : Set X` just means `A : X → Prop`
variable (x : X)
#check A x

-- Similarly we can write `x ∈ A`, which is notation for `A x`
#check x ∈ A

-- Let's see some examples of subsets.
#check (∅ : Set X) -- The empty subset of `X`
#check (Set.univ X) -- `X` as a subset of itself

-- We can define standard set theoretical operations:
#check A ∩ B -- written as `\cap` or `\inter`
#check A ∪ B -- written as `\cup` or `\union`
#check A \ B -- written as `\` or `\setminus`
#check A ⊆ B -- written as `\subseteq` or `\subset`
#check A ∩ B ⊆ C

-- For a given formula `P` on `X`, we can use the usual set builder notation.

variable (P : X → Prop)
#check { x : X | P x } -- set of all `x` such that `P x` is true
#check { n : ℕ | n < 10 } -- set of all `n` such that `n < 10`
#check { x : X | x = x }

set_option linter.unusedVariables false

-- All of this is notation, and Lean thinks of these as equal:
example : A = { x : X | x ∈ A } := by rfl
example : A ∩ B = { x : X | x ∈ A ∧ x ∈ B } := by rfl
example : A ∪ B = { x : X | x ∈ A ∨ x ∈ B } := by rfl
example : ∅ = { x : X | False } := by rfl
example : Set.univ = { x : X | True} := by rfl

set_option linter.unusedVariables true

-- We prove facts about sets, using the same tactics we have seen before.
example (h : A ⊆ C) : A ∩ B ⊆ C ∩ B := by
  intro x hx
  obtain ⟨ha , hb⟩ := hx
  constructor
  · exact h ha
  · exact hb

-- We can also take *indexed* operations.

variable (I : Type) (A : I → Set X)

#check Set.iUnion
#print Set.iUnion
#check Set.iUnion A
#check (⋃ i, A i) -- written as `\bigcup`

#check Set.iInter
#print Set.iInter
#check Set.iInter A
#check (⋂ i, A i) -- written as `\bigcap`

-- There are various useful ways to deal with indexed unions and intersections.
#check Set.mem_iUnion
#check Set.mem_iInter

example {α I : Type} (A B : I → Set α) : ⋃ i, (A i ∩ B i) ⊆ (⋃ i, A i) ∩ (⋃ i, B i) := by
  intro x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  intro h
  obtain ⟨i, hAB⟩ := h
  obtain ⟨hA, hB⟩ := hAB
  -- Alternatively we can do both `obtain` in one step:
  -- obtain ⟨i, ⟨hA,hB⟩⟩ := h
  -- Alternatively, we can use `rcases`
  -- rcases h with ⟨i, ⟨hA,hB⟩⟩
  constructor
  · use i
  · use i

end set_theory_basics


section extensionality
/-
Extensionality is the principle that two sets are equal if they have the same elements.
This fact is built into the foundation in Lean and comes with a tactic `ext`.
-/

example (X : Type) (A B : Set X) (hab : A ⊆ B) : A ∩ B = A := by
  ext a
  constructor
  · intro hb
    obtain ⟨ha, _⟩ := hb
    -- Here, we did not name `a ∈ B` because we do not need it.
    exact ha
  · intro ha
    constructor
    · exact ha
    · exact hab ha

-- We can in particular use `ext` to prove that nothing is equal to itself.
example (X : Type) : ∅ = { x : X | x ≠ x } := by
 ext a
 constructor
 · intro h
   exfalso
   exact h
 · intro h
   exfalso
   apply h
   rfl

-- Note in this last step `contradiction` would have also worked to close things.
example (X : Type) : ∅ = { x : X | x ≠ x } := by
 ext a
 constructor
 · intro h
   exfalso
   exact h
 · intro h
   exfalso
   contradiction

-- Here all of the effort focuses on showing that `x ≠ x` always holds!
-- This can be simplified using `simp`:
example (X : Type) : ∅ = { x : X | x ≠ x } := by
  simp

end extensionality

section functions_definitions
-- We have already seen functions in Lean.
variable (X Y : Type) (f : X → Y) (A : Set X) (B : Set Y)
#check X → Y
#check f

-- Now, for a given function `f : X → Y` we can define the preimage.
-- It consists of elements in `X` that map to `B` via `f`.
#check Set.preimage f
#check Set.preimage f B

-- The preimage admits alternative notation, more common in set theory:
#check f ⁻¹' B  -- here we use `\preim` to get the desired notation.

-- For a function `f : X → Y` we can also define the image.
-- It consists of elements in `Y` that are images of elements in `A` via `f`.
#check Set.image f
#check Set.image f A
#check f '' A -- here we use `''` to get the desired notation.

example : A ⊆ f ⁻¹' (f '' A) := by
  intro x xs
  use x, xs

-- Let us see some tactics that can help us unwind things.
example : A ⊆ f ⁻¹' (f '' A) := by
  intro x xs
  simp only [Set.mem_preimage, Set.mem_image] -- `simp` shows us what we really need to do.
  use x, xs

example : A ⊆ f ⁻¹' (f '' A) := by
  intro x xs
  unfold Set.preimage Set.image
  use x, xs

-- Let's see how we can prove things about them.
example : A ⊆ f ⁻¹' (f '' A) := by
  intro x xs
  change f x ∈ f '' A -- The `change` tactic simplifies goals along statements we enter.
  use x, xs

-- Functions have many properties.
-- First of all there are the usual injective, surjective and bijective functions.

-- A function `f : X → Y` is injective if `f x₁ = f x₂` implies `x₁ = x₂`.
#check Function.Injective
#print Function.Injective

-- A function `f : X → Y` is surjective if for every `y : Y`,
-- there exists an `x : X` such that `f x = y`.
#check Function.Surjective
#print Function.Surjective

-- A function `f : X → Y` is bijective if it is both injective and surjective.
#check Function.Bijective
#print Function.Bijective

-- We can define, injective, surjective and bijective functions on a particular set.
#check Set.InjOn
#print Set.InjOn

#check Set.SurjOn
#print Set.SurjOn

#check Set.BijOn
#print Set.BijOn


-- Let's compare these definitions.
#check Set.mem_univ

example : Set.InjOn f Set.univ = Function.Injective f := by
  -- Here are I want to prove two propositions are equal.
  -- I can still use `ext` to reduce that to an `iff`.
  ext
  constructor
  · intro inj x y hi
    exact inj (Set.mem_univ x) (Set.mem_univ y) hi
  · intro inj x xs y ys hi
    exact inj hi

-- This proof seems too long. We are really just using that everything is in `Set.univ`.
example : Set.InjOn f Set.univ = Function.Injective f := by
  unfold Function.Injective Set.InjOn
  simp only [Set.mem_univ, forall_const]
  -- simp only [Set.injOn_univ]

-- Note, this proof is one example, where `unfold` is not redundant and *cannot* be removed.

end functions_definitions

noncomputable section axiom_of_choice
/-
Let's try some more advanced set theory. Unfortunately, this will require the axiom of choice,
which is not `computable` in Lean. Hence, we will use the `noncomputable` section.
-/

-- For a given type `α`, we can abstractly state that it is non-empty.
variable {α : Type} [Inhabited α]

-- If it is inhabited, it has an element called `default`.
#check (default : α)

/-
The axiom of choice states that if there is an existential statement `∃ x, P x`,
for a proposition `P`, then we can *choose* an element `x` such that `P x` holds.
-/
variable (P : α → Prop) (h : ∃ x, P x)

-- For a given h, there is a choice function `Classical.choose` that gives us a witness.
#check Classical.choose h
#check Classical.choose_spec

example (Q : α → Prop) (hh : ∃ x, Q x) :  Q (Classical.choose hh) :=
  Classical.choose_spec _

/-
We now want a proof for the following statement:
If `f : X → Y` is a surjective function, then `f` has a right inverse.
So `g : Y → X` such that `f ∘ g = id`.
-/
def right_inverse {X Y : Type} (f : X → Y) (fsurj : ∀ y, ∃ x, f x = y) : Y → X :=
  fun y : Y ↦ Classical.choose (fsurj y)

lemma right_inverse_spec {X Y : Type} (f : X → Y) (fsurj : ∀ y, ∃ x, f x = y) (y : Y) :
  f (right_inverse f fsurj y) = y := Classical.choose_spec (fsurj y)
-- Note, I did not even use tactics here.

end axiom_of_choice

section Cantor
/-
Let's end this with one advanced theorem in set theory: Cantor's theorem.

Recall that Cantor's theorem states that there is no surjective function
from a set to its power set (the set of subsets).
-/

/- For convenience we introduce the `let` tactic, which
helps introduce new definitions in a proof. -/
theorem Cantor (X : Type) : ∀ f : X → Set X, ¬Function.Surjective f := by
  intro f surjf
  -- First we pick the set `S` in `Set X`, that cannot be in the image.
  let S := { i | i ∉ f i }
  -- This means `f j = S`
  -- obtain ⟨j, h⟩ := surjf S
  rcases surjf S with ⟨j, h⟩
  -- We now prove `j ∈ S`
  have hj : j ∈ S := by {
    intro h'
    have : j ∉ f j := by {
      rw [h] at h'
      exact h'
    }
    contradiction
  }
  -- We now prove `j ∉ S`
  have hnj : j ∉ S := by {
    rw [← h]
    exact hj
  }
  contradiction

end Cantor
