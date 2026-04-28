import Mathlib.Tactic

section min

variable (a b c d : ℝ)

-- We have a min function in Lean:
#check min
-- It has various properties:
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- You will also need the following facts about inequalities:
#check le_antisymm
#check le_trans

-- Now use those to prove the following.
-- Only use `apply`.
example : min a b = min b a := by
  sorry

-- Now redo the exercise with `simp`.
example : min a b = min b a := by
  sorry

-- Now solve the following only with `apply` and nothing else!
example : min a (min b c) = min (min a b) c := by
  sorry

-- Again try again with `simp`.
example : min a (min b c) = min (min a b) c := by
  sorry

-- If you are very daring, you can also try the following one with `apply` only.
example : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  sorry

-- If you are not daring, you can also try the following one with `simp`.
example : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  sorry

end min

section calculation
open Real Nat

-- Let's us use `calc` to do some calculations.

-- `exp` is the exponential function.
#check exp

-- Of course we know some properties of `exp`:
#check exp_add

-- For this example we also need:
#check pow_two
-- Maybe also `ring` or `ring_nf` to do some algebraic manipulations.

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by sorry
              _ = exp ((b + b) + (c + c))           := by sorry
              _ = exp (b + b) * exp (c + c)         := by sorry
              _ = (exp b * exp b) * (exp c * exp c) := by sorry
              _ = (exp b) ^ 2 * (exp c)^2           := by sorry

-- Use `calc` to prove the following from the axioms of rings, without using `ring`.
-- You can however use
#check add_neg_cancel_comm
#check add_assoc

example {a b c : ℝ} (h : a + b = a + c) : b = c := by sorry

/-
`(n)!` denotes the factorial function on the natural numbers.
Here the parentheses are mandatory when writing.
Use `calc` to solve this question.
For the different steps use `exact?` to find the lemmas you need in the library.
 -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by sorry

end calculation

section evenfunction

def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

#check EvenFunction

-- For this next exercise you want to use `calc`.
example (f g : ℝ → ℝ) (hf : EvenFunction f) : EvenFunction (f + g) ↔ EvenFunction g := by
  sorry

end evenfunction

section contradiction
/- In this section we also use `by_contra`. -/

-- This first one should not require `by_contra`.
example (P : Prop) (h : P) : ¬¬P := by
  sorry

example (P : Prop) (h : ¬¬P) : P := by
  sorry

example (P : Prop) : (P → ¬P) → ¬P := by
  sorry

-- Let's prove the famous De Morgan's laws.
-- Note these two are harder than the three previous ones.
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

-- These ones are also not easy, but worth a shot.
example {α : Type*} (P : α → Prop) : (∃ x, P x) ↔ (¬ ∀ x, ¬ P x) := by
  sorry

example {α : Type*} (P : α → Prop) : (∀ x, P x) ↔ (¬ ∃ x, ¬ P x) := by
  sorry

end contradiction
