import Mathlib.Tactic

-- Let's do some basic tactics exercises.

section rw

/-
In this section, *only* use the `rw` tactic.
You will also need the following functions:
-/
#check mul_comm
#check mul_assoc

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm]
  rw [← mul_assoc]
  rw [mul_comm]
  rw [mul_comm a c]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc]
  rw [h]
  rw [h']
  rw [mul_assoc]


example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [mul_assoc a e f]

-- For this next exercise, you can also use:
#check sub_self

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm a b]
  rw [sub_self]

end rw

section logic

/-
For the following exercises, *only* use the tactics:
- `intro`
- `exact`
- `constructor`
- `left`
- `right`
- `apply`
- `obtain`
- `rcases`
- `rw`
-/

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro jPQ
  obtain ⟨jP,jQ⟩ := jPQ
  constructor
  · apply h
    exact jP
  · apply h'
    exact jQ

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro jPQ
  obtain ⟨jP,jQ⟩ := jPQ
  have jR : R := h jP
  have jS : S := h' jQ
  constructor
  · exact jR
  · exact jS

example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  obtain ⟨x,hPQ⟩ := h
  use x
  obtain ⟨hP,hQ⟩ := hPQ
  constructor
  · exact hQ
  · exact hP

example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  obtain ⟨x,⟨hP,hQ⟩⟩ := h
  use x

-- For the next exercise you also need the function
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀ h₁

-- For the next exercise, you can also use `ring`.
-- You will also need the following:
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h
    rw[h]
    rw[sub_self]
  · intro j
    rw[← add_zero a]
    rw[← j]
    ring

example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
 constructor
 · intro fPQR
   obtain ⟨fP,fQR⟩ := fPQR
   rcases fQR with fQ | fR
   · left
     constructor
     · exact fP
     · exact fQ
   · right
     constructor
     · exact fP
     · exact fR
 · intro gPQPR
   rcases gPQPR with gPQ | gPR
   · obtain ⟨gP,gQ⟩ := gPQ
     constructor
     · exact gP
     · left
       exact gQ
   · obtain ⟨gP,gR⟩ := gPR
     constructor
     · exact gP
     · right
       exact gR


example (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 constructor
 · intro f
   constructor
   · intro x
     have hPQ := f x
     obtain ⟨hP,hQ⟩ := hPQ
     exact hQ
   · intro x
     have hPQ := f x
     obtain ⟨hP,hQ⟩ := hPQ
     exact hP
 · intro f
   obtain ⟨fQ,fP⟩ := f
   intro x
   have hQ := fQ x
   have hP := fP x
   constructor
   · exact hP
   · exact hQ





end logic
