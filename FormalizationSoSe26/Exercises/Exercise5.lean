import Mathlib.Tactic
import FormalizationSoSe26.Lectures.Lecture5

section finite_sets

open Finset Fintype
/-
For this exercise recall the following properties of `Finset`:
-/
#check mem_inter
#check mem_union
example (X : Type*) [DecidableEq X] (A B C : Finset X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext f
  simp only [mem_inter, mem_union]
  tauto

/-
This next one should be very straightforward, so don't overthink it!
-/
example (X Y : Type*) [Fintype X] [Fintype Y] :
  card (Fin 2 → (X ⊕ Y)) = (card X)^2 + 2*(card X) * (card Y) + (card Y)^2 := by
  simp only [Fintype.card_pi, card_sum, prod_const, card_univ, Fintype.card_fin]
  ring

/-
Recall from the lecture how we can prove the following two properties:
-/
example {X Y : Type*} [DecidableEq X] [DecidableEq Y] (A B : Finset X) :
  #(A ∪ B) = #A  + #B  -  #(A ∩ B)  := by
  simp only [card_union]

example {X Y : Type*} [DecidableEq X] [DecidableEq Y] (A : Finset X) (C : Finset Y) :
  #(A ×ˢ C) = #A * #C := by
  simp only [card_product]

/-
Now, use the experience you gained to solve the following exercise.
You might also want to use the following properties of `Nat`:
-/

#check Nat.sub_mul
#check Nat.mul_sub
#check Nat.add_mul
#check Nat.mul_add

example {X Y : Type*} [DecidableEq X] [DecidableEq Y] (A B : Finset X) (C : Finset Y) :
  #((A ∪ B) ×ˢ C) = #A * #C + #B * #C -  #(A ∩ B) * #C := by
  simp only [card_product,card_union]
  ring_nf
  simp only[Nat.sub_mul,Nat.add_mul]
  ring

end finite_sets

section induction

/-
Here is our new definition of natural numbers.
-/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-
This `namespace` is necessary so we can use `add`, `mul`, ...
without resulting in any conflicts.
-/
namespace MyNat

/-
Inductively complete the following definitions of
`add` and `mul` for `MyNat`.
Your definition should be motivated by what
addition and multiplication of natural numbers should be.
-/
def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

/-
Uncomment the following if you have defined `add`.
-/
#eval add (succ zero) (succ zero)
/-
It should give us `MyNat.succ (MyNat.succ (MyNat.zero))`
-/

def mul : MyNat → MyNat → MyNat
  | _ , zero => zero
  | x, succ y => add (mul x y) x

/-
Uncomment the following if you have defined `mul`.
-/
#eval mul (succ (succ zero)) (succ (succ zero))
/-
It should give us `MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero))))`
-/

/-
Now, use the inductive definition to prove the following theorems.
-/
theorem zero_add (n : MyNat) : add zero n = n := by
  induction n with
  | zero => rfl
  | succ n nh =>
    rw[add]
    rw[nh]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction n with
  | zero => rfl
  | succ n nh =>
    rw[add,nh,add]
  --  rw[nh]
  --  rw[add]

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction n with
  | zero =>
    rw[zero_add,add]
  | succ n nh =>
    rw[add,nh,succ_add]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by sorry

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by sorry

theorem zero_mul (n : MyNat) : mul zero n = zero := by sorry

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by sorry

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by sorry

end MyNat

end induction

section irrationals
/-
Complete the following proof steps, to show that the square root of `2` is not rational.
-/
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have m_is_even : 2 ∣ m := by
    have f: 2 ∣ m ^ 2 := by use n ^ 2
    exact even_of_even_sqr₄ f
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp m_is_even
  have step₁ : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have step₂ : 2 * k ^ 2 = n ^ 2 := by
    calc
    2 * k ^ 2   = 2 * (2 * k ^ 2) / 2 := by norm_num
    _           = 2 * n ^ 2 / 2 := by rw[step₁]
    _            = n ^ 2 := by norm_num
  have n_is_even : 2 ∣ n := by
    have g: 2 ∣ n ^ 2 := by
      use k ^ 2
      exact step₂.symm
    exact even_of_even_sqr₄ g
  have : 2 ∣ m.gcd n := by
    exact Nat.dvd_gcd m_is_even n_is_even
  have weird : 2 ∣ 1 := by
    rw[coprime_mn] at this
    exact this
  norm_num at weird

/-
If you solve the case for `2` above, you can generalize it to any prime.
You should be able to use a similar approach, however might need the following
additional facts:
-/
#check Nat.Prime.dvd_of_dvd_pow
variable {q : ℕ} (prime_q : q.Prime)
#check prime_q.ne_zero
#check prime_q.ne_one
/-
You might also benefit from the tactic `field_simp` which
can prove `a * b / a = b` with the assumption `a ≠ 0`.
-/

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  sorry

/-
For the next two exercises, you want to use the various facts we established
about the `.factorization` list, we saw in the lecture.
-/

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    sorry
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    sorry
  have eq3 : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at eq3
  norm_num at eq3

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (eq_zero_of_pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 :
    ((r + 1) * n ^ k).factorization p = k * n.factorization p + (r + 1).factorization p := by
    sorry
  have eq3 : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [eq3]
  sorry

end irrationals

section infinite_primes
/-
Prove there are infinitely many primes by completing the proof steps.
Here are some things that can help:
-/
#check Nat.dvd_factorial
#check Nat.dvd_sub
/-
Also, if `pp` is a proof that `p` is prime, then `pp.pos` is a proof that `p > 0`.
-/
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  -- First we show that `Nat.factorial n + 1` is greater than `2`.
  have greater_than_two : 2 ≤ Nat.factorial n + 1 := by
    sorry
  -- We now pick a prime factor `p` of `Nat.factorial n + 1`.
  rcases exists_prime_factor greater_than_two with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  -- Finally, we show that `p` is greater than `n`.
  show p > n
  by_contra ple
  push Not at ple
  have p_divides : p ∣ Nat.factorial n := by
    sorry
  -- We finish with a contradiction.
  have weird : p ∣ 1 := by
    sorry
  change False
  sorry

end infinite_primes
