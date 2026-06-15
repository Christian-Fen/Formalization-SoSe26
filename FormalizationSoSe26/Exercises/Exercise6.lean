import Mathlib.Tactic
import FormalizationSoSe26.Lectures.Lecture6

section triple_constructors

-- Recall the integers are defined as `\bZ`.
#check ℤ

/-
Use `structure` to construct a new constructor:
* It is called `new_triple`
* The data should be three integers `x` `y` `z` in `ℤ`
* It should satisfy `extensionality`
-/
@[ext]
structure new_triple where
   x : Int
   y : Int
   z : Int
/-
Now, solve the following exercises about `new_triple`:

1. Create three instances of `new_triple` using three different approaches:
   * With `.mk`
   * With `⟨⟩`
   * With `where`
   using the numbers `x = 1`, `y = 2`, `z = -3`.
-/

example : new_triple := new_triple.mk 1 2 3

example : new_triple := ⟨1, 2, 3⟩

example : new_triple where
   x := 1
   y := 2
   z := 3

/-
2. Uncomment the following expression and prove it.
-/


example (x₁ y₁ z₁ x₂ y₂ z₂ : ℤ) :
   (x₁ = x₂) ∧ (y₁ = y₂) ∧ (z₁ = z₂) ↔ (⟨x₁, y₁, z₁⟩ :
   new_triple )= (⟨x₂, y₂, z₂⟩ : new_triple) := by
   constructor
   · intro f
     obtain ⟨fx,fy,fz⟩ := f
     rw[fx,fy,fz]
   · intro f
     cases f
     constructor
     · rfl
     · constructor
       · rfl
       · rfl


/-
3. Define a namespace `new_triple` and define the following functions:
    * `add` that adds two `new_triple` objects.
    * `mul` that multiplies two `new_triple` objects.
    * `sub` that subtracts two `new_triple` objects.
  Close the namespace `new_triple`.
-/

namespace new_triple

def add (a b : new_triple) : new_triple :=
   ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def mul (a b : new_triple) : new_triple :=
   ⟨a.x * b.x, a.y * b.y, a.z * b.z⟩

def sub (a b : new_triple) : new_triple :=
   ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

end new_triple

/-
4. Use `#eval` to compute
    * addition of `⟨1, 2, -3⟩` and `⟨2, -5, 6⟩)`
    * multiplication of `(⟨2, -3, 2⟩` and `⟨1, -2, 2⟩`
    * subtraction of `⟨-1, 2, -3⟩` and `⟨4, 1, 3⟩)`
   For this you want to use `#eval` to evaluate an expression.
-/

#eval new_triple.add ⟨1, 2, -3⟩ ⟨2, -5, 6⟩
#eval new_triple.mul ⟨2, -3, 2⟩ ⟨1, -2, 2⟩
#eval new_triple.sub ⟨1, 2, -3⟩ ⟨4, 1, 3⟩

/-
5. Reopen the namespace `new_triple` and prove:
   * `mul` is commutative by defining and proving `mul_comm`.
   * `mul` is associative by defining and proving `mul_assoc`.
   Close the namespace `new_triple`.
-/

namespace new_triple

def mul_comm (a b : new_triple) : mul a b = mul b a := by
   ext
   · simp only [mul, Int.mul_comm]
   · simp only [mul, Int.mul_comm]
   · simp only [new_triple.mul, Int.mul_comm]

def mul_assoc (a b c : new_triple) : mul (mul a b) c = mul a (mul b c) := by
   ext
   · simp only [mul, Int.mul_assoc]
   · simp only [mul, Int.mul_assoc]
   · simp only [mul, Int.mul_assoc]

end new_triple

/-
6. Use `#check` to compare the definition of `new_triple.mul_comm` and `mul_comm`.
-/

#check new_triple.mul_comm
#check mul_comm

end triple_constructors

section group_five
/-
In the `Lecture6.lean` we defined `Group₄` as a particular group structure.
-/
#check Group₄

-- Here is a different group structure.
class Group₅ (G : Type*) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

export Group₅ (inv_dia)

/-
We want to see that although `Group₅` seems weaker than `Group₄`, we can actually
recover the original definition.
-/


/-
Let's start with the easy case.
Show that every `Group₄` gives us a `Group₅`.
Here you probably want to use `Group₅.mk`.
-/
@[reducible]
def group4_to_group5 {G : Type*} [Group₄ G] : Group₅ G :=
   Group₅.mk inv_dia

/-
Now, we also go the other way around.
This requires some lemmas.

These two lemmas should be provable using only:
- `rw`
- `exact`
- `have`
and the structure of `Monoid₁` and `Group₅`.
-/
lemma equal_inverses {M : Type*} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) :
   b = c := by
      rw [← dia_one b]
      rw [← hac]
      rw [← dia_assoc]
      rw [hba]
      rw [one_dia]


lemma dia_inv' {G : Type*} [Group₅ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have first := inv_dia (a⁻¹)
  have second := equal_inverses (first) (inv_dia a)
  rw[second] at first
  exact first

/-
Now, use this last lemma to go from `Group₅` to `Group₄`.
Here you probably want to use `Group₄.mk`.
-/
@[reducible]
def group5_to_group4 {G : Type*} [Group₅ G] : Group₄ G :=
   Group₄.mk inv_dia dia_inv'

/-
Let us end this by observing that the two constructions are inverse to each other.
-/
lemma group4_to_group5_to_group4 {G : Type*} [h : Group₄ G] :
   @group5_to_group4 G (@group4_to_group5 G h) = h  := by
      rfl

lemma group5_to_group4_to_group5 {G : Type*} [h : Group₅ G] :
   @group4_to_group5 G (@group5_to_group4 G h) = h  := by
      rfl

end group_five

section ordered_monoid
/-
Let us now try to make new structures.
We go step by step.

First we define a new structure `LE₁` that defines a relation on a type `α`.
-/

class LE₁ (α : Type*) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

/-
Your job is now to slowly define and extend from here:

Recall a preorder is a relation on a type that is reflexive and transitive.
- Reflexivity means that for all `a`, `a ≤ a`.
- Transitivity means that for all `a`, `b`, `c`, if `a ≤ b` and `b ≤ c` then `a ≤ c`.

Define a class called `Preorder₁` that extends `LE₁` with these two properties.
They should be named and have the following docstrings:
- `refl` should have the docstring "The reflexivity property."
- `trans` should have the docstring "The transitivity property."
-/

class Preorder₁ (α : Type*) extends LE₁ α where
   /-- The reflexivity property. -/
   refl : ∀ a : α, a ≤₁ a
   /-- he transitivity property. -/
   trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c

/-
A partial order is a preorder with the additional property of antisymmetry.
- Antisymmetry means that for all `a`, `b`, if `a ≤ b` and `b ≤ a` then `a = b`.

Define a class called `PartialOrder₁` that extends `Preorder₁` with this property.
It should be named `antisymm` and have the docstring "The antisymmetry property.".
-/

class PartialOrder₁ (α : Type*) extends Preorder₁ α where
   /-- The antisymmetry property. -/
   antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b

/-
We now bring in some algebraic structure.
We have already defined `Monoid₁` in the lecture.
-/

#check Monoid₁

/-
A commutative monoid is a monoid with the additional property of commutativity.
- Commutativity means that for all `a`, `b`, `a ⋄ b = b ⋄ a`.

Define a class called `CommMonoid₁` that extends `Monoid₁` with this property.
It should be named `dia_comm` and have the docstring "Diamond is commutative."
-/

class CommMonoid₁ (α : Type*) extends Monoid₁ α where
   /-- Diamond is commutative. -/
   dia_comm : ∀ a b : α, a ⋄ b = b ⋄ a

/-
We now combine the two structures into one.
An ordered commutative monoid is a structure that is a
commutative monoid and also a partial order, with the following property:
- For all `a`, `b`, `c`, if `a ≤ b` then `a ⋄ c ≤ b ⋄ c`.
This means that the multiplication is compatible with the order.

Define a class called `OrderedCommMonoid₁` that extends `PartialOrder₁` and `CommMonoid₁`
 with this property. It should be named `le_mul_left₁` and have the docstring
"The multiplication is compatible with the order."
-/

class OrderedCommMonoid₁ (α : Type*) extends PartialOrder₁ α, CommMonoid₁ α where
   /-- The multiplication is compatible with the order. -/
   le_mul_left₁ : ∀ a b c : α, a ≤₁ b → a ⋄ c ≤₁ b ⋄ c

/-
The class `OrderedCommMonoid₁` has many new properties.
`export` all of them.
-/

export OrderedCommMonoid₁ (le_mul_left₁)
export CommMonoid₁ (dia_comm)
export PartialOrder₁ (antisymm)
export Preorder₁ (trans refl)

/-
Now we want to prove something about ordered commutative monoids.

Write a lemma called `le_mul_right₁` that states
- for all `a`, `b`, `c`, if `a ≤₁ b` then `c ⋄ a ≤₁ c ⋄ b`.

Here:
- There should be an implicit type `α` in `Type*`.
- `OrderedCommMonoid₁` should be a typeclass.
- `a`, `b`, `c` should be of type `α` and also implicit.
- There should only be an explicit hypothesis named `h` that `a ≤₁ b`.

Now prove it!
Again, this should be provable using only `rw`, `apply` and `exact`,
and the properties of `OrderedCommMonoid₁`.
-/

lemma le_mul_right₁ {α : Type*} [OrderedCommMonoid₁ α] {a b c : α} (h : a ≤₁ b) :
    c ⋄ a ≤₁ c ⋄ b := by
    rw [dia_comm c a, dia_comm c b]
    apply le_mul_left₁
    exact h

/-
Finally, let us get an instance of a `OrderedCommMonoid₁`.
We will use the natural numbers.

Here we call some basic facts about inequalities for natural numbers.
-/
#check 0
#check 2 ≤ 3
#check le_refl
#check le_trans
#check le_antisymm
#check Nat.add
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.add_zero
#check Nat.zero_add
#check Nat.add_le_add_right

/-
We now have the following structure of `OrderedCommMonoid₁`.

Uncomment the next line if you have solved the previous exercises.-/
-- #print OrderedCommMonoid₁

/-
Define an `instance` in `OrderedCommMonoid₁ ℕ`.
Use the properties given above.
-/

instance : OrderedCommMonoid₁ ℕ where
   le := fun a b => a ≤ b
   refl := le_refl
   trans := fun _ _ _ hab hbc => le_trans hab hbc
   antisymm := fun _ _  hab hba => le_antisymm hab hba
   dia := Nat.add
   dia_assoc := Nat.add_assoc
   one := 0
   one_dia := Nat.zero_add
   dia_one := Nat.add_zero
   dia_comm := Nat.add_comm
   le_mul_left₁ := fun _ _ c h => Nat.add_le_add_right h c

end ordered_monoid
