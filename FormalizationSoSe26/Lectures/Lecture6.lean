import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.HasLimits


section overview


/-
Last time we did some combinatorics and number theory.
-/
#check Finset
#check Fintype
#check Nat.card
#check gcd
#check Nat.Coprime
#check Nat.primeFactorsList
/-
Today we cover some advanced topics in Lean:
1. The `rintro` tactic.
2. `namespaces`.
3. `universes`.
4. `mathlib`
5. `structures`.
6. `classes`
7. `instances`

Next lecture we will then also discuss `morphisms`.
-/
end overview

section rintro
/-
We have seen the `intro` tactic, which introduces a hypothesis.
We can use `obtain` more efficiently.
We can also use `rintro`, which is a more powerful version of `intro`.
-/

-- Let's see an example that should be familiar.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  · intro hpqr
    · obtain ⟨hpq, hr⟩ := hpqr
      rcases hpq with hp | hq
      · simp [hp, hr]
      · simp [hq, hr]
  · intro hpqr
    · obtain hpr | hqr := hpqr
      · obtain ⟨hp, hr⟩ := hpr
        simp [hp, hr]
      · obtain ⟨hq, hr⟩ := hqr
        simp [hq, hr]

example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  · intro hpqr
    · obtain ⟨hpq, hr⟩ := hpqr
      -- We can phrase everything with `obtain`
      obtain hp | hq := hpq
      · simp [hp, hr]
      · simp [hq, hr]
  · intro hpqr
    · obtain hpr | hqr := hpqr
      · obtain ⟨hp, hr⟩ := hpr
        simp [hp, hr]
      · obtain ⟨hq, hr⟩ := hqr
        simp [hq, hr]

example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  · intro hpqr
    -- We can combine the `obtain`
    obtain ⟨ hp | hq , hr⟩ := hpqr
    · simp [hp, hr]
    · simp [hq, hr]
  · intro hpqr
    -- We can combine the `obtain`
    obtain ⟨hp, hr⟩ | ⟨hq, hr⟩ := hpqr
    · simp [hp, hr]
    · simp [hq, hr]

-- We can also use `rcases` instead of `obtain`.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  · intro hpqr
    -- We can combine the `rcases`
    rcases hpqr with ⟨ hp | hq , hr⟩
    · simp [hp, hr]
    · simp [hq, hr]
  · intro hpqr
    -- We can combine the `rcases`
    rcases hpqr with ⟨hp, hr⟩ | ⟨hq, hr⟩
    · simp [hp, hr]
    · simp [hq, hr]

-- We now introduce `rintro`!
-- It combines `intro` and `obtain` or `rcases`.
example (P Q R : Prop) : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) := by
  constructor
  · rintro ⟨ hp | hq , hr⟩
    · simp [hp, hr]
    · simp [hq, hr]
  · rintro (⟨hp, hr⟩ | ⟨hq, hr⟩)
    · simp [hp, hr]
    · simp [hq, hr]

end rintro

section namespaces
/-
We saw we can use more advanced definitions and results with `dot` notation.

So, `Injective` is a property of functions, and hence needs a `Function.` before.
-/
#check Set.InjOn
#check Function.Injective

/-
We saw a similar issue in number theory.
-/
#check Nat.primeFactorsList

/- In the long run this is very inconvenient. What we want is more efficient code!
For that we use `namespace`-/

open Function
-- This opens the `namespace` for `Function`.
#check Injective

open Set
-- This opens the `namespace` for `Set`.
#check InjOn

open Nat
-- This opens the `namespace` for `Nat`.
#check primeFactorsList

-- Namespaces *automatically* stay open in the section and
-- close with the closing of the section!
end namespaces

-- These result in errors, because the namespaces are closed.
-- #check Injective
-- #check InjOn
-- #check primeFactorsList

section manynamespaces
-- One can open multiple namespaces at once.
open Function Set Nat

#check Injective
#check univ
#check InjOn
#check primeFactorsList

end manynamespaces

section testuniverses
/-
To avoid set theoretical paradoxes, Lean has a hierarchy of universes.
By default, the lowest one is `Type 0` or just `Type`.
-/
example : Type 0 = Type := rfl

variable (X : Type)
variable (X' : Type 0)
#check X
#check X'
#check Type

-- There are higher universes.
variable (Y : Type 1)
#check Y
#check Type 1

variable (n : Nat)
variable (Z : Type n)
#check Z
#check Type n

/-
Lean has a `universe` command to declare universe variables.
-/
universe u v w

/-
Unlike other types, Lean has a `polymorphism` property for universes.
This means terms across different universes can be used together.
-/
#check Type u
variable (A : Type u)
variable (B : Type v)
#check  A × B

/-
We can write `Type*` to let Lean figure out the universe level.
-/
#check Type*

variable (C : Type*)
-- Here we see `C` is in universe level `u_1`.
#check C
#check C × A

/-
In most cases these universe considerations are not relevant.
But some times things are subtle.
-/

#check X
#check X'
#check Y

/-
As `X` and `X'` are in the same universe, this first one is easy.
-/
def XX' : Type := X × X'

/-
Now `X` and `Y` are in different universes, so things are trickier.
-/
def XY : Type 1 := X × Y
-- def XY' : Type := X × Y
-- def XY'' : Type* := X × Y
def XY''' : Type _ := X × Y

#check XY
#check XY'''
end testuniverses


section mathlib
/-
Let's learn a little about `MathLib`
`MathLib` is the standard mathematical library for Lean4.
It contains most of the mathematics formalized in Lean4.
Part of setting up this project involved installing `MathLib`.

A single Lean file does not contain any particular definitions.
We hence load existing definitions from `MathLib` to use them in our file.
We include them in the beginning of the file using `import`.

For example, if you notice, every file until now has the first line:
`import Mathlib.Tactic`.

This loads `tactics` and various standard definitions and theorems from `MathLib`.

Let us see some examples.
-/

#check Group
#check Ring
#check Field
#check TopologicalSpace
#check MetricSpace
#check CategoryTheory.Category
#check ULift

-- If we go more specialized, we need more imports.
-- Here is an example from limits in category theory.
#check CategoryTheory.Limits.HasLimits

/-
Working on a project will mean familiarizing yourself with certain parts of `MathLib`,
relevant to your project.
-/
end mathlib

section structures

/-
In mathematics we layer structures to study more
complicated objects and ideas:
* A group is a set with operations ...
* A ring is a set with operations ...
* A topological spaces is a set with ...
* A metric space is a set with ...
* A vector space is a set with ...

We know what a set is in Lean, a `Type`.
But what are structures?
We want to *structure* our types!
-/

-- We can define a structure in Lean using the `structure` keyword.

-- We will come back to this first line later.
@[ext]
structure new_pair where
  x : Nat
  y : Nat

#check new_pair
#check new_pair.x -- projection to first component
#check new_pair.y -- projection to second component


/-
We can create new instances via:
* `newpair.mk x y` which stands for *make*
* A tuple `⟨x , y⟩`
* `where` notation
-/


example : new_pair := new_pair.mk 1 2

-- We can also explicitly provide the input names:
example : new_pair := new_pair.mk (x := 1) (y := 2)

example : new_pair := new_pair.mk (y := 2) (x := 1)

example : new_pair := ⟨1, 2⟩

example : new_pair where
  x := 1
  y := 2

-- These three approaches results in the same object.
example : new_pair.mk 1 2 = ⟨1, 2⟩ := by rfl

-- `new_pair` satisfies extensionality.
-- For `structure` the tactic `cases` is very useful.
-- We can use `cases` to deconstructs the object.

example (x₁ y₁ x₂ y₂ : Nat) : new_pair.mk x₁ y₁ = new_pair.mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨eqx, eqy⟩
    rw [eqx, eqy]

-- By adding the `@[ext]` attribute we can use the tactic `ext` to prove equality.
example (x₁ y₁ x₂ y₂ : Nat) : new_pair.mk x₁ y₁ = new_pair.mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨eqx, eqy⟩
    ext
    · rw [eqx]
    · rw [eqy]

-- Of course when all data are just two points, this does not help too much.

-- We can now define functions on `new_pair`, the way we did before.
example : new_pair := by
  constructor
  · exact 3
  · exact 4

example : new_pair := ⟨3 ,4⟩

example (a b : new_pair) : new_pair :=
  ⟨a.x + b.x, a.y + b.y⟩

/-
Here is a problem:
We want to define standard operations on `new_pair`.
Like `add`, `mul`, etc.
This requires creating a new `namespace`.
-/

def new_pair.add'' (a b : new_pair) : new_pair :=
  ⟨a.x + b.x, a.y + b.y⟩

-- Via `namespace` we can start introducing functions in the `new_pair` namespace.
namespace new_pair

def add (a b : new_pair) : new_pair :=
  ⟨a.x + b.x, a.y + b.y⟩

def add' (a b : new_pair) : new_pair where
  x := a.x + b.x
  y := a.y + b.y

example : new_pair := add (⟨2, 3⟩) (⟨1, 4⟩)

def mul (a b : new_pair) : new_pair :=
  ⟨a.x * b.x, a.y * b.y⟩

#check add_comm
#check add
#check add'
#check add''

def add_comm (a b : new_pair) : add a b = add b a := by
  ext
  · simp [add]
    ring
  · simp [add]
    ring

#check add_comm

end new_pair

-- Now outside the namespace we can use these operations
-- via `new_pair.add` and `new_pair.mul`.

#check new_pair.add
#check mul
#check new_pair.mul
#check add_comm
#check new_pair.add_comm

end structures

section pointed_types
-- Let's see a more difficult example, just to get a sense what Lean is capable of.

-- A `pointed type` is a type with a distinguished term.
structure PointedType where
  carrier : Type*
  pt : carrier

#print PointedType
#check PointedType.{0}

-- We can do a `coercion` to associate to a `PointedType` a `Type` in an implicit manner.
instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

-- Here is a example defined for `Type`
def product (X : Type) : Type :=
  X × X

-- We can hence define operations on `PointedType` whenever the input is a `Type`.
#check product (PointedType.mk ℕ 0)

-- Working with `PointedType` is a bit more complicated.
example (X Y : Type) (x : X) (y : Y) :
  PointedType.mk X x = PointedType.mk Y y ↔ ∃ (h : X = Y), h ▸ x = y := by
  constructor
  · intro h
    cases h
    simp
  · intro ⟨h, eq⟩
    simp only [PointedType.mk.injEq]
    constructor
    · rw [h]
    · subst h
      simp only at eq
      rw [eq]

/-
Similar to `PointedType`, we can define a `PointedFunction`
as a function between `PointedType` that preserves the distinguished point.
-/
structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

-- We can even define new notation for `PointedFunction`.
infix:50 " →. " => PointedFunction

-- Similar to types, we can coerce `PointedFunction` to a  `Function`.
instance {X Y : PointedType} : CoeFun (X →. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩

-- This tells the pretty printer to print the operation with `↑`.
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

-- The `@[simp]` attribute tells Lean to use this lemma in `simp` tactics.
@[simp] lemma coe_pt (f : X →. Y) : f X.pt = Y.pt := f.toFun_pt

-- We can use simp to construct the composition.
def comp (g : Y →. Z) (f : X →. Y) : X →. Z :=
  { toFun := g ∘ f
    toFun_pt := by simp}

end PointedFunction

/-
Now, for two pointed functions we can take the regular composition
`Function.comp` and the pointed composition `PointedFunction.comp`.
-/

variable (X Y Z : PointedType) (f : X →. Y) (g : Y →. Z)

#check Function.comp g f
#check PointedFunction.comp g f

end pointed_types

section groups_as_structures

-- `Groups` have already been defined in `MathLib`.
#check Group
-- We can unwind the definition.
#print Group
-- Let us try to reproduce such a definition by hand.

-- Here is a hands-on definition of a group:
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

-- We can now as an example define the integers as a group:
def group_z : Group₁ ℤ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring

-- We can now use this group structure on `ℤ`:
#check group_z.mul
#check group_z.inv_mul_cancel
#check group_z.mul 2 (-3)

-- We can (for example) see that `ℤ` with the group structure `group_z` is commutative:
example (a b : ℤ) : group_z.mul a b = group_z.mul b a := by
  simp [group_z]
  ring

/-
We can use this approach to define any structure
(groups, rings, fields, topological spaces, etc.) in Lean.

However, this approach diverges from standard mathematical practice.

For example, we just write `ℝ` and the additional structure should be recognizable from the context.
-/

#check ℝ
-- In this line `ℝ` is a `group`:
#check (2 : ℝ) + (3 : ℝ)
#check Add.add (2 : ℝ) (3 : ℝ)
-- Here `ℝ` is a `field`:
#check (5 : ℝ) * (0.2 : ℝ)
-- Here `ℝ` is a `topological space` or maybe a `metric space`:
variable (f : ℝ → ℝ)
#check Continuous f

/-
If we followed our approach above, every one of these statements would require
explicitly stating the group structure, field structure, topology, etc.

Fortunately, there is a computer scientific solution in Lean.
Those are `classes` and `instances`.
-/
end groups_as_structures

section groups_as_classes
/-
We want to try to understand `structures`, `classes`, and `instances` in Lean.
In particular, the powerful tool of `type class inference`.

Let us restate a structure, we had seen before:
-/

def GroupR : Group₁ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring
/-
This definition is clearly the worst and we always have to
*remember* and *use* the name of the structure `GroupR`.
-/

#check Group₁.mul GroupR (2:ℝ) (3: ℝ)

-- Lean knows what this structure is, because of `GroupR`.
example (x y : ℝ) : Group₁.mul GroupR x y = x + y := by
  rfl

#eval Group₁.mul GroupR (2:ℝ) (3:ℝ)

/-
We have seen before we can add `tags` to structures.
One such tag is `@[class]`.
-/

@[class] structure Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

/-
The `@[class]` tag tells Lean that this structure is a `class`.
This means that we can use `type class inference` to find the structure.
Concretely, we now construct structures as an `instance`.
We can then access the structure via `inferInstance`.
-/

instance : Group₂ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring

#check Group₂.mul inferInstance (2:ℝ) (3:ℝ)

/-
We can add the option `trace.Meta.synthInstance true`
to see how Lean finds the instance.
-/

set_option trace.Meta.synthInstance true in
#check Group₂.mul inferInstance (2:ℝ) (3:ℝ)

-- Even though we just wrote `inferInstance`, Lean knows what the operation is
example (x y : ℝ) : Group₂.mul inferInstance x y = x + y := by
  rfl

#eval Group₂.mul inferInstance (2:ℝ) (3:ℝ)

/-
That's a much easier than before, because we dont have to remember
and use the name of the structure `GroupR`.

However, this is still not what we usually do in mathematics.
We simply don't state any structure and just use the operations.

For that reason there is `class` which is:
- a structure with the `@[class]` tag
- that makes instances implicit.
-/

class Group₃ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
  mul_inv_cancel : ∀ x : α, mul x (inv x) = one

instance : Group₃ ℝ where
  mul x y := x + y
  one := 0
  inv x := -x
  mul_assoc _ _ _ := add_assoc _ _ _
  one_mul := zero_add
  mul_one := add_zero
  inv_mul_cancel := fun _ => by ring
  mul_inv_cancel := fun _ => by ring


#check Group₁.mul GroupR (2:ℝ) (3:ℝ)
#check Group₂.mul (inferInstance : Group₂ ℝ) (2:ℝ) (3:ℝ)
#check Group₃.mul (2:ℝ) (3:ℝ)

example (x y : ℝ) : Group₃.mul x y = x + y := by
  rfl

#eval Group₃.mul (2:ℝ) (3:ℝ)

-- We assume the existence of classes with `[` `]` brackets.
example (α : Type*) [Group₃ α] (x y : α) : α := Group₃.mul x y
/-
Note here the Group structure is implicit, both
- In the assumption.
- In the parameter of the multiplication operation.
-/


/-
Here are some sample computations using:
- structures
- structures with `@[class]`
- classes
-/

example (α : Type*) (GrpA : Group₁ α) (x y z w : α) :
  Group₁.mul GrpA (Group₁.mul GrpA x (Group₁.mul GrpA y z)) w
  = Group₁.mul GrpA (Group₁.mul GrpA x y) (Group₁.mul GrpA z w) := by
    simp [Group₁.mul_assoc]

example (α : Type*) [GrpA : Group₂ α] (x y z w : α) :
  Group₂.mul GrpA (Group₂.mul GrpA x (Group₂.mul GrpA y z)) w =
  Group₂.mul GrpA (Group₂.mul GrpA x y) (Group₂.mul GrpA z w) := by
    simp [Group₂.mul_assoc]

example (α : Type*) [Group₃ α] (x y z w : α) :
  Group₃.mul (Group₃.mul x (Group₃.mul y z)) w =
  Group₃.mul (Group₃.mul x y) (Group₃.mul z w) := by
    simp [Group₃.mul_assoc]

/-
This last one looks very similar to what we would usually hope for.
We can now even add custom notation and make it even more regular.

Here we use `infixl` to define the notation.
Here `infix` means that the notation is used between two elements.
Then ``infixl` means that the notation is left associative.
This means by definition `x ·₃ y ·₃ z` is interpreted as `x ·₃ (y ·₃ z)`.
The number `60` is the precedence of the operator.
-/

infix:60 " ·₃ "   => Group₃.mul

example (x y : ℝ) : x ·₃ y = x + y := by
  rfl

example (α : Type*) [Group₃ α] (x y z w : α) : (x ·₃ (y ·₃ z)) ·₃ w = (x ·₃ y) ·₃ (z ·₃ w) := by
  simp [Group₃.mul_assoc]

/-
Via instances and suitable notation we can write readable operations,
resembeling regular mathematical notation.

So `+` is just notation for `Add.add`, which is a class for `ℝ`.
-/

#check Add.add

/-
We can now see how all these desired structures are classes:

In this first example we use `AddGroup`, instead of `Group₁`,
as we think of the operation in `Group` by default being multiplication.
-/
example : AddGroup ℝ := inferInstance
example : Ring ℝ := inferInstance
-- Here we use `noncomputable` to construct inverses.
noncomputable example : Field ℝ := inferInstance
example : MetricSpace ℝ := inferInstance
example : TopologicalSpace ℝ := inferInstance

/-
We can now also witness our invented group
structures on `ℝ`:
-/

example : Group₁ ℝ := GroupR
example : Group₂ ℝ := inferInstance
example : Group₃ ℝ := inferInstance

/-
Even better, for a given instance, we can figure out the name via the command `#synth`.
-/
#synth AddGroup ℝ
#synth Ring ℝ
#synth Field ℝ
#synth MetricSpace ℝ
#synth TopologicalSpace ℝ
#synth Group₂ ℝ
#synth Group₃ ℝ

#check Real.instRing

/-
Here is a fancier example!
It defines a group structure on the set of self-equivalences.
We might explain this in detail later.
-/
instance {α : Type*} : Group₃ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
  mul_inv_cancel := Equiv.symm_trans_self

end groups_as_classes

section hierarchies
/-
We have now seen structures, classes, and instances.
Of course, there are many different structures.
Are they related and if yes, how?
The solution is to use `hierarchies`.

Let's try to understand this via an example.

Here is a simple class that assumes add a single term `one`.

Notice here the line `/-- The element one -/` is the doc-string.
That can be used to document the class for users.
-/
class One₁ (α : Type*) where
  /-- The element one -/
  one : α

/- Because of the class we have `[self : One₁ α]` -/
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

/-
Similar to operations, we can add notation for structures
Here, the tag `@[inherit_doc]`, means it has the same
doc-string as the original definition.
-/
@[inherit_doc]
notation "𝟙" => One₁.one

/- Remember for Lean this is just notation. -/
example {α : Type*} [One₁ α] : α := 𝟙
example {α : Type*} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
example {α : Type*} [One₁ α] : One₁.one = (𝟙 : α) := rfl
/-
You can check here, that `(𝟙 : α)` is necessary
so Lean can infer the type.
-/

/-
We now separately proceed to define a class with a
binary operation, named `dia` for `diamond`.

Our eventual goal is that `𝟙` should be an identity element.
-/
class Dia₁ (α : Type*) where
  /-- Diamond operation -/
  dia : α → α → α

-- We saw before, we can introduce infix notation.
infixl:70 " ⋄ "   => Dia₁.dia

/-
We now have a binary operation, we want to make it associative.
Naively, we could just write out the operation and associativity.
-/
class Semigroup₀ (α : Type*) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
Turns out this is a terrible idea!
The point of `class` is to synthesize instances.
But from this definition, Lean cannot recognize a semigroup.
-/

example {α : Type*} [Dia₁ α] (a b : α) : α := a ⋄ b
-- example {α : Type*} [Semigroup₀ α] (a b : α) : α := a ⋄ b

-- Beside `Semigroup₀ α`, we need to add `Dia₁ α` by hand.
example {α : Type*} [Dia₁ α] [Semigroup₀ α] (a b : α) : α := a ⋄ b
/-
This is of course not what we want.
Mathematically, we think of `Semigroup₀` as a `Dia₁` with associativity,
meaning we are extending one structure via another.

One possible way to obtain this, is after the fact, add the
relevant connection to the `Dia₁` structure.
We achieve this via `attribute [reducible, instance]`.
This tells Lean that `Semigroup₀` is an instance of `Dia₁`.
-/

attribute [reducible, instance] Semigroup₀.toDia₁

-- We now have a `Dia₁` instance.
example {α : Type*} [Semigroup₀ α] : Dia₁ α := inferInstance

example {α : Type*} [Semigroup₀ α] (a b : α) : α := a ⋄ b

/-
The better solution is to build in the connection from the start.
We can do this by using `extends` in the definition of `Semigroup₁`.
This means that by definition `Semigroup₁` is a `Dia₁` with associativity.
-/
class Semigroup₂ (α : Type*) extends toDia₁ : Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type*} [Semigroup₂ α] (a b : α) : α := a ⋄ b

/-
Note the `toDia₁` is redundant.
-/

class Semigroup₁ (α : Type*) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
Lean automatically uses `toDia₁`.
Meaning it uses `to` with the previous class name.
-/
#check Semigroup₁.toDia₁

example {α : Type*} [Semigroup₁ α] : Dia₁ α := inferInstance
example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b

/-
We now move one step further and add the identity element.
We do this by extending with `Semigroup₁` and `One₁` at the same time.
-/

class DiaOneClass₁ (α : Type*) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- In `DiaOneClass₁` we have instances of `One₁ α` and  `Dia₁ α`:
example {α : Type*} [DiaOneClass₁ α] : Dia₁ α := inferInstance
example {α : Type*} [DiaOneClass₁ α] : One₁ α := inferInstance
-- We hence use all the previous operations and definitions:
example {α : Type*} [DiaOneClass₁ α] : α := 𝟙
example {α : Type*} [DiaOneClass₁ α] (a b : α) : α := a ⋄ b

/-
Let's use the `trace.Meta.synthInstance true` option
again to see what is going on.
-/
set_option trace.Meta.synthInstance true in
example {α : Type*} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


/-
We have almost defined a monoid.
What is missing is combining associativity and the identity element.
We can do this by extending `Semigroup₁` and `DiaOneClass₁`.

The cool fact is that we do not need any additional information:
-/
class Monoid₁ (α : Type*) extends Semigroup₁ α, DiaOneClass₁ α

/-
Here is an interesting fact about this definition:
The `dia` operation is over-determined.
-/

example {α : Type*} [Semigroup₁ α] (a b : α) : α := a ⋄ b
example {α : Type*} [DiaOneClass₁ α] (a b : α) : α := a ⋄ b
example {α : Type*} [Monoid₁ α] (a b : α) : α := a ⋄ b

/-
Part of what `extends` does is to recognize common information
and make sure they coincide.
-/
example {α : Type*} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

/-
This does not happen if we try to use naive definitions.
For example, here is a more direct definition of a monoid:
-/
class Monoid₂ (α : Type*) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

-- Now we, can check the following:
-- example {α : Type*} [Monoid₂ α] :
--   (Monoid₂.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₂.toDiaOneClass₁.toDia₁.dia := rfl

/-
Why is everything okay in `Monoid₁` but not in `Monoid₂`?
The reason is that `extends` does not do what we tell it to do!
It has a mind on its own. When writing
`extends Semigroup₁ α, DiaOneClass₁ α`
Lean will check if the two structures have intersections and then remove them.

Let's see how this is done in practice:
-/
#check Monoid₁.mk
#check Monoid₂.mk
#print Monoid₂
#print Monoid₁

/-
Note, this does *not* mean there is no `Monoid₁.toDiaOneClass₁`
-/
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

set_option trace.Meta.synthInstance true in
example {α : Type*} [Monoid₁ α] (a b : α) : α := a ⋄ b

/-
We can now define the class `Inv₁` for inverses.
Then extend `Monoid₁` with `Inv₁` to define groups.
-/

class Inv₁ (α : Type*) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₄ (G : Type*) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
  dia_inv : ∀ a : G, a ⋄ a⁻¹ = 𝟙

/-
We can now start proving facts about groups.
Here is a simple example:
-/
example {M : Type*} [Group₄ M] {a : M} (u : ∀ b : M, a ⋄ b = b) : a =  𝟙 := by
  calc
    a = a ⋄ 𝟙:= by  rw [DiaOneClass₁.dia_one]
    _ = 𝟙 := by rw [u 𝟙]

/-
As we see, using the various properties of groups is very annoying.
We need to refer to the proper level of the structure.
For example, we write `DiaOneClass₁.dia_one` instead of just `dia_one`.

The solution is to use `export`.
-/

export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₄ (inv_dia dia_inv)

example {M : Type*} [Group₄ M] {a : M} (u : ∀ b : M, a ⋄ b = b) : a =  𝟙 := by
  calc
    a = a ⋄ 𝟙:= by  rw [dia_one]
    _ = 𝟙 := by rw [u 𝟙]

end hierarchies

section making_implicit_explicit
/-
Let us end with a useful syntax.

When we define functions, then usually the input type and instances are implicit
-/
def gettingid {G : Type*} [Group₄ G] : G := 𝟙

#check gettingid
-- This means we cannot apply anything to `gettingid`.
variable (G : Type*) (h : Group₄ G)
-- None of these options work:
-- #check gettingid G
-- #check gettingid h
-- #check gettingid G h

/-
Whenever we do need to do so,
the solution is to add a `@` in front of the function.
-/
#check @gettingid
#check @gettingid G h

end making_implicit_explicit

section two_operations
/-
We saw how monoids and groups using `structure` and `class`.
But many mathematical objects have more than one operation.
For example, rings, fields, vector spaces, etc. .
How can we deal with that properly?

The trick is to have *2* separate monoids.
-/

#print Monoid
#print AddMonoid
-- We can define `Ring` as an extension of `Monoid` and `AddMonoid`.
#check Ring

/-
Of course this would mean many results have to be proven twice:
- For addition
- For multiplication

That's not how we should do things.

There is hence a transport mechanism that generates statements
about the additive monoid from the multiplicative monoid.

Here is a simple example:
-/
@[to_additive]
lemma mul_four_assoc₂ {α : Type*} [Semigroup α] (a b c d : α) :
  (a * b) * (c * d) = a * (b * (c * d)) := by
    simp [Semigroup.mul_assoc]

#check mul_four_assoc₂
#check add_four_assoc₂

@[to_additive]
lemma inv_eq_of_mul {G : Type*} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  calc
    a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
    _   = a⁻¹ * (a * b) := by rw [← h]
    _   = (a⁻¹ * a) * b := by rw [mul_assoc]
    _   = 1 * b         := by rw [inv_mul_cancel a]
    _   = b             := by rw [one_mul]

#check neg_eq_of_add

end two_operations
