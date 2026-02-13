import Mathlib.Tactic
/-
Do the exercises in Theorem Proving in Lean 4 about the Natural Numbers defined inductively
Think about the extent to which inductive types can be hidden from the student
    until they are more versed in type theory
The essential problem is that we have a lot of machinery in and around propositions that
    ought to be explained to establish the curry-howard isomorphisms, but
    it's difficult to reason without having objects to reason with. MIL solves this by
    presuming that the natural numbers and the integers are sufficiently simple,
    but following Aubrey's book implores us to take the time to build the natural numbers
    from the ground up. This approach will delay the aspect of proof, but perhaps for the better.
-/
theorem nat_plus_one_squared (n : Nat) : (n+1)^2 = n^2 + 2*n + 1 := by sorry



theorem sq_ge_self (n : Nat) : n^2 ≥ n := by sorry


#check And

#check Sum
#check Prod

/-
Product Type example:

1. Formation rule

Γ ⊢ A:Type    Γ ⊢ B:Type
-------------------------  Prod
Γ ⊢ A×B : Type

2. Introduction rule
Γ ⊢ a : A      Γ ⊢ b : B
---------------------------- Prod.intro
Γ, a:A, b:B ⊢ (a,b) : A × B

3. Elimination rules

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.fst
Γ, z : A×B ⊢ z.fst : A

and

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.snd
Γ, z : A×B ⊢ z.snd : B

(or z.1 for z.fst and z.2 for z.snd)

4. Computation rule
a : A      b : B
----------------- Prod.mk
(a,b) : A × B
----------------- Prod.fst
(a,b).fst = a : A

5. Uniqueness rule
z:A×B
----------------------- Prod.ext
(z.fst,z.snd) =_{A×B} z
-/

#check Sum.inl

/-
Sum Type example:

1. Formation rule

Γ ⊢ A:Type    Γ ⊢ B:Type
-------------------------  Sum
Γ ⊢ A⊕B : Type

2. Introduction rules
Γ ⊢ a : A
---------------------------- Sum.inl
Γ, a:A ⊢ (a,b) : A × B

3. Elimination rule

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.fst
Γ, z : A×B ⊢ z.fst : A

and

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.snd
Γ, z : A×B ⊢ z.snd : B

(or z.1 for z.fst and z.2 for z.snd)

4. Computation rule
a : A      b : B
----------------- Prod.mk
(a,b) : A × B
----------------- Prod.fst
(a,b).fst = a : A

5. Uniqueness rule
z:A×B
----------------------- Prod.ext
(z.fst,z.snd) =_{A×B} z
-/



#check Sigma
