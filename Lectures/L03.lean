import MIL.Common

/- # Lecture 3

## Summary of Lecture 1
1. Theorem = declaration of a type (Prop), proof = a term of that type.
Another view: A theorem is a set of all its proofs.  A proof is an element of that set.
2. Proof Irrelevance (in LEAN).
3. Each type has:
   __Formation__,
  __Introduction__,
  __Elimination__,
  __Computation__, and (possibly)
  __Uniqueness Rules__.
4. Implication is a function P → Q
5. `True` and `False` types.
6. Tactics: __intro, exact, apply, contradiction, exfalso__
-/

variable (P Q R : Prop)

-- ## Negation: Not   ¬
example : (¬ P) = (P → False) := by rfl
-- Not P means one can derive False from P.
-- This is the definition in Lean.



example : ¬False := by
intro h
exact h

example : ¬False := False.elim

example : ¬False := id

example : ¬True → P := by
intro notTrue
exfalso
apply notTrue
exact True.intro

example : P → ¬ P → False := by
 intro hp hnp
 apply hnp
 exact hp


example : ¬ P → P → False := by
intro notP hp
apply notP
apply hp


example : (P → Q) → (¬Q → ¬P) := by
intro q_of_p notQ hp
apply notQ
apply q_of_p
exact hp
done

example : ¬(P → Q) → (¬Q) := by
intro h hq
apply h
intro hp
exact hq

example : (P → Q) → ¬P → ((P → Q) → Q) → Q := sorry

example : (P → Q) → ¬Q → ((P → Q) → Q) → False := sorry

example : ¬(P → Q) → (¬Q) := by
  sorry

example : (P → Q) → ¬P → ((P → Q) → Q) → Q := by
  sorry

-- New tactic __dsimp__
-- __dsimp [Not]__

example : P → ¬ ¬ P := by
  intro hp
  dsimp [Not]
  intro hnp
  apply hnp
  apply hp

example : (P → Q) → ((¬ Q) → ¬ P) := by
 intro q_of_p notQ
 dsimp [Not]
 dsimp [Not] at notQ
 sorry
 done

-- ## Product Type: (and And)

#check Prod -- is a type constructor
-- Prod : Type → Type → Type
#check And -- is a type constructor
-- And : Prop → Prop → Prop

variable (X Y : Type) (a : X) (b : Y)
example : Prod X Y = (X × Y) := rfl -- X × Y is a syntactic sugar for Prod X Y

variable (P Q : Prop)
#check (P,Q)
#check (P,Q) -- NOTE: this is NOT a Prop
#check P∧Q -- This is a Prop

example (hp:P) (hq:Q) : P∧Q :=  And.intro hp hq
example (hp:P) (hq:Q) : P∧Q :=  ⟨hp,hq⟩ -- NOte these angle brackets!
example (hp:P) (hq:Q) : And.intro hp hq =  ⟨hp,hq⟩ := rfl
example (hx:X) (hy:Y) : X×Y :=  (hx,hy)

/-
Pattern for introducing a new type
1. Formation Rules
2. Introduction rules (constructors)
3. Elimination rules (eliminators)
4. Computation rules (how eliminator acts on a constructor)
5. Uniqueness principle (optional)
-/

/-
Product Type example:

1. Formation rule

Γ ⊢ A:Type    Γ ⊢ B:Type
-------------------------  Prod
Γ ⊢ A×B : Type

-/
#check Prod

/-
2. Introduction rule
Γ ⊢ a : A      Γ ⊢ b : B
---------------------------- Prod.intro
Γ, a:A, b:B ⊢ (a,b) : A × B
-/

#check Prod.mk

/-
3. Elimination rules

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.fst
Γ, z : A×B ⊢ z.fst : A

and

Γ ⊢ A:Type    Γ ⊢ B:Type
------------------------- Prod.snd
Γ, z : A×B ⊢ z.snd : B

(or z.1 for z.fst and z.2 for z.snd)
-/
#check Prod.fst
#check Prod.snd

#eval (3,4).fst

/-
More generally, to define a function on A×B

Γ⊢a:A   Γ⊢b:B   Γ⊢g: A → B → C
------------------------------- Prod.rec  (Recursor or recursion principle)
  f: A×B → C :=(a,b)↦ g (a) (b)

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

#check Prod.ext
#check Prod.mk

#check Prod
#check Prod.casesOn -- discuss later

#check And       -- Formation
#check And.intro -- Introduction.  Same as ⟨ , ⟩
#check And.right -- Elimination
#check And.left  -- Elimination

-- Make a table of corresponding rules for And


theorem modusTollens : (P → Q) ∧ ¬Q → ¬ P := by
intro h hp
apply h.right
apply h.left
exact hp
done

example:  (P → Q) ∧ ¬Q → ¬ P := by
rintro ⟨h1,h2⟩

example : (P ∧ Q) → P := sorry

example : (P ∧ Q) → (Q ∧ P) := sorry

example : (P ∧ Q) → (P ∧ (P ∧ Q)) := by
  sorry

example : R → (R ∧ R) := by
  sorry

-- Equivalence as a pair
-- `P ↔ Q` is really
-- `P → Q` (modus ponens) and `Q → P` (modus ponens reversed)
-- for `h : P ↔ Q` we have `h.mp : P → Q` and `h.mpr : Q → P`

example : (P ↔ Q) ↔ (P → Q) ∧  (Q → P) := by
constructor
. intro h
  constructor
  exact h.mp
  exact h.mpr
. rintro ⟨ha,hb⟩
  constructor
  exact ha
  exact hb

#print Iff


-- ## Law of Excluded Middle (LEM): P ∧ ¬ P
-- Constructive vs Intuitionistic Math

-- Certainly, negation of the Law of Excluded middle is false!

example : ¬ (P ∧ ¬ P) := sorry
