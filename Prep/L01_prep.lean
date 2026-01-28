import Mathlib
-- import Paperproof -- No DOT attempt using Paperproof yet.  Use Paperproof Codespace instead, if you have to.

/- # Lecture 1: Type Theory and LEAN + Mathlib Intro
## Welcome
Intro:
Goals
Tools: VSCode, Mathlib, Zulip, Codespace

## Traditional Math Foundations: Set Theory + Propositional Logic
Zermelo-Fraenkel set theory with the Axiom of Choice
An element can belong to many sets

Examples of Props and not Props

## Type Theory
Judgements: a:T and a=_A a
Every terms has one type

Interpretations of Type Theory: Table
Types | Logic  |  Sets  |  Topology | Programming
...
term : type
proof : Proposition
element : Set
point : Space
program : Specifications

### Basic Types
True
False
Bool
Nat (?)

Context ⊢ judgement

## LEAN
(__#check and #eval and #print__)
(__def, theorem, lemma, example__)
(__import, open, section x ... end x__)
(__def, fun__)

Currying: f (x) or, better f x.
Multi-variable functions: A -> B -> C

Symbol Entry (hover)

Tactics: __rfl, intro and rintro__

term mode and tactic mode
-/

/- Check types -/
#check Nat
#check ℕ

#check 1
#check Nat.add
#check Nat.succ
#check @Nat.succ
#check 1+1 = 2
#check Nat = ℕ
#check Prop

#check Type
#check Type 1 -- etc
#check Type 1 = Type 1

#check true = false
#check rfl

#check True
#check trivial
#check (trivial : True)
#check False

/- Define quantities (terms, types, etc)-/
def n : ℕ := 5
def m : ℕ := 2 + 2

#check n
#check m

#eval n
#eval m

#check n + m
#eval  n + m

#print add_comm -- a + b = b + a

/- Defining functions -/
def f (x : ℕ) := x * x
def g (x : ℕ) (y : ℕ) := x*x + y
#check f
#check @f
/- Currying -/
#check g 2

#eval f 2
#eval g 2 1

/- Lambda abstraction -/
def ff : ℕ → ℕ := fun z => z * z
def gg : ℕ → ℕ → ℕ := fun a => fun b => a * a + b
def gg' : ℕ → ℕ → ℕ := λ x => λ y => x * x + y
#check ff
#check gg
def hh : ℕ -> ℕ := λ z ↦ z*z+1


-- Cursor over various symbols and functions to see descriptions how to type them.

-- # Logic

variable (P Q R : Prop)

-- Implication as a function: P -> Q

example : P → P := sorry

-- Two types (True : Prop) and (False : Prop), not to confuse with (true false : Bool)

#check (trivial : True)
-- Of course False type is empty.

example : True := sorry

example : P -> True := sorry

example : False → P := False.elim -- term mode
example : False → P := by
  intro h
  contradiction
  done

example : False → P := by
  intro h
  apply False.elim
  apply h

-- Negation: Not   ¬
example : (¬ P) = (P → False) := by rfl
-- Not P means one can derive False from P.
-- __dsimp [Not]__


example : P → ¬ ¬ P := by
  intro hp
  dsimp [Not]
  intro hnp
  apply hnp
  apply hp

example : (P → Q) → ((¬ Q) → ¬ P) := by
 intro p_of_q nq p
 apply nq
 apply p_of_q
 apply p

theorem modusTollens : (P → Q) ∧ ¬Q → ¬ P := by sorry

theorem elimination : (P ∨ Q) ∧ ¬ P → Q := by
rintro ⟨hp | hq, np⟩
contradiction
exact hq
done

example : P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R) := by
constructor
rintro (hp | ⟨hq, hr⟩)
. constructor
  left
  exact hp
  left
  exact hp
. constructor
  right
  exact hq
  right
  exact hr
rintro ⟨(hp | hq), (hpp | hr)⟩
left; exact hp
left; exact hp
left; exact hpp
right
constructor
exact hq
exact hr
done


#exit


example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
rintro ⟨hp, hq | hr⟩
. left
  constructor
  exact hp
  exact hq
. right
  constructor
  exact hp
  exact hr
rintro (hpq | hpr)
constructor
exact hpq.left
left
exact hpq.right
constructor
exact hpr.left
right
exact hpr.right
done

-- in more detail
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
. intro h
  obtain ⟨hp, hqr⟩  := h
  obtain (hq | hr) := hqr
  . left
    constructor
    exact hp
    exact hq
  . right
    constructor
    exact hp
    exact hr
sorry

-- using more terms
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
rintro ⟨hp, hq | hr⟩
. left
  exact ⟨hp,hq⟩
. right
  exact ⟨hp,hr⟩
rintro (⟨hp,hq⟩ | ⟨hp,hr⟩)
. exact ⟨hp,by left; apply hq⟩
. exact ⟨hp,by right; apply hr⟩
done









/- Example of proposition type -/
#check f = ff

-- fill in these sorrys
example : f = ff := sorry
example : gg = gg' := sorry
-- note the type mismatch: I.E. this is NOT a Prop
example : f ≠ g := sorry
-- we are still to build some more to prove
example : f ≠ g 1 := sorry
/-by
  intro h
  have : 1 = 2 := by
   calc
    1 = f 1 := by dsimp [f]
    _ = g 1 1 := by rw [h]
    _ = 2 := by dsimp [g]
  linarith
-/
