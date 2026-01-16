import Mathlib

/- # Lecture 1: Type Theory and LEAN + Mathlib Intro
## Welcome
Intro and Goals
Tools: VSCode, LEAN4, Mathlib
Follow instructions on https://github.com/cherkis/math496T

## Traditional Math Foundations: Set Theory + First-Order Logic
Zermelo-Fraenkel set theory with the Axiom of Choice (ZFC)
An element can belong to many sets

Examples of Props and not Props

## Type Theory
Judgements: a:T and a=_A a
Every terms has one specific type

Interpretations of Type Theory: Table
Types | Logic  |  Sets  |  Topology | Programming
...
term : type
proof : Proposition
element : Set
point : Space
program : Specifications
(see CorrespondencesTable.pdf on D2L)

### Basic Types
True
False
Bool
Nat (?)
Prop

Context ⊢ judgement

## LEAN
(__#check and #eval and #print__)
(__def, theorem, lemma, example__)
(__import, open, section x ... end x__)
(__def, fun__)

Currying: `f (x)` or, better `f x`.  But not `f(x)`, use space between `f` and `(x)`.
Multi-variable functions: `g : A -> B -> C`
Use `g x y`, or `g (x) (y)` for the value of a function fo two variables `g(x,y)`.  Also, `g x` is now a function of one variable, `g x : B -> C`.

Symbol Entry: hover to see how to enter any symbol.  Click to jump to a definition.
-/

/- Check types -/
#check Nat
#check ℕ

#check 1
#check Nat.add
#check Nat.succ
#check @Nat.succ
#check 1+1 = 2
#check 1+1=3
#check Nat = ℕ
#check Prop

#check Type
#check Type 1 -- etc
#check Type 1 = Type 1

#check true = false
#check rfl
#check Eq

#check True
#check trivial
#check (trivial : True)
#check False

/- Define quantities (terms, types, etc)-/
def n : ℕ := 5
def m : ℕ := 2 + 2

#check n
#check m

-- To evaluate an expression:
#eval n
#eval m

#check n + m
#eval  n + m

-- to see a definition:
#print add_comm -- a + b = b + a

/- Defining functions -/
def f (x : ℕ) := x * x
def g (x : ℕ) (y : ℕ) := x*x + y
def h := g 2
#check f
#check @f
#print h
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

-- This lets Lean know that P, Q, and R denote propositions:
variable (P Q R : Prop)

-- Implication as a function: P -> Q
theorem simpleImplication : P → P := fun x => x

-- `theorem` or `lemma` are a way of defining a function on propositions.  Both require a name, e.g. `simpleImplication` above.  You are free to give any name, but you must give it one.  This makes sense, since it allows you to invoke this theorem using this name later.
-- A theorem is a function from its hypotheses (some propositions) to its conclusion.  Given proofs of all of its hypotheses, it produces a proof of its conclusion.

-- `example` is like `theorem` or `lemma`, but requires no name.

example : P → P := id

-- Two types (True : Prop) and (False : Prop), not to confuse with (true false : Bool)

#check (trivial : True)
-- Of course False type is empty.

example : True := sorry

example : P -> True := sorry
