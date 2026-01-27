import MIL.Common

/- # Lecture 2:

## Summary of Lecture 1:
1. Intro: VSCode, Mathlib, clone https://github.com/cherkis/math496T
2. Types and terms. Two judgements: a:T and, for a:T and b:T a=_A b; and rfl : a=a.
3. Interpretations of Type Theory: Types | Logic  |  Sets  |  Topology | Programming
4. Universes: Type, Type 1, Type 2, ...
5. Prop type, implication as a function
6. Lean commands:
   __#check and #eval and #print__ and __def, fun, theorem, lemma, example__
7. Currying and multivariable functions.
8. Cursor over various symbols and functions to see descriptions how to type them.


## Today's assignment:
Register on Zulip: https://leanprover.zulipchat.com
and join `UA Lean Group`

## Term mode and Tactic Mode in LEAN
Today's LEAN commands: __import, open, section x ... end x__
        LEAN tactics : __intro, exact, apply__
                   and __contradiction, exfalso__
-/

#check rfl
#check (fun n => n + 1)
def oldFunction (m : ℕ) := m + 1
def newFunction : ℕ → ℕ := (fun n => n + 1)
example : oldFunction = (fun n => n + 1) := rfl  -- Term mode
example : oldFunction = (fun n => n + 1) := by rfl  -- Tactic mode

-- # Logic
-- Well formed vs True.  Less `True` more `provable`

/-
Theorem or Lemma is a **declaration of a Prop type**
Proof is a **term of that type**

## Proof as a tree:
Peperproof illustration: https://github.com/Paper-Proof/paperproof
WARNING: No DOT attempt using Paperproof in your VSCode yet.  Use Paperproof Codespace instead, if you have to. Choose 4 cores option.

Every type has:
1. Formation Rules
2. Introduction rules (constructors)
3. Elimination rules (eliminators)
4. Computation rules (how eliminator acts on a constructor)
5. Uniqueness principle (optional)
-/

variable (P Q R : Prop)

-- Implication as a function: P → Q

theorem selfImp : P → P := fun hp => hp -- term proof

theorem selfImp' : P → P := id

theorem selfImp2 : P → P := by
  intro hp
  exact hp

theorem impImp : P → Q → P := by
  intro hp
  exact (fun _ => hp)

theorem impImp' : P → Q → P := by
  intro hp
  intro hq
  exact hp

theorem impImp'' : P → Q → P := by
intro hp hq
exact hp

theorem impImp''' : P → Q → P := by -- HOLE
  intro hp _
  exact hp
  done

-- Two types `True : Prop` and `False : Prop`, not to confuse with `true : Bool` and `false : Bool`
#check trivial
#check (trivial : True)
-- Of course False type is empty.

-- ## The THIRD JUDGEMENT: ctx ⊢ term

/- ### True : Type
**Formation Rule:**

------------
True : Type

**Introduction Rule:**

------------ True.intro
trivial

**No elimination rule**
-/

example : True := True.intro --sorry
example : True.intro = trivial := rfl

example : P -> True := sorry


/- ### False : Type
also called Empty type
**Formation Rule:**

------------
False : Type

**No Introduction Rule:**

**Elimination rule**
False
------------ False.elim
a : A

-/
#check False.elim

example (hf : False) :  Prop := False.elim hf -- **Term mode**

example (hf : False) :  Prop := by -- brings you into **Tactic mode**
  contradiction

example (hf : False) :  Prop := by
  exfalso
  exact hf



example : False → P := False.elim -- term mode
example : False → P := by
  intro h
  contradiction
  done

example : False → P := by
  intro h
  apply False.elim
  apply h

example : (P → Q) → (Q → R) → P → R := sorry

example : (P → Q) → ((P → Q) → P) → Q := sorry
