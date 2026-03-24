import MIL.Common
import Mathlib.Data.Set.Prod

/-
This week can you please prepare a lean file taking one through
- Naturals (and how addition and order works),
- Integers (and how addition and order works in this case, and how to go back and forth bwn N and Z),
- Rationals (and also how to go back and forth),
And, if time permits,
- Reals.

The goal is not to be thorough, but to outline the logical structure.
For example, establishing the bijection between N and Z requires such going back and forth.
It is better when the students already understand how Lean thinks of Z.

Something similar for Q, etc.
-/


-- ### Philosophy
/-
  The natural numbers, the integers, the rationals, and the reals all
  have explicit constructions which are necessary to provide for any formal
  system of mathematics, but we rarely "look under the hood" to investigate
  the constructions in practice. Instead, when working with these types, we use
  a collection of properties that characterize the type, and the only time where
  the construction deeply matters is in the proofs of those basic properties.

  That said, if you want to create your own interesting type and prove
  theorems about it, you require knowledge of how to construct a type.
  So we introduce the formal constructions of `Nat`, `Int`, `Rat`, and `Real` in
  Lean as case studies for this process.
-/


-- ## Natural Numbers

/-
The natural numbers are defined roughly in accordance with the Peano axioms,
so we have two constructors, `Nat.zero : Nat` and `Nat.succ : Nat → Nat`.
The other Peano axioms are encoded in the inductive type system.
In particular, the axiom of induction is inherent to Lean via the `.rec`
eliminator for inductive types.

We will now define a new type, Nat', which copies exactly how Nat is defined.
-/

inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'

#check Nat'.rec

example : ∀ n : Nat', n = Nat'.zero ∨ ∃ m : Nat', n = Nat'.succ m := by
  intro n
  induction' n with n ih
  · left
    rfl
  · right
    exists n


-- # Addition

/-
We define addition of natural numbers recursively, as repeated succession
-/

def Nat'.add : Nat' → Nat' → Nat'
  | a, zero => a
  | a, succ b => Nat'.succ (Nat'.add a b)


-- # Subtraction

-- First, we define predecession

def Nat'.pred : Nat' → Nat'
  | zero => zero
  | succ n => n

/-
Already we have something unintuitive: Nat'.pred 0 = 0?
Typically, we would think of zero as an element without a predecessor,
so we might consider Nat.pred as function from ℕ \ {0} to ℕ.
Rather than restricting Nat.pred to a subtype of Nat which excludes Nat.zero,
Lean chooses to define Nat.pred 0 = 0, sacrificing some conceptual cohesion
in order to preserve the typing of Nat.pred. The typing of Nat.pred becomes
important when we define subtraction as repeated predecession.
-/

def Nat'.sub: Nat' → Nat' → Nat'
  | a, zero => a
  | a, succ b => Nat'.pred (Nat'.sub a b)


def three := Nat'.succ $ Nat'.succ $ Nat'.succ $ Nat'.zero
def one := Nat'.succ Nat'.zero

#eval Nat'.sub three one
#eval Nat'.sub one three

/-
Now we see the consequences of defining Nat.pred 0 = 0.

If instead Nat.pred has restricted its domain to exclude 0,
Nat.sub wouldn't be so easy to define, since at each step
in the repeated predecession, we would have to supply a proof
that the argument of Nat.pred is nonzero. To supply those proofs,
`Nat.sub n` would need to restrict its domain to only
those natural number less than or equal to n, but we don't yet
even have a formalized notion of "less than or equal."

As Nat.pred is in fact defined, we can easily define
Nat.sub as repeated succession, and the only strange byproduct
is that `3-5` is assigned a natural number value, namely 0.

Consequently, over Nat, `(n - m) + m` does not always equal `n`,
but `(n + m) - m = n` is provably true:
-/

example : ∀ n m : Nat', Nat'.sub (Nat'.add n m) m = n := by
  intro n m
  induction' m with m ih
  · sorry -- the *unfold* tactic will take care of a lot
  · have : ∀ a b : Nat', a.sub b = (a.succ).sub (b.succ) := by
      intro a b
      induction' b with b ih'
      · sorry
      · sorry
    unfold Nat'.add
    rw [←this]
    exact ih

#check Nat.one_ne_zero

example : ∃ n m : Nat', Nat'.add (Nat'.sub n m) m ≠ n := by
  exists Nat'.zero
  exists Nat'.succ Nat'.zero
  unfold Nat'.add Nat'.add
  unfold Nat'.sub Nat'.sub
  unfold Nat'.pred
  dsimp only
  nofun

/-
This is just a fun example of how Natural number subtraction
doesn't behave the way one would think.
-/
def myDist : Nat → Nat → Nat := fun n => fun m => (n-m)+(m-n)

#eval myDist 3 7
#eval myDist 7 3


-- # Division

-- # Order

#check Nat.le

inductive Nat'.le : Nat' → Nat' → Prop
  | refl {n} : Nat'.le n n
  | step {n} {m} : Nat'.le n m → Nat'.le n (succ m)
