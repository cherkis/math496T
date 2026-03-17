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
-/

inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'

#check Nat'.rec

-- # Addition

/-
We define addition of natural numbers recursively, as repeated succession
-/

def Nat'.add : Nat' → Nat' → Nat'
  | a, zero => a
  | a, succ b => Nat'.succ (Nat'.add a b)

-- # Order

#check Nat.le

inductive Nat'.le : Nat' → Nat' → Prop
  | refl {n} : Nat'.le n n
  | step {n} {m} : Nat'.le n m → Nat'.le n (succ m)

-- ## Integers

/-
There are two constructors for integers, `Int.ofNat : Nat → Int` and
`Int.negSucc : Nat → Int`.
`ofNat` reflects that we can think of any natural number as an integer, but
these are not all the integers, so we need another constructor `negSucc` to
catch all the negative integers. To avoid double-counting 0, `negSucc n`
corresponds to `-(n+1)`.

The usual negation is defined separately, `Int.negOfNat : Nat → Int`

-/

-- Lean uses inductive types again
inductive Int' : Type where
  | ofNat   : Nat → Int'
  | negSucc : Nat → Int'

def negThree : Int' := Int'.negSucc 2



-- # Addition

def Int'.subNatNat (m n : Nat) : Int' :=
  match (n - m : Nat) with
  | 0          => Int'.ofNat (m - n)  -- m ≥ n
  | Nat.succ k => Int'.negSucc k

def Int'.add : Int' → Int' → Int'
  | Int'.ofNat m  , Int'.ofNat n   => Int'.ofNat (m + n)
  | Int'.ofNat m  , Int'.negSucc n => Int'.subNatNat m (Nat.succ n)
  | Int'.negSucc m, Int'.ofNat n   => Int'.subNatNat n (Nat.succ m)
  | Int'.negSucc m, Int'.negSucc n => Int'.negSucc (Nat.succ (m + n))

-- # Order

inductive NonNeg : Int' → Prop where
  | mk {n : Nat} : NonNeg (Int'.ofNat n)

-- ## Rationals
/-
The typical construction of ℚ is as a quotient of ℤ × (ℤ-{0})
under the equivalence relation (a, b) ∼ (x, y) iff a·y = b·x .
This construction is nice because it extends to a broader concept
of "localization" in algebra.

Our lean construction instead takes advantage of Euclid's algorithm
to think of rational numbers as reduced fractions with a positive nonzero
denominator. The benefit of this construction is that there is a singular
pair (p, q) associated to each rational number rather than an equivalence
class of pairs, so the computer can do concrete calculations.
-/


#check Rat

-- # Addition

-- # Order


theorem even_or_odd : ∀ n : Nat, (∃ k, n = 2*k) ∨ (∃ k, n = 2*k + 1) := by
  intro n
  induction' n with n ih
  · left
    exists 0
  · rcases ih with (n_even | n_odd)
    · right
      obtain ⟨k, hk⟩ := n_even
      exists k
      rw [hk]
    · left
      obtain ⟨q, hq⟩ := n_odd
      exists q + 1
      rw [hq]
      omega

theorem zero_not_odd : ¬ (∃ k, 0 = 2*k + 1) := by
  push_neg
  intro k
  apply Nat.zero_ne_add_one

theorem not_even_and_odd : ∀ n : Nat, ¬((∃ k, n = 2*k) ∧ (∃ k, n = 2*k + 1)) := by
  intro n
  push_neg
  rintro ⟨k, hk⟩
  intro q
  rw [hk]
  intro h
  clear n hk
  rcases lt_or_ge q k with (qltk | kleq)
  · apply zero_not_odd
    exists k-(q+1)
    rw [Nat.mul_sub, ←Nat.sub_add_comm, Nat.mul_add, h, add_assoc, Nat.sub_self]
    apply Nat.mul_le_mul_left
    exact qltk
  · suffices : 2*q - 2 * k + 1 = 0
    · apply zero_not_odd
      exists q - k
    rw [←Nat.sub_add_comm, h, Nat.sub_self]
    apply Nat.mul_le_mul_left
    exact kleq

theorem eq_of_sum_eq : ∀ {n m : Nat}, n + n = m + m → n = m := by
  intro n m
  intro h
  apply le_antisymm
  · contrapose! h
    apply ne_of_gt
    exact add_lt_add h h
  · contrapose! h
    apply ne_of_lt
    apply add_lt_add h h

def zigzag : Int → Nat
  | Int.ofNat n => n+n
  | Int.negSucc n => n+n+1

theorem zigzag_inj : Function.Injective zigzag := by
  intro x
  match x with
  | Int.ofNat n =>
    intro y
    match y with
    | Int.ofNat m =>
      intro h
      dsimp [zigzag] at h
      congr
      exact eq_of_sum_eq h
    | Int.negSucc m =>
      intro h
      dsimp [zigzag] at h
      exfalso
      apply not_even_and_odd (n+n)
      constructor
      · exists n
        rw [two_mul]
      · exists m
        rw [h, two_mul]
  | Int.negSucc n =>
    intro y
    match y with
    | Int.ofNat m =>
      intro h
      dsimp [zigzag] at h
      exfalso
      apply not_even_and_odd (n+n+1)
      constructor
      · exists m
        rw [h, two_mul]
      · exists n
        rw [two_mul]
    | Int.negSucc m =>
      intro h
      dsimp [zigzag] at h
      congr
      let claim := add_right_cancel h
      exact eq_of_sum_eq claim



theorem zigzag_surj : Function.Surjective zigzag := by
  intro n
  let claim := even_or_odd n
  rcases claim with (⟨k, hk⟩|⟨k, hk⟩)
  · exists Int.ofNat k
    dsimp [zigzag]
    rw [hk, two_mul]
  · exists Int.negSucc k
    dsimp [zigzag]
    rw [hk, two_mul]
