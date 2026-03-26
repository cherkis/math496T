import Mathlib.Data.Set.Prod
import MIL.Common


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

structure Rat' where
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq


#check Rat.mk' -- Inherent constructor
#check mkRat -- Smart constructor

#eval mkRat 7 0
#eval mkRat 6 4
--#eval Rat.mk' 6 4   --This will throw an error, since 4 and 6 are not coprime
#eval mkRat 0 0
#eval (24 : Rat) / 16

-- # Field Axioms
/-
The rational numbers are part of a class of sets called a field.
A set is a field if there are notions of multiplication and addition
on that set which each have inverses, identities, and some other
properties described below.
-/


#print Field
#check Rat.add
#check Rat.add_assoc
#check Rat.zero_add
#check Rat.add_comm

#check Rat.mul
#check Rat.mul_add
#check Rat.mul_assoc
#check Rat.mul_zero
#check Rat.mul_comm
#check Rat.mul_one

#check Rat.neg
#check Rat.sub_eq_add_neg
#check Rat.neg_add_cancel

#check Rat.inv
#check Rat.div_def
#check Rat.inv_mul_cancel
