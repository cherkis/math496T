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


#check Rat

-- # Addition

-- # Order
