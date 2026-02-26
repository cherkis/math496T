-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Data.Int.Basic


/-! # Homework 4: Quotients
Based on Lectures 12–13.
-/

-- ## Integers as a quotient
-- Define an equivalence relation on pairs of natural numbers.

def CongZ (p q : ℕ × ℕ) : Prop := p.1 + q.2 = q.1 + p.2

-- Prove this is an equivalence relation,
-- by proving reflexivity,
@[autogradedProof 5]
theorem problem1 : ∀ p : ℕ × ℕ, CongZ p p := by
  sorry
  done

-- symmetry,
@[autogradedProof 5]
theorem problem2 : CongZ p q → CongZ q p := by
  sorry
  done

-- and transitivity.
@[autogradedProof 5]
theorem problem3 : CongZ p q → CongZ q r → CongZ p r := by
  sorry
  done

-- These assemple into a theorem
theorem congZ_equiv : Equivalence CongZ where
  refl := problem1
  symm := problem2
  trans := problem3

-- and provide a `Setoid` instance.
instance congZSetoid: Setoid (ℕ × ℕ) where
  r := CongZ
  iseqv := congZ_equiv

-- and use this Setoid instance to define our custom integer type as a quotient type!
abbrev newZ := Quotient congZSetoid

-- Consider a few integers as elements of `newZ`:
def negOne : newZ := Quotient.mk congZSetoid (1, 2)
def negOne' : newZ := Quotient.mk congZSetoid (2, 3)
def negTwo : newZ := Quotient.mk congZSetoid (1, 3)
def negTwo' : newZ := Quotient.mk congZSetoid (5, 7)

-- Prove that 1/2 = 2/4
@[autogradedProof 5]
theorem problem4 : negOne = negOne' := by
  sorry
  done

-- Prove that 1/2 ≠ 1/3
@[autogradedProof 5]
theorem problem5 : negOne ≠ negTwo := by
  sorry
  done


-- Prove that the absolute value is well-defined on the quotient.
def newAbs (p : ℕ × ℕ) : ℕ := if p.1 ≥ p.2 then p.1 - p.2 else p.2 - p.1

-- To show this is well-defined, we need to show that if p and q are CongZ, then newAbs p = newAbs q.
@[autogradedProof 5]
theorem problem6 : ∀ (a b : ℕ × ℕ), a ≈ b → newAbs a = newAbs b := by
  sorry
  done

-- Then we can use `Quotient.liftOn` to define a function on `newZ` that computes the absolute value.
def newZAbs (z : newZ) : ℕ := Quotient.liftOn z newAbs problem6

@[autogradedProof 10]
theorem problem7 : newZAbs negTwo = 2 := by
  sorry
  done

@[autogradedProof 10]
theorem problem8 : newZAbs ⟦(1,0)⟧  = newZAbs negOne := by
  sorry
  done
