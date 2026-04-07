-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

--! # Homework 9: Supremum and Infimum

/-!
This homework covers Lectures 22-23.

Topics: intervals in `ℝ`; upper and lower bounds; supremum and infimum;
the ε-approximation property; the separation theorem; nested intervals.

**Total: 50 points.**
-/

#check Set.mem_setOf -- : a ∈ {x | p x} ↔ p a

-- ============================================================================
-- Problem 1 (4 points): Midpoint of a closed interval
-- ============================================================================

/-
If `a ≤ b`, then the midpoint `(a + b) / 2` also lies in `[a, b]`.
-/

@[autogradedProof 4]
theorem problem1 (a b : ℝ) (h : a ≤ b) :
    (a + b) / 2 ∈ Set.Icc a b := by
  sorry
  done


-- ============================================================================
-- Problem 2 (5 points): Positive sets have positive supremum
-- ============================================================================

/-
If every element of a nonempty bounded-above set is positive, then its
supremum is positive.
-/

@[autogradedProof 5]
theorem problem2 (S : Set ℝ) (hS : S.Nonempty) (hB : BddAbove S)
    (hpos : ∀ x ∈ S, 0 < x) :
    0 < sSup S := by
  sorry
  done


-- ============================================================================
-- Problem 3 (6 points): A predicate-defined supremum
-- ============================================================================

/-
Let `S = {x : ℝ | 0 ≤ x ∧ x ^ 2 ≤ 9}`.  Prove that `sSup S = 3`.

Hint: use `le_antisymm`.  For the `≤` direction, show that any `x ∈ S` must
satisfy `x ≤ 3`.  For the `≥` direction, show that `3 ∈ S`.
-/

@[autogradedProof 6]
theorem problem3 : sSup {x : ℝ | 0 ≤ x ∧ x ^ 2 ≤ 9} = 3 := by
  sorry
  done


-- ============================================================================
-- Problem 4 (6 points): The open interval `(0, 1)` has no maximum
-- ============================================================================

/-
There is no element `m ∈ (0, 1)` which is at least every other element of
`(0, 1)`.
-/

@[autogradedProof 6]
theorem problem4 :
    ¬ ∃ m ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≤ m := by
  sorry
  done


-- ============================================================================
-- Problem 5 (7 points): A larger supremum gives a witness
-- ============================================================================

/-
If `sSup S < sSup T`, then some element of `T` lies strictly above `sSup S`.

Hint: argue by contradiction.  If every `t ∈ T` satisfies `t ≤ sSup S`, then
`csSup_le` implies `sSup T ≤ sSup S`.
-/

@[autogradedProof 7]
theorem problem5 (S T : Set ℝ) (hT : T.Nonempty) (hB : BddAbove T)
    (h : sSup S < sSup T) :
    ∃ t ∈ T, sSup S < t := by
  sorry
  done


-- ============================================================================
-- Problem 6 (7 points): The separation theorem
-- ============================================================================

/-
If every element of `S` is at most every element of `T`, then `sSup S ≤ sInf T`.

Hint: first prove that `sSup S` is a lower bound for `T`, then apply `le_csInf`.
-/

@[autogradedProof 7]
theorem problem6 (S T : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSB : BddAbove S) (hTB : BddBelow T)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s ≤ t) :
    sSup S ≤ sInf T := by
  sorry
  done


-- ============================================================================
-- Problem 7 (7 points): Nested intervals pinch to `0`
-- ============================================================================

/-
Suppose `c` belongs to every interval `[0, 1 / (n + 1)]`.  Prove that `c = 0`.

 Hint: first show `0 ≤ c`, and then show `c ≤ 1 / (n + 1)` for every `n`.
 Recall `exists_nat_one_div_lt`.
-/

@[autogradedProof 7]
theorem problem7 (c : ℝ)
    (h : ∀ n : ℕ, c ∈ Set.Icc (0 : ℝ) (1 / ((n : ℝ) + 1))) :
    c = 0 := by
  sorry
  done


-- ============================================================================
-- Problem 8 (8 points): Zero width means a single value
-- ============================================================================

/-
If a nonempty set has the same infimum and supremum, then every element of the
set equals that common value.

Hint: for `x ∈ S`, use `le_csSup` and `csInf_le`.
-/

@[autogradedProof 8]
theorem problem8 (S : Set ℝ) (hS : S.Nonempty) (hAbove : BddAbove S)
    (hBelow : BddBelow S) (hEq : sInf S = sSup S) :
    ∀ x ∈ S, x = sSup S := by
  sorry
  done
