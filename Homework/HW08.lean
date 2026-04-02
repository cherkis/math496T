-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Irrational
import Mathlib.Order.Interval.Set.Basic

--! # Homework 8: Real Numbers and Density of ℚ

/-!
This homework covers Lectures 20–21 (Real Numbers).

Topics: type coercions between ℕ, ℤ, ℚ, ℝ; the new tactics
`linarith`, `nlinarith`, `field_simp`, `positivity`, `push_cast`;
the Archimedean property; the floor function; density of ℚ in ℝ;
density of irrationals in ℝ.

**Total: 50 points.**
-/


-- ============================================================================
-- Problem 1 (5 points): The Archimedean squeeze
-- ============================================================================

/-
If a nonnegative real number is at most `1/n` for every positive
natural number `n`, it must be zero. This fundamental lemma underlies
every limit argument in analysis.

Hint: By contradiction. If `x > 0`, the Archimedean property (via
`exists_nat_one_div_lt`) gives an `n` with `1/n < x`,
contradicting the hypothesis.
-/

@[autogradedProof 5]
theorem problem1 (x : ℝ) (hx : 0 ≤ x)
    (h : ∀ n : ℕ, 0 < n → x ≤ 1 / (↑n : ℝ)) : x = 0 := by
  sorry
  done


-- ============================================================================
-- Problem 2 (6 points): AM-GM variant
-- ============================================================================

/-
The arithmetic mean – geometric mean inequality (for two numbers)
states that a·b ≤ (a² + b²)/2.  This follows from the fact that
(a − b)² ≥ 0.

Hint: `nlinarith` can close this, possibly with the auxiliary fact
`sq_nonneg (a - b)` or `have h := sq_nonneg (a - b)`.
-/

@[autogradedProof 6]
theorem problem2 (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry
  done


-- ============================================================================
-- Problem 3 (6 points): `positivity` and `push_cast`
-- ============================================================================

/-
For a positive natural number n, the product n · (n + 1) is positive
as a real number.
-/

@[autogradedProof 6]
theorem problem3 (n : ℕ) (hn : 0 < n) :
    (0 : ℝ) < (↑n) * (↑n + 1) := by
  sorry
  done


-- ============================================================================
-- Problem 4 (7 points): No smallest positive real (variant)
-- ============================================================================

/-
For every ε > 0, there exists δ > 0 with δ < ε and δ < 1.
This witnesses that the set of positive reals smaller than both
ε and 1 is always nonempty.

Hint: Consider δ = min(ε, 1) / 2, or split into cases on whether
ε < 1 or 1 ≤ ε.
-/

@[autogradedProof 7]
theorem problem4 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < 1 := by
  sorry
  done


-- ============================================================================
-- Problem 5 (8 points): Floor sub-additivity
-- ============================================================================

/-
The floor function is sub-additive: `⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋`.

Intuitively, rounding each summand down individually loses more
than rounding the sum down once.
-/

#check Int.floor_le

@[autogradedProof 8]
theorem problem5 (x y : ℝ) : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := by
  sorry
  done


-- ============================================================================
-- Problem 6 (10 points): Two rationals between any two reals
-- ============================================================================

/-
Between any two distinct reals there are (at least) two distinct
rationals.  This strengthens the density theorem from Lecture 21.

Hint: Apply `exists_rat_btwn` twice — first to (a, b), obtaining
some q₁, then to (q₁, b) or (a, q₁) to get q₂.
-/

@[autogradedProof 10]
theorem problem6 (a b : ℝ) (hab : a < b) :
    ∃ q₁ q₂ : ℚ, a < ↑q₁ ∧ (↑q₁ : ℝ) < ↑q₂ ∧ (↑q₂ : ℝ) < b := by
  sorry
  done


-- ============================================================================
-- Problem 7 (8 points): Irrationals between rationals
-- ============================================================================

/- Between any two distinct rationals there is an irrational via `sqrt 2`.  (5 points)

**Suggested Strategy**: Shift the interval by `√2`. Apply density
of `ℚ` (via `exists_rat_btwn`) to the shifted interval
`(↑p − √2, ↑q − √2)` to find a rational `r` in it. Then
`z = ↑r + √2` is irrational by part (a) and lies in `(↑p, ↑q)`
by arithmetic.

Useful Mathlib facts:
 - `irrational_sqrt_two : Irrational (Real.sqrt 2)`
 - `Irrational.ratCast_add : Irrational x → Irrational (↑q + x)`
 - `exists_rat_btwn : a < b → ∃ q : ℚ, a < ↑q ∧ ↑q < b`
-/

@[autogradedProof 8]
theorem problem8 (p q : ℚ) (h : p < q) :
    ∃ z : ℝ, (↑p : ℝ) < z ∧ z < ↑q ∧ Irrational z := by
  sorry
  done
