import MIL.Common
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

/- # Lecture 24: Sequences, Limits, and the Squeeze Theorem

New concepts: **`ConvergesTo`, eventual tail control, basic limit algebra**
New Mathlib API: **`exists_nat_one_div_lt`, `abs_add_le`, `le_max_left`, `le_max_right`, `abs_sub_comm`, `abs_lt`, `max_le_iff`**
Recall: **`linarith`, `nlinarith`, `positivity`, `push_cast`, `field_simp`, `obtain`, `have`, `exact_mod_cast`**
-/

-- ============================================================================
-- ## Part 1: Sequences and Convergence
-- ============================================================================

/-
A sequence of real numbers is simply a function `ℕ → ℝ`.

Three examples to keep in mind:

  `n ↦ 1 / (n + 1)` tends to `0`.
  `n ↦ (-1)^n` oscillates.
  `n ↦ n / (n + 1)` approaches `1` from below.

We define convergence directly.  The condition says that for every tolerance
`ε > 0`, eventually all terms of the sequence lie within `ε` of the limit.
-/

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

/-
Mathlib also has a more general *filter*-based notion of convergence.
For now, the direct epsilon-N definition keeps the mathematics visible.
-/

theorem const_converges (c : ℝ) : ConvergesTo (fun _ => c) c := by
  intro ε hε
  use 0
  intro n hn
  simp [hε]

/-
The first genuinely analytic example is the sequence `1 / (n + 1)`.

Lecture 21 already prepared the key Archimedean estimate: for every `ε > 0`,
some reciprocal `1 / (N + 1)` is smaller than `ε`.
-/

#check exists_nat_one_div_lt
-- For every `ε > 0`, some natural number has reciprocal less than `ε`.

theorem one_div_succ_converges : ConvergesTo (fun n => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use N
  intro n hn
  rw [sub_zero, abs_of_nonneg]
  · have hcast : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast add_le_add_right hn 1
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      exact one_div_le_one_div_of_le hpos hcast
    exact lt_of_le_of_lt hle hN
  · positivity

-- Shifting the denominator by a fixed amount does not change the
-- convergence behavior.
example : ConvergesTo (fun n => 1 / ((n : ℝ) + 5)) 0 := by
  sorry

-- ============================================================================
-- ## Part 2: Uniqueness of Limits
-- ============================================================================

/-
If a sequence converged to two different numbers `L` and `M`, then far enough
out it would have to lie close to both at once.  That is impossible if `L ≠ M`.

The key pattern is already important:

 if one argument gives a threshold `N₁` and another gives `N₂`, then
 `max N₁ N₂` works for both simultaneously.
-/

#check abs_add_le
-- Triangle inequality: `|x + y| ≤ |x| + |y|`.

#check le_max_left
#check le_max_right
-- `max N₁ N₂` is large enough for both thresholds at once.

#check abs_sub_comm
-- Swaps the order inside an absolute value.

theorem limit_unique (a : ℕ → ℝ) (L M : ℝ)
    (hL : ConvergesTo a L) (hM : ConvergesTo a M) : L = M := by
  by_contra h
  have hε : 0 < |L - M| / 2 := by
    have hdist : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr h)
    positivity
  obtain ⟨N₁, hN₁⟩ := hL _ hε
  obtain ⟨N₂, hN₂⟩ := hM _ hε
  let k := max N₁ N₂
  have h1 := hN₁ k (le_max_left N₁ N₂)
  have h2 := hN₂ k (le_max_right N₁ N₂)
  have htri : |L - M| ≤ |L - a k| + |a k - M| := by
    have hdecomp : L - M = (L - a k) + (a k - M) := by ring
    calc
      |L - M| = |(L - a k) + (a k - M)| := by rw [hdecomp]
      _ ≤ |L - a k| + |a k - M| := abs_add_le _ _
  rw [abs_sub_comm L (a k)] at htri
  linarith

-- A first direct use of uniqueness.
example (a : ℕ → ℝ) (L : ℝ)
    (h0 : ConvergesTo a 0) (hL : ConvergesTo a L) : L = 0 := by
  sorry


-- ============================================================================
-- ## Part 3: The Squeeze Theorem
-- ============================================================================

/-
This theorem turns order information into convergence.

If `x n ≤ a n ≤ y n` for every `n`, and both outer sequences converge to the
same limit `L`, then the middle sequence must converge to `L` as well.

The picture is simple: once both outer sequences are trapped inside the strip
`(L - ε, L + ε)`, the middle sequence is trapped there too.
-/

#check abs_lt
-- `|x| < ε` turns into a two-sided inequality.

#check max_le_iff
-- `max N₁ N₂ ≤ n` means both `N₁ ≤ n` and `N₂ ≤ n`.

theorem squeeze_theorem (x a y : ℕ → ℝ) (L : ℝ)
    (hlo : ∀ n, x n ≤ a n) (hhi : ∀ n, a n ≤ y n)
    (hx : ConvergesTo x L) (hy : ConvergesTo y L) :
    ConvergesTo a L := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hx ε hε
  obtain ⟨N₂, hN₂⟩ := hy ε hε
  use max N₁ N₂
  intro n hn
  rw [abs_lt]
  obtain ⟨hn₁, hn₂⟩ := max_le_iff.mp hn
  have h1 := hN₁ n hn₁
  have h2 := hN₂ n hn₂
  rw [abs_lt] at h1 h2
  constructor
  · linarith [hlo n, h1.1]
  · linarith [hhi n, h2.2]

-- A first direct use of squeeze.
example (a : ℕ → ℝ) (h : ∀ n, |a n| ≤ 1 / ((n : ℝ) + 1)) :
    ConvergesTo a 0 := by
  sorry


-- ============================================================================
-- ## Part 4: Basic Limit Algebra
-- ============================================================================

theorem add_const_converges (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a n + c) (L + c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  have h := hN n hn
  have hEq : (a n + c) - (L + c) = a n - L := by ring
  rw [hEq]
  exact h

theorem neg_converges (a : ℕ → ℝ) (L : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => -a n) (-L) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  have h := hN n hn
  have hEq : (-a n) - (-L) = -(a n - L) := by ring
  rw [hEq, abs_neg]
  exact h

theorem mul_const_converges (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => c * a n) (c * L) := by
  by_cases hc : c = 0
  · intro ε hε
    use 0
    intro n hn
    simp [hc, hε]
  · intro ε hε
    have hcabs : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := ha (ε / |c|) (div_pos hε hcabs)
    use N
    intro n hn
    have h := hN n hn
    have hEq : (c * a n) - c * L = c * (a n - L) := by ring
    rw [hEq, abs_mul]
    have hmul : |c| * |a n - L| < |c| * (ε / |c|) := by
      gcongr
    have hcabs_ne : |c| ≠ 0 := ne_of_gt hcabs
    have hEq' : |c| * (ε / |c|) = ε := by
      field_simp [hcabs_ne]
    simpa [hEq'] using hmul

theorem tail_converges (a : ℕ → ℝ) (L : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a (n + 1)) L := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  exact hN (n + 1) (Nat.le_trans hn (Nat.le_succ n))


-- ============================================================================
-- ## Part 5: One Clean Application
-- ============================================================================

/-
The sequence `n / (n + 1)` is a first example of a nontrivial limit computed by
rewriting it into a familiar form:

  `n / (n + 1) = 1 - 1 / (n + 1)`.

So it differs from `1` by the same small error term we already understand.
-/

example : ConvergesTo (fun n => (n : ℝ) / ((n : ℝ) + 1)) 1 := by
  have hneg : ConvergesTo (fun n => -(1 / ((n : ℝ) + 1))) 0 := by
    simpa using neg_converges (fun n => 1 / ((n : ℝ) + 1)) 0 one_div_succ_converges
  have hadd : ConvergesTo (fun n => -(1 / ((n : ℝ) + 1)) + 1) 1 := by
    simpa using add_const_converges (fun n => -(1 / ((n : ℝ) + 1))) 0 1 hneg
  intro ε hε
  obtain ⟨N, hN⟩ := hadd ε hε
  use N
  intro n hn
  have h := hN n hn
  have hEq : (n : ℝ) / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) + 1 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp [ne_of_gt hpos]
  simpa [hEq] using h


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/-
Warm-up
-/

example (a : ℕ → ℝ) (L c : ℝ) (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a n + c) (L + c) := by
  sorry

example (a : ℕ → ℝ) (L : ℝ) (ha : ConvergesTo a L) :
    ConvergesTo (fun n => -a n) (-L) := by
  sorry

example (a : ℕ → ℝ) (L : ℝ) (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a (n + 1)) L := by
  sorry

/-
Core
-/

example : ConvergesTo (fun n => (-1 : ℝ) ^ n / ((n : ℝ) + 1)) 0 := by
  sorry

/-
Challenging
-/

example (a b : ℕ → ℝ) (L M : ℝ)
    (ha : ConvergesTo a L) (hb : ConvergesTo b M) :
    ConvergesTo (fun n => a n + b n) (L + M) := by
  sorry

example (a : ℕ → ℝ) (h : ∀ n, |a n| ≤ (1 / 2 : ℝ) ^ n) :
    ConvergesTo a 0 := by
  sorry
