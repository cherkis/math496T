-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Ring.Parity

--! # Homework 10: Sequences and Limits

/-!
This homework covers Lectures 24-25.

Topics: epsilon-N convergence of sequences; divergence; order preservation
in limits; the Monotone Convergence Theorem; recursive sequences.

**Total: 5 problems, 50 points.**
-/


def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε


-- ============================================================================
-- Problem 1 (6 points): A first epsilon-N proof
-- ============================================================================

/-
Prove that `1 / (2n + 1)` converges to `0`.
-/

#check exists_nat_one_div_lt
#check one_div_le_one_div_of_le

@[autogradedProof 6]
theorem problem1 : ConvergesTo (fun n => 1 / ((2 : ℝ) * n + 1)) 0 := by
  sorry
  done


-- ============================================================================
-- Problem 2 (8 points): Order is preserved in the limit
-- ============================================================================

/-
If every term of a convergent sequence is at most `c`, then the limit is also
at most `c`.
-/

@[autogradedProof 8]
theorem problem2 (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) (hc : ∀ n, a n ≤ c) : L ≤ c := by
  sorry
  done


-- ============================================================================
-- Problem 3 (10 points): A sequence with no limit
-- ============================================================================

/-
Show that `(-1)^n` does not converge.
-/

#check Even.neg_one_pow
#check Odd.neg_one_pow

@[autogradedProof 10]
theorem problem3 : ¬ ∃ L : ℝ, ConvergesTo (fun n => (-1 : ℝ) ^ n) L := by
  sorry
  done


-- ============================================================================
-- Limit algebra
-- ============================================================================

theorem add_const_converges (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a n + c) (L + c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  simpa [show (a n + c) - (L + c) = a n - L by ring] using hN n hn

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
    have hmul : |c| * |a n - L| < |c| * (ε / |c|) := by gcongr
    have hEq' : |c| * (ε / |c|) = ε := by field_simp [ne_of_gt hcabs]
    linarith


-- ============================================================================
-- Problem 4 (10 points): An algebraic limit
-- ============================================================================

/-
Prove that `n² / (n² + 1) → 1`.
-/

@[autogradedProof 10]
theorem problem4 :
    ConvergesTo (fun n => ((n : ℝ) ^ 2) / (((n : ℝ) ^ 2) + 1)) 1 := by
  sorry
  done


-- ============================================================================
-- Monotone Convergence Theorem and limit identification
-- ============================================================================

theorem monotone_convergence (a : ℕ → ℝ)
    (hmon : Monotone a) (hbdd : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) := by
  intro ε hε
  have ⟨_, ⟨N, rfl⟩, hN⟩ : ∃ x ∈ Set.range a, sSup (Set.range a) - ε < x := by
    by_contra! h
    have hne : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
    linarith [csSup_le hne h]
  use N
  intro n hn
  have hle : a n ≤ sSup (Set.range a) :=
    le_csSup hbdd (Set.mem_range.mpr ⟨n, rfl⟩)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith [hmon hn]

theorem tail_converges (a : ℕ → ℝ) (L : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a (n + 1)) L := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  exact hN (n + 1) (Nat.le_trans hn (Nat.le_succ n))

theorem limit_unique (a : ℕ → ℝ) (L M : ℝ)
    (hL : ConvergesTo a L) (hM : ConvergesTo a M) : L = M := by
  by_contra h
  have hε : 0 < |L - M| / 2 := by
    have : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr h)
    positivity
  obtain ⟨N₁, hN₁⟩ := hL _ hε
  obtain ⟨N₂, hN₂⟩ := hM _ hε
  have h1 := hN₁ (max N₁ N₂) (le_max_left N₁ N₂)
  have h2 := hN₂ (max N₁ N₂) (le_max_right N₁ N₂)
  have htri := abs_add_le (L - a (max N₁ N₂)) (a (max N₁ N₂) - M)
  rw [show (L - a (max N₁ N₂)) + (a (max N₁ N₂) - M) = L - M by ring,
      abs_sub_comm L (a (max N₁ N₂))] at htri
  linarith


-- ============================================================================
-- Problem 5 (16 points): Recursive-sequence capstone
-- ============================================================================

noncomputable def hw_seq : ℕ → ℝ
  | 0 => 0
  | n + 1 => (hw_seq n + 4) / 5

lemma hw_seq_le_one : ∀ n, hw_seq n ≤ 1 := by
  intro n
  induction' n with n ih
  · simp [hw_seq]
  · simp [hw_seq]; linarith

/-
The recursively defined sequence `a₀ = 0`, `aₙ₊₁ = (aₙ + 4) / 5` converges
to `1`.  The bound `hw_seq n ≤ 1` is provided above.
-/

#check monotone_nat_of_le_succ

@[autogradedProof 16]
theorem problem5 : ConvergesTo hw_seq 1 := by
  sorry
  done
