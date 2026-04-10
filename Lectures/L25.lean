import MIL.Common
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 25: Monotone Convergence and Cauchy Sequences

New concepts: **`Monotone`, recursive real sequences, `IsCauchy`**
New Mathlib API: **`monotone_nat_of_le_succ`, `antitone_nat_of_succ_le`, `abs_of_nonpos`, `sub_nonpos`**
Recall: **`exists_between_sup_minus_eps`, `le_csSup`, `csSup_le`, `Set.range`, `induction'`, `linarith`**

## Overview

Today we prove one of the central theorems of elementary analysis:
 *a bounded monotone sequence of real numbers converges*.
This is where completeness of `ℝ` becomes a theorem
about actual functions rather than about abstract sets.

This can be used for a recursively defined sequence whose convergence is
guaranteed by monotonicity and boundedness, without knowing any
explicit formula for its terms.

### An Interesting Fact: Completeness Can Produce a Limit Without a Formula

The sequence

 `a₀ = 0`, `aₙ₊₁ = (aₙ + 2) / 3`

does converge, and we can prove it without ever solving the recurrence. First,
monotonicity and boundedness give existence of the limit. Then the recurrence
itself forces the value of that limit. This is a good example of how structural
theorems can replace explicit calculation.
-/


-- ============================================================================
-- ## Part 1: Two Recalled Definitions
-- ============================================================================

/-
Recall some Lecture 24 convergence facts in epsilon-N language.
And the epsilon-approximation theorem for suprema from Lecture 22,
which is the completeness input behind the Monotone Convergence Theorem.
-/

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

theorem exists_between_sup_minus_eps
    (S : Set ℝ) (hS : S.Nonempty) (_hB : BddAbove S) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  by_contra! h
  have hs : sSup S ≤ sSup S - ε := by
    apply csSup_le hS
    intro x hx
    exact h x hx
  linarith


-- ============================================================================
-- ## Part 2: Monotone Sequences
-- ============================================================================

/-
A sequence is monotone increasing if later terms are always at least as large
as earlier ones. It is monotone decreasing if later terms are always at most as large.

In practice, for sequences indexed by `ℕ`, it is often enough to compare
adjacent terms.
-/

#check @Monotone ℕ ℝ _ _
#check @Antitone ℕ ℝ _ _

#check monotone_nat_of_le_succ
-- To prove a sequence is increasing, it is enough to compare adjacent terms.

#check antitone_nat_of_succ_le
-- Similarly for decreasing sequences.

example : Monotone (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num]
  change (n : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1)
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

example : Antitone (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num]
  change 1 + 1 / ((n : ℝ) + 1 + 1) ≤ 1 + 1 / ((n : ℝ) + 1)
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h12 : (n : ℝ) + 1 ≤ (n : ℝ) + 1 + 1 := by linarith
  have hdiv : 1 / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) := by
    exact one_div_le_one_div_of_le h1 h12
  linarith

-- The same decreasing-tail argument also shows the sequence is bounded below by
-- its constant term.
example : ∀ n, (1 : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) := by
  sorry


-- ============================================================================
-- ## Part 3: Why Both Hypotheses Matter
-- ============================================================================

/-
The Monotone Convergence Theorem needs both monotonicity and boundedness.

`a n = n` is monotone increasing but unbounded, so it cannot converge.
`a n = (-1)^n` is bounded but not monotone, and it does not converge either.

-/


-- ============================================================================
-- ## Part 4: The Monotone Convergence Theorem
-- ============================================================================

/-
Let `L = sSup (Set.range a)`.
The *completeness* move says that for every `ε > 0`,
some term of the sequence lies above `L - ε`.
*Monotonicity* then pushes all later terms above `L - ε`.
Since every term is at most `L`, the
tail of the sequence lies inside the interval `(L - ε, L]`.
-/

#check exists_between_sup_minus_eps
-- If `ε > 0`, some element of the set lies above `sSup - ε`.

#check le_csSup
-- Every element of the set is at most the supremum.

#check abs_of_nonpos
#check sub_nonpos
-- These rewrite `|a n - L|` as `L - a n` once we know `a n ≤ L`.

theorem monotone_convergence (a : ℕ → ℝ)
    (hmon : Monotone a) (hbdd : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) := by
  intro ε hε
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ :=
    exists_between_sup_minus_eps (Set.range a) ⟨a 0, ⟨0, rfl⟩⟩ hbdd ε hε
  use N
  intro n hn
  have hle : a n ≤ sSup (Set.range a) := by
    exact le_csSup hbdd (Set.mem_range.mpr ⟨n, rfl⟩)
  have hlo : sSup (Set.range a) - ε < a n := by
    exact lt_of_lt_of_le hN (hmon hn)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

-- A first direct consequence of monotone convergence ideas.
example (a : ℕ → ℝ) (L : ℝ) (hmon : Monotone a) (ha : ConvergesTo a L) :
    ∀ n, a n ≤ L := by
  sorry


-- ============================================================================
-- ## Part 5: A Short Recall from Lecture 24
-- ============================================================================

/-
To identify the limit of a recursive sequence, it helps to know that convergence
is preserved by simple algebraic operations and by shifting the index.

From Lecture 24:
-/

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

#check tail_converges
#check add_const_converges
#check mul_const_converges
#check limit_unique
-- These are the Lecture 24 tools that let us pass to the limit in a recurrence.


-- ============================================================================
-- ## Part 6: A Recursive Sequence
-- ============================================================================

noncomputable def seq : ℕ → ℝ
  | 0 => 0
  | n + 1 => (seq n + 2) / 3

/-
We first show that the sequence stays below `1`,
then we show that it is monotone increasing.
Once those two ingredients are in place, the
Monotone Convergence Theorem gives convergence.
-/

lemma seq_lt_one : ∀ n, seq n < 1 := by
  intro n
  induction' n with n ih
  · simp [seq]
  · simp [seq]
    linarith

-- The same induction also shows all terms are nonnegative.
example : ∀ n, 0 ≤ seq n := by
  sorry

lemma seq_monotone : Monotone seq := by
  apply monotone_nat_of_le_succ
  intro n
  simp [seq]
  linarith [seq_lt_one n]

theorem seq_converges : ConvergesTo seq (sSup (Set.range seq)) := by
  apply monotone_convergence
  · exact seq_monotone
  · refine ⟨1, ?_⟩
    rintro x ⟨n, rfl⟩
    exact le_of_lt (seq_lt_one n)

/-
The point of the recurrence is that it lets us identify the limit. If the
sequence converges to `s`, then the shifted sequence `seq (n + 1)` converges to
the same `s`.

But the recurrence also says that `seq (n + 1)` is obtained from
`seq n` by the transformation `x ↦ (x + 2) / 3`, so its limit *if it exists*
must also be `(s + 2) / 3`.
Uniqueness of limits then forces `s = (s + 2) / 3`, hence `s = 1`.
-/

theorem seq_limit_eq_one : sSup (Set.range seq) = 1 := by
  let s : ℝ := sSup (Set.range seq)
  have hsconv : ConvergesTo seq s := by
    simpa [s] using seq_converges
  have hshift : ConvergesTo (fun n => seq (n + 1)) s := by
    exact tail_converges seq s hsconv
  have hadd : ConvergesTo (fun n => seq n + 2) (s + 2) := by
    exact add_const_converges seq s 2 hsconv
  have hmul : ConvergesTo (fun n => (1 / 3 : ℝ) * (seq n + 2)) ((1 / 3 : ℝ) * (s + 2)) := by
    exact mul_const_converges (fun n => seq n + 2) (s + 2) (1 / 3) hadd
  have hrec : ConvergesTo (fun n => seq (n + 1)) ((1 / 3 : ℝ) * (s + 2)) := by
    have hEq : (fun n => seq (n + 1)) = (fun n => (1 / 3 : ℝ) * (seq n + 2)) := by
      funext n
      simp [seq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    rw [hEq]
    exact hmul
  have hfix : s = (1 / 3 : ℝ) * (s + 2) := by
    exact limit_unique (fun n => seq (n + 1)) s ((1 / 3 : ℝ) * (s + 2)) hshift hrec
  linarith


-- ============================================================================
-- ## Addendum: Cauchy Sequences
-- ============================================================================

/-
A Cauchy sequence is one whose terms eventually become close to each other.

This is a different way of describing the idea that a sequence is settling
down. In `ℝ`, the two notions are equivalent: a sequence converges if and only
if it is Cauchy.

The forward direction is a triangle-inequality argument. The reverse direction
is another form of completeness.
-/

def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n → |a m - a n| < ε


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/-
Warm-up
-/

example : Monotone (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2)) := by
  sorry

example : Antitone (fun n : ℕ => 2 + 1 / ((n : ℝ) + 1)) ∧
    (∀ n, (2 : ℝ) ≤ 2 + 1 / ((n : ℝ) + 1)) := by
  sorry

/-
Core
-/

example (a : ℕ → ℝ) (hanti : Antitone a) (hbdd : BddBelow (Set.range a)) :
    ConvergesTo a (sInf (Set.range a)) := by
  sorry

example : ConvergesTo (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2))
    (sSup (Set.range (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2)))) := by
  sorry

/-
Challenging
-/

noncomputable def seq' : ℕ → ℝ
  | 0 => 0
  | n + 1 => (seq' n + 4) / 5

example : ConvergesTo seq' (sSup (Set.range seq')) ∧ sSup (Set.range seq') = 1 := by
  sorry

example (a b : ℕ → ℝ)
    (ha : Monotone a) (hb : Antitone b)
    (hsep : ∀ n, a n ≤ b n)
    (hba : BddAbove (Set.range a)) (hbb : BddBelow (Set.range b)) :
    sSup (Set.range a) ≤ sInf (Set.range b) := by
  sorry
