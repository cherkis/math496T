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

does converge, and we can prove it without ever solving the recurrence.
First, monotonicity and boundedness give existence of the limit.
Then the recurrence itself forces the value of that limit.
This is a good example of how structural theorems can replace explicit calculation.
-/


/-
Recall the ε-approximation theorem for suprema,
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
-- ## Part 1: Monotone Sequences
-- ============================================================================

/-
A sequence is *monotone increasing* if later terms are always at least as large
as earlier ones.
It is *monotone decreasing* if later terms are always at most as large.

In practice, for sequences indexed by `ℕ`, it is often enough to compare
adjacent terms.
-/

#check @Monotone ℕ ℝ _ _ -- ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
#check @Antitone ℕ ℝ _ _ -- ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

#check monotone_nat_of_le_succ
-- To prove a sequence is increasing, it is enough to compare adjacent terms.

#check antitone_nat_of_succ_le --  ∀ (n : ℕ), f n ≤ f (n + 1)) → Monotone f
-- Similarly for decreasing sequences.

example : Monotone (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) := by
  apply monotone_nat_of_le_succ
  intro n
  push_cast
  rw [div_le_div_iff₀]
  nlinarith <;> positivity

example : Antitone (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  push_cast
  simp
  apply inv_anti₀ -- NB
  positivity


-- The same decreasing-tail argument also shows the sequence is bounded below by
-- its constant term.
example : ∀ n, (1 : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) := by
  sorry


-- ============================================================================
-- ## Part 2: Why Both Hypotheses Matter
-- ============================================================================

/-
The Monotone Convergence Theorem needs both monotonicity and boundedness.
`a n = n` is monotone increasing but unbounded, so it cannot converge.
`a n = (-1)^n` is bounded but not monotone, and it does not converge either.
-/

/-
Let `L = sSup (Set.range a)`.
*Completeness* says that for every `ε > 0`,
some term of the sequence lies above `L - ε`.
*Monotonicity* then pushes all later terms above `L - ε`.
Since every term is at most `L`, the
tail of the sequence lies inside the interval `(L - ε, L]`.
-/

#check exists_between_sup_minus_eps -- : ∃ x ∈ S, sSup S - ε < x
-- (S : Set ℝ) (hS : S.Nonempty) (_hB : BddAbove S) (ε : ℝ) (hε : 0 < ε) :  ∃ x ∈ S, sSup S - ε < x
-- If `ε > 0`, some element of the set lies above `sSup - ε`.

#check le_csSup -- a ∈ s) → a ≤ sSup s
-- Every element of the set is at most the supremum.

#check abs_of_nonpos -- (h : a ≤ 0) : |a| = -a
#check sub_nonpos --  a - b ≤ 0 ↔ a ≤ b
-- These rewrite `|a n - L|` as `L - a n` once we know `a n ≤ L`.

theorem monotone_convergence (a : ℕ → ℝ)
    (hmon : Monotone a) (hbdd : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) := by
  intro ε hε
  obtain ⟨x,hx,hxsup⟩ := exists_between_sup_minus_eps (Set.range a)  ?_ hbdd ε hε
  obtain ⟨N,hN⟩ := hx
  use N
  intro n hn
  rw [abs_of_nonpos,neg_sub]
  have hnN : a N ≤ a n := by apply hmon hn
  linarith
  simp [le_csSup hbdd]

-- A first direct consequence of monotone convergence ideas.
-- If you wish, you can add a boundedness assumption, but it is not necessary here
example (a : ℕ → ℝ) (L : ℝ) (hmon : Monotone a) (ha : ConvergesTo a L) :
    ∀ n, a n ≤ L := by
  sorry


-- ============================================================================
-- ## Part 3: Recall from Lecture 24
-- ============================================================================

/-
To identify the limit of a recursive sequence, it helps to know that convergence
is preserved by simple algebraic operations and by shifting the index.

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

-- `lim (aₙ + c) = (lim aₙ) + c`
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

-- `lim (c*aₙ) = c* lim aₙ`
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

-- `lim aₙ₊₁ = lim aₙ`
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


-- ============================================================================
-- ## Part 4: A Recursive Sequence
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

-- The induction also shows all terms are nonnegative.
example : ∀ n, 0 ≤ seq n := by
  sorry

lemma seq_monotone : Monotone seq := by
  apply monotone_nat_of_le_succ
  intro n
  simp [seq]
  linarith [seq_lt_one n]

theorem seq_converges : ConvergesTo seq (sSup (Set.range seq)) := by
  apply monotone_convergence seq seq_monotone
  use 1
  intro a ⟨n,hn⟩
  apply le_of_lt
  rw [←hn]
  apply seq_lt_one

/-
The point of the recurrence is that it lets us identify the limit.
If the sequence converges to `s`, then the shifted sequence `seq (n + 1)` converges to the same `s`.

But the recurrence also says that `seq (n + 1)` is obtained from `seq n`
by the transformation `x ↦ (x + 2) / 3`, so its limit *if it exists*
must also be `(s + 2) / 3`.
Uniqueness of limits then forces `s = (s + 2) / 3`, hence `s = 1`.
-/

theorem seq_limit_eq_one : sSup (Set.range seq) = 1 := by
  let s : ℝ := sSup (Set.range seq)
  -- lim seqₙ = s
  have hsconv : ConvergesTo seq s := by apply seq_converges
  -- lim seqₙ₊₁ = s
  have hshift : ConvergesTo (fun n => seq (n + 1)) s := tail_converges seq s hsconv
  -- lim (seqₙ + 2) = s + 2
  have hadd : ConvergesTo (fun n => seq n + 2) (s + 2) := add_const_converges seq s 2 hsconv
  -- lim ((seqₙ + 2)/3) = (s+2) / 3
  have hmul : ConvergesTo (fun n => (1 / 3 : ℝ) * (seq n + 2)) ((1 / 3 : ℝ) * (s + 2)) := mul_const_converges (fun n => seq n + 2) (s + 2) (1 / 3) hadd
  -- lim ((seqₙ₊₁ + 2)/3) = (s+2) / 3
  have hrec : ConvergesTo (fun n => seq (n + 1)) ((1 / 3 : ℝ) * (s + 2)) := by
    have hEq : (fun n => seq (n + 1)) = (fun n => (1 / 3 : ℝ) * (seq n + 2)) := by
      funext n
      simp [seq] --, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      linarith
    rw [hEq]
    exact hmul
  -- s = (s+2) / 3
  have hfix : s = (1 / 3 : ℝ) * (s + 2) := limit_unique (fun n => seq (n + 1)) s ((1 / 3 : ℝ) * (s + 2)) hshift hrec
  -- s=1
  linarith


-- ============================================================================
-- ## Addendum: Cauchy Sequences
-- ============================================================================

/-
A Cauchy sequence is one all of whose terms eventually become close to each other.

This is a different way of describing the idea that a sequence is settling down.
In `ℝ`, the two notions are equivalent: a sequence converges if and only
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
