import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.Basic

/- # Lecture 26: Open Sets, Closed Sets, and Closure

New concepts: **`IsOpenSet`, `IsClosedSet`, accumulation points, `IsClosurePt`, sequential characterization of closure**
New Mathlib API: **`min_le_left`, `min_le_right`, `lt_min_iff`, `abs_of_neg`, `Metric.isOpen_iff`**
New tactics: **`lt_or_ge` (three-way sign split for reals), `subst` (substitutes an equality hypothesis into the goal)**
Recall: **`exists_nat_one_div_lt` (L21), `exists_rat_btwn` (L21), density of `ℚ` in `ℝ` (L21), `ConvergesTo` (L24), `abs_lt`, `abs_sub_comm` (L20, L24), `abs_of_nonneg`, `sub_ne_zero`, `abs_pos` (L24), `choose` (L14)**

## Overview

So far all of our analysis has been *pointwise*: a sequence converges to a
specific point, a supremum is approximated by a specific element, and so on.
Today we take the step into **topology**, where the primitive notion is a
*set* of points — open, closed, or accumulated around a limit.

Three facts will drive the lecture:

 1. An open interval is open and a closed interval is closed.  This is
    the familiar case; the content is in the *definitions* that capture
    these words uniformly.
 2. Infinite intersections can destroy openness.  The intersection
    `⋂ₙ (−1/(n+1), 1/(n+1))` is just `{0}`.  The Archimedean estimate
    from L21 is what forces every non-zero `x` out of that intersection.
 3. Every real number is the limit of a sequence of rationals.  This
    reframes the density of `ℚ` in `ℝ` as a statement about *closure*.
-/

-- ============================================================================
-- ## Part 1: ε-neighborhoods and open sets
-- ============================================================================

/-
An **ε-neighborhood** of `x` is the set of real numbers within distance `ε`
of `x`.  A set `U ⊆ ℝ` is **open** if every point of `U` has some
ε-neighborhood entirely inside `U`.  The number `ε` is allowed to depend on
the point.
-/

def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

/-
The open interval `(a, b)` is open.  For `x ∈ (a, b)` we use
`ε = min (x − a) (b − x)`: a tolerance that fits between `x` and each
endpoint.
-/

example (a b : ℝ) : IsOpenSet (Set.Ioo a b) := by
  intro x hx
  obtain ⟨ha, hb⟩ := hx
  use min (x - a) (b - x)
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  intro y hy
  rw [abs_lt] at hy
  constructor
  · linarith [min_le_left (x - a) (b - x)]
  · linarith [min_le_right (x - a) (b - x)]

example : IsOpenSet (∅ : Set ℝ) := by
  intro x hx
  exact hx.elim

example : IsOpenSet (Set.univ : Set ℝ) := by
  intro x _
  use 1
  constructor
  · norm_num
  · intro _ _
    trivial

#check @Metric.isOpen_iff
-- Mathlib's general `IsOpen` on `ℝ` agrees with our concrete `IsOpenSet`
-- through this lemma.  We will not use it; it is here to show that our
-- freshman definition lines up with the library.

-- **Practice (in-body)**: the ray `(a, ∞)` is open.
example (a : ℝ) : IsOpenSet (Set.Ioi a) := by
  sorry


-- ============================================================================
-- ## Part 2: Closed sets
-- ============================================================================

/-
A set `F ⊆ ℝ` is **closed** if its complement is open.  This is the standard
topological definition; sequential characterizations follow in Part 4.
-/

def IsClosedSet (F : Set ℝ) : Prop := IsOpenSet Fᶜ

example (a b : ℝ) : IsClosedSet (Set.Icc a b) := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · use a - x, by linarith
    intro y hy
    rw [abs_lt] at hy
    rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le]
    left; linarith
  · use x - b, by linarith
    intro y hy
    rw [abs_lt] at hy
    rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le]
    right; linarith

example (a : ℝ) : IsClosedSet ({a} : Set ℝ) := by
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  use |x - a|, abs_pos.mpr (sub_ne_zero.mpr hx)
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  subst heq
  rw [abs_sub_comm] at hy
  linarith

/-
**Main example (an interesting fact)**.  The infinite descending
intersection `⋂ₙ (−1/(n+1), 1/(n+1))` equals `{0}`.

The `⊆` direction is the substantive one: if `x ≠ 0`, the Archimedean
estimate of L21 gives an `N` with `1/(N+1) < |x|`, which kicks `x` out of
the `N`-th open interval.  Passing to infinite intersections turns open
sets into a *closed* singleton.
-/

example : (⋂ n : ℕ, Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) = {0} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (abs_pos.mpr hx)
    -- `hN : 1/(N+1) < |x|`.  Case-split on the sign of `x` using `lt_or_ge`.
    obtain ⟨h1, h2⟩ := h N
    rcases lt_or_ge x 0 with hxneg | hxpos
    · rw [abs_of_neg hxneg] at hN; linarith
    · rw [abs_of_nonneg hxpos] at hN; linarith
  · intro hx n
    subst hx
    rw [neg_lt_iff_pos_add, zero_add, and_self]
    positivity

-- **Practice (in-body)**: the union of two closed sets is closed.
example (F G : Set ℝ) (hF : IsClosedSet F) (hG : IsClosedSet G) :
    IsClosedSet (F ∪ G) := by
  sorry


-- ============================================================================
-- ## Part 3: Accumulation points and closure points
-- ============================================================================

/-
An **accumulation point** of `S` is a point with points of `S` other than
itself arbitrarily close.  A **closure point** is allowed to coincide with
a point of `S`; every member of `S` is automatically a closure point.
-/

def IsAccPt (x : ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ S, y ≠ x ∧ |y - x| < ε

def IsClosurePt (x : ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ S, |y - x| < ε

-- `0` is an accumulation point of `{1/(n+1) | n : ℕ}`, yet `0` itself is
-- not a member of the set.
example : IsAccPt 0 {x : ℝ | ∃ n : ℕ, x = 1 / ((n : ℝ) + 1)} := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  use 1 / ((N : ℝ) + 1), ⟨N, rfl⟩
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  refine ⟨fun h => ?_, ?_⟩
  · linarith
  · rw [sub_zero, abs_of_pos hpos]; exact hN

-- **Practice (in-body)**: every element of `S` is a closure point of `S`.
example (S : Set ℝ) (x : ℝ) (hx : x ∈ S) : IsClosurePt x S := by
  sorry


-- ============================================================================
-- ## Part 4: Sequential characterization of closure (climax)
-- ============================================================================

/-
We use the `ConvergesTo` definition from L24.  A closure point is exactly
the limit of a sequence drawn from `S`.  The forward direction builds the
approximating sequence using the `1/(n+1)` tolerance; the reverse is
immediate by taking `N` large.
-/

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

theorem isClosurePt_iff_exists_seq (x : ℝ) (S : Set ℝ) :
    IsClosurePt x S ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ S) ∧ ConvergesTo a x := by
  constructor
  · intro h
    -- `choose` turns a pointwise ∃-statement into a function + its witness.
    choose a ha using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
    use a, fun n => (ha n).1
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    linarith [(ha n).2, hN]
  · rintro ⟨a, haS, hconv⟩ ε hε
    obtain ⟨N, hN⟩ := hconv ε hε
    use a N, haS N
    exact hN N le_rfl


-- ============================================================================
-- ## Part 5: Closure of ℚ in ℝ is ℝ
-- ============================================================================

/-
The density theorem from L21 says between any two reals there is a rational.
Recast as a closure statement: every real is a closure point of the set of
rationals embedded into `ℝ`.  Every real is a limit of a sequence of
rationals — the analyst's working form of "ℝ is the completion of ℚ."
-/

example (x : ℝ) : IsClosurePt x (Set.range ((↑) : ℚ → ℝ)) := by
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x + ε by linarith)
  use (q : ℝ), ⟨q, rfl⟩
  rw [abs_lt]
  constructor <;> linarith


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/- Warm-up -/

example (U V : Set ℝ) (hU : IsOpenSet U) (hV : IsOpenSet V) :
    IsOpenSet (U ∪ V) := by
  sorry

example : IsClosedSet (Set.univ : Set ℝ) := by
  sorry

/- Core -/

example (n : ℕ) : IsOpenSet (Set.Iio (1 + 1 / ((n : ℝ) + 1))) := by
  sorry

example : IsClosedSet (⋂ n : ℕ, Set.Iio (1 + 1 / ((n : ℝ) + 1)) ) := by
  sorry

example (U V : Set ℝ) (hU : IsOpenSet U) (hV : IsOpenSet V) :
    IsOpenSet (U ∩ V) := by
  sorry

/- Challenging -/

example (F : Set ℝ) :
    IsClosedSet F ↔
      ∀ a : ℕ → ℝ, (∀ n, a n ∈ F) → ∀ L, ConvergesTo a L → L ∈ F := by
  sorry
