import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 29: Compactness Characterizations, EVT Completed, and the Finale

New tactic: **simp_rw**
New concepts: **Minimum half of EVT, `seqCompact_bounded`, `seqCompact_closed`, sequential Heine–Borel, the Cantor intersection theorem (course finale)**
New Mathlib API: **`Finset.sup'`, `Finset.le_sup'`, `Finset.nonempty_range_succ`, `Nat.lt_succ_iff`**

Recall: **`IsSeqCompact`, Bolzano–Weierstrass, max half of EVT (L28), `IsClosedSet` (L26), `limit_unique` (L24), `choose` (L14), `Set.mem_iInter` (L11), `abs_le` (L20), `Nat.zero_le` (L17), `induction` (L07), `let` (L04)**

## Overview

Today we complete the mathematical core of this course.  Three tasks:

 1. Complete EVT: the minimum half follows from the max half by a sign
    flip.
 2. Show that sequential compactness is *equivalent to* "closed and bounded"
    for subsets of `ℝ`.  This is the sequential form of the Heine–Borel
    theorem.
 3. Prove the **Cantor intersection theorem**: a descending sequence of
    nonempty sequentially compact subsets of `ℝ` has a nonempty
    intersection.  This is the course's closing statement — it synthesizes
    completeness, compactness, and closedness into a single theorem.

The connecting thread: once compactness captures "closed + bounded", the
machinery we developed produces existence theorems almost for free.
-/

namespace L29

def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

def IsClosedSet (F : Set ℝ) : Prop := IsOpenSet Fᶜ

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

def ContinuousAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

def IsSeqCompact (K : Set ℝ) : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, a n ∈ K) →
    ∃ (s : ℕ → ℕ) (x : ℝ), x ∈ K ∧ StrictMono s ∧
      ConvergesTo (fun n => a (s n)) x

/-- Uniqueness of limits (from L24), restated locally. -/
private theorem limit_unique (a : ℕ → ℝ) (L M : ℝ)
    (hL : ConvergesTo a L) (hM : ConvergesTo a M) : L = M := by
  -- choose ε = |L - M| / 2
  -- use both limits at same ε
  -- triangle inequality at max NL NM
  sorry



/-- Provided (proved in L28 Part 4): the maximum half of EVT. -/
private axiom evt_max {K : Set ℝ} (hK : IsSeqCompact K) (hKne : K.Nonempty)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c) :
    ∃ xmax ∈ K, ∀ x ∈ K, f x ≤ f xmax

/-- Provided (proved in L28 Part 3): Bolzano–Weierstrass. -/
private axiom bolzano_weierstrass (A B : ℝ) (hAB : A ≤ B) :
    IsSeqCompact (Set.Icc A B)


-- ============================================================================
-- ## Part 1: Minimum half of EVT
-- ============================================================================

/-
The minimum half is a one-line consequence of the max half applied to `−f`.
-/

theorem evt_min {K : Set ℝ} (hK : IsSeqCompact K) (hKne : K.Nonempty)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c) :
    ∃ xmin ∈ K, ∀ x ∈ K, f xmin ≤ f x := by
  sorry


-- ============================================================================
-- ## Part 2: Sequentially compact ⟹ bounded
-- ============================================================================

/-
A sequentially compact set in `ℝ` is bounded.  Idea: if it is not, pick
`xₙ` with `|xₙ| ≥ n`, but then no subsequence of `xₙ` can converge
(convergent sequences are bounded).
-/

/-- Convergent sequences are bounded. -/
private lemma bounded_of_convergesTo {a : ℕ → ℝ} {L : ℝ}
    (h : ConvergesTo a L) : ∃ M, ∀ n, |a n| ≤ M := by
  -- After index `N` we have `|aₙ − L| < 1`, hence `|aₙ| ≤ |L| + 1`.
  -- For indices `≤ N` we take the max of finitely many `|a k|`.
  sorry

theorem seqCompact_bounded {K : Set ℝ} (hK : IsSeqCompact K) :
    ∃ M, ∀ x ∈ K, |x| ≤ M := by
  -- For each n, pick xₙ ∈ K with |xₙ| > n.
  sorry



-- ============================================================================
-- ## Part 3: Sequentially compact ⟹ closed
-- ============================================================================

/-
A sequentially compact set in `ℝ` is closed:
if a sequence in `K` converges to `x`,
seq-compactness provides a subsequence converging to *some* `y ∈ K`;
but that subsequence also converges to `x`, so `x = y ∈ K`.
-/

/-- A subsequence of a convergent sequence converges to the same limit. -/
private lemma subseq_conv {a : ℕ → ℝ} {x : ℝ} (h : ConvergesTo a x)
    {s : ℕ → ℕ} (hs : StrictMono s) : ConvergesTo (fun n => a (s n)) x := by
  sorry

theorem seqCompact_closed {K : Set ℝ} (hK : IsSeqCompact K) :
    IsClosedSet K := by
  -- For each n : ℕ, pick yₙ ∈ K with |yₙ − x| < 1/(n+1).
  sorry

-- ============================================================================
-- ## Part 4: Sequential Heine–Borel
-- ============================================================================

/-
`K ⊆ ℝ` is sequentially compact iff it is closed and bounded.  The forward
direction is Parts 2 and 3; the backward direction uses Bolzano–Weierstrass
inside `[−M, M]`.
-/

theorem heine_borel_seq (K : Set ℝ) :
    IsSeqCompact K ↔ IsClosedSet K ∧ ∃ M, ∀ x ∈ K, |x| ≤ M := by
  sorry


-- ============================================================================
-- ## Part 5: Course finale — Cantor intersection theorem
-- ============================================================================

/-
**Finale.**  If `(K n)` is a descending sequence of nonempty sequentially
compact subsets of `ℝ`, then `⋂ n, K n` is nonempty.

This theorem closes our main mathematical arc:
completeness of `ℝ` (via Bolzano–Weierstrass),
sequences, closedness, and compactness all enter together.
Cantor intersection is the reason
- a Dedekind cut,
- a nested-intervals witness, and
- a limit of a Cauchy sequence
all refer to the *same* kind of real number.
-/

theorem cantor_intersection (K : ℕ → Set ℝ)
    (hne : ∀ n, (K n).Nonempty)
    (hcompact : ∀ n, IsSeqCompact (K n))
    (hdesc : ∀ n, K (n + 1) ⊆ K n) :
    (⋂ n, K n).Nonempty := by
  -- `hdesc` iterated by induction on `m ≤ n`: `K n ⊆ K m`.
  -- Each `x n` lies in `K 0`, so seq-compactness of `K 0` applies.
  -- Closedness of `K m` (Part 3) + the fact that the tail `x (s k)` eventually
  -- lies in `K m` gives `x₀ ∈ K m`.
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/- Warm-up -/

example (K L : Set ℝ) (hK : IsSeqCompact K) (hL : IsSeqCompact L) :
    IsSeqCompact (K ∩ L) := by
  sorry

example : IsSeqCompact (∅ : Set ℝ) := by
  sorry

/- Core -/

example (f : ℝ → ℝ) (hcont : ∀ c ∈ Set.Icc (0 : ℝ) 1, ContinuousAt f c)
    (hmono : ∀ x y, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      x < y → f x < f y) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∃ δ > 0,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |x - c| < δ → |f x - f c| < 1 := by
  sorry

/- Challenging -/

example (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ∀ c ∈ Set.Icc a b, ContinuousAt f c) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      |x - y| < δ → |f x - f y| < ε := by
  sorry

end L29
