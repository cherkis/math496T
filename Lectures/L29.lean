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
  by_contra h
  have hε : 0 < |L - M| / 2 := by
    have : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr h)
    linarith
  obtain ⟨N₁, hN₁⟩ := hL _ hε
  obtain ⟨N₂, hN₂⟩ := hM _ hε
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  have htri : |L - M| ≤ |L - a (max N₁ N₂)| + |a (max N₁ N₂) - M| := by
    have : L - M = (L - a (max N₁ N₂)) + (a (max N₁ N₂) - M) := by ring
    rw [this]; exact abs_add_le _ _
  rw [abs_sub_comm L (a _)] at htri
  linarith

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
  have hneg : ∀ c ∈ K, ContinuousAt (fun x => -f x) c := by
    intro c hc ε hε
    obtain ⟨δ, hδ, hδprop⟩ := hcont c hc ε hε
    use δ, hδ
    simp
    simp_rw [add_comm,←sub_eq_add_neg,abs_sub_comm (f c)]
    exact hδprop
  obtain ⟨xmin, hxminK, hmax⟩ := evt_max hK hKne hneg
  use xmin, hxminK
  intro x hx
  linarith [hmax x hx]


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
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  -- After index `N` we have `|aₙ − L| < 1`, hence `|aₙ| ≤ |L| + 1`.
  -- For indices `≤ N` we take the max of finitely many `|a k|`.
  let C : ℕ → ℝ := fun n => |a n|
  let bound_pre : ℝ := (Finset.range (N + 1)).sup' Finset.nonempty_range_succ C
  use max bound_pre (|L| + 1)
  intro n
  by_cases hnN : n ≤ N
  · have hbp : C n ≤ bound_pre := by
      apply Finset.le_sup'
      simp [Nat.lt_succ_iff]; exact hnN
    linarith [le_max_left bound_pre (|L| + 1)]
  · push_neg at hnN
    -- from convergence |a n - L| < 1
    have h_above := hN n (le_of_lt hnN)
    have htri : |a n| ≤ |L| + 1 := by
      calc |a n| = |a n - L + L| := by ring_nf
        _ ≤ |a n - L| + |L| := by apply abs_add_le
        _ ≤ |L| + 1 := by linarith
    linarith [le_max_right bound_pre (|L| + 1)]

theorem seqCompact_bounded {K : Set ℝ} (hK : IsSeqCompact K) :
    ∃ M, ∀ x ∈ K, |x| ≤ M := by
  by_contra! h
  -- For each n, pick xₙ ∈ K with |xₙ| > n.
  choose x hxK hxn using fun n : ℕ => h (n : ℝ)
  obtain ⟨s, _, _, hsmono, hconv⟩ := hK x hxK
  obtain ⟨M, hM⟩ := bounded_of_convergesTo hconv
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsmN : (N : ℝ) ≤ (s N : ℝ) := by exact_mod_cast hsmono.id_le N
  linarith [hxn (s N), hM N]


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
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  use N
  intro n hn
  exact hN (s n) (le_trans hn (hs.id_le n))

theorem seqCompact_closed {K : Set ℝ} (hK : IsSeqCompact K) :
    IsClosedSet K := by
  intro x hxc
  by_contra! hnb
  -- For each n : ℕ, pick yₙ ∈ K with |yₙ − x| < 1/(n+1).
  have hseq : ∀ n : ℕ, ∃ y, y ∈ K ∧ |y - x| < 1 / ((n : ℝ) + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hy_close, hy_compl⟩ := hnb _ hε
    refine ⟨y, ?_, hy_close⟩
    rw [Set.mem_compl_iff, not_not] at hy_compl
    exact hy_compl
  choose y hyK hy_close using hseq
  -- y n → x.
  have hy_to_x : ConvergesTo y x := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    linarith [hy_close n, hN]
  -- Seq-compactness gives a subsequence → some z ∈ K; but subsequence also → x.
  obtain ⟨s, z, hzK, hsmono, hconv⟩ := hK y hyK
  have hys_to_x : ConvergesTo (fun n => y (s n)) x := subseq_conv hy_to_x hsmono
  have hxz : x = z := limit_unique _ _ _ hys_to_x hconv
  rw [hxz, Set.mem_compl_iff] at hxc
  exact hxc hzK


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
  constructor
  · intro hK
    exact ⟨seqCompact_closed hK, seqCompact_bounded hK⟩
  · rintro ⟨hclosed, M, hbdd⟩ a ha
    have haIcc : ∀ n, a n ∈ Set.Icc (-M) M := by
      intro n
      rw [Set.mem_Icc, ← abs_le]
      exact hbdd (a n) (ha n)
    have hMpos : (-M) ≤ M := by
      linarith [hbdd (a 0) (ha 0), abs_nonneg (a 0)]
    obtain ⟨s, x, _, hsmono, hconv⟩ := bolzano_weierstrass (-M) M hMpos a haIcc
    use s, x
    refine ⟨?_, hsmono, hconv⟩
    -- `x ∈ K` by closedness + sequential characterization.
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := hclosed x hxK
    obtain ⟨N, hN⟩ := hconv ε hε
    exact hball (a (s N)) (hN N le_rfl) (ha (s N))


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
  choose x hx using hne
  -- `hdesc` iterated by induction on `m ≤ n`: `K n ⊆ K m`.
  have hdesc_iter : ∀ m n, m ≤ n → K n ⊆ K m := by
    intro m n hmn
    induction hmn with
    | refl => exact fun _ h => h
    | step _ ih => exact fun y hy => ih (hdesc _ hy)
  -- Each `x n` lies in `K 0`, so seq-compactness of `K 0` applies.
  have hx0 : ∀ n, x n ∈ K 0 := fun n => hdesc_iter 0 n (Nat.zero_le n) (hx n)
  obtain ⟨s, x₀, _, hsmono, hconv⟩ := hcompact 0 x hx0
  use x₀
  simp only [Set.mem_iInter]
  intro m
  -- Closedness of `K m` (Part 3) + the fact that the tail `x (s k)` eventually
  -- lies in `K m` gives `x₀ ∈ K m`.
  by_contra hx₀K
  obtain ⟨ε, hε, hball⟩ := seqCompact_closed (hcompact m) x₀ hx₀K
  obtain ⟨N, hN⟩ := hconv ε hε
  let k := max N m
  have hsk_ge_m : m ≤ s k := le_trans (le_max_right N m) (hsmono.id_le k)
  exact hball (x (s k)) (hN k (le_max_left N m))
    (hdesc_iter m (s k) hsk_ge_m (hx (s k)))


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
