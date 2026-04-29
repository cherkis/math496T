import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 28: Sequential Characterizations, Bolzano–Weierstrass, and EVT (for maximum)

New concepts: **Converse sequential continuity, sequential compactness, Bolzano–Weierstrass, the Extreme Value Theorem**
New Mathlib API: **`StrictMono`, `StrictMono.id_le`, `not_bddAbove_iff`, `Set.Nonempty.image`**

Recall: **`ConvergesTo`, `limit_unique`, `squeeze_theorem` (L24), `exists_between_sup_minus_eps`, `le_csSup` (L22), `BddAbove`, `exists_nat_gt` (L20), `one_div_le_one_div_of_le` (L21), `unfold` (L10), `simp only` (L10), `choose` (L14)**

## Overview

Today we return to sequences — but from a topological perspective.

 1. *Continuity and sequences speak the same language.*  Last lecture we
    showed that `ContinuousAt f c` implies the ε-δ-free condition
    `aₙ → c ⟹ f(aₙ) → f c`.  Today we prove the converse, so both
    conditions are *equivalent*.  One continuity theorem, two dictionaries.
 2. *Closed bounded intervals are "sequentially compact"*: every sequence
    has a convergent subsequence.  This is the Bolzano–Weierstrass
    theorem, the machine that powers existence theorems like the Extreme
    Value Theorem.

Bolzano–Weierstrass is proved by *bisection*: repeatedly halving `[A, B]`,
always keeping the half with infinitely many terms of the sequence.
The Monotone Convergence Theorem (L25) makes the nested interval endpoints converge;
the squeeze theorem (L24) carries the subsequence along.
-/

namespace L28

def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

def ContinuousAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

/-- Local copy of the sSup ε-approximation lemma from L22. -/
private theorem exists_between_sup_minus_eps
    (S : Set ℝ) (hS : S.Nonempty) (_hB : BddAbove S) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  by_contra! h
  have : sSup S ≤ sSup S - ε := by
    apply csSup_le hS
    intro x hx
    linarith [h x hx]
  linarith

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

/-- Squeeze theorem (from L24), restated locally. -/
private theorem squeeze_theorem (x a y : ℕ → ℝ) (L : ℝ)
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


-- ============================================================================
-- ## Part 1: Converse sequential continuity
-- ============================================================================

/-
L27 showed: `ContinuousAt f c` implies preservation of convergent sequences at `c`.
The converse is true too: if `f` preserves every convergent
sequence at `c`, then `f` is continuous at `c`.

The contrapositive idea: if `f` is discontinuous at `c`, build a sequence
`aₙ → c` on which `f` fails to converge by grabbing, for each `n`,
an `aₙ` within `1/(n+1)` of `c` yet with `|f aₙ − f c| ≥ ε₀`.
-/

theorem continuousAt_of_seq {f : ℝ → ℝ} {c : ℝ}
    (hseq : ∀ a : ℕ → ℝ, ConvergesTo a c →
        ConvergesTo (fun n => f (a n)) (f c)) :
    ContinuousAt f c := by
  by_contra hnc
  unfold ContinuousAt at hnc
  push_neg at hnc
  obtain ⟨ε₀, hε₀, hbad⟩ := hnc
  -- For each n, pick aₙ with |aₙ − c| < 1/(n+1) and |f aₙ − f c| ≥ ε₀.
  choose a ha_close ha_bad using fun n : ℕ =>
    hbad (1 / ((n : ℝ) + 1)) (by positivity)
  -- aₙ converges to c
  have ha_conv : ConvergesTo a c := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    linarith [ha_close n, hN]
  -- so, by assumption, f(aₙ) converges to f(c)
  have hfconv : ConvergesTo (fun n => f (a n)) (f c) := hseq a ha_conv
  obtain ⟨N, hN⟩ := hfconv ε₀ hε₀
  -- Being ε₀ away from f(c) contradicts this convergence of f(aₙ)
  linarith [ha_bad N, hN N le_rfl]

-- **Practice**: if `aₙ ∈ [a, b]` and `aₙ → c`, then `c ∈ [a, b]`.
example (a b : ℝ) (seq : ℕ → ℝ) (c : ℝ)
    (hseq : ∀ n, seq n ∈ Set.Icc a b) (hconv : ConvergesTo seq c) :
    c ∈ Set.Icc a b := by
  sorry


-- ============================================================================
-- ## Part 2: Sequential compactness
-- ============================================================================

/-
A set `K ⊆ ℝ` is **sequentially compact** if every sequence in `K`
has a subsequence that converges to a point still inside `K`.
-/

def IsSeqCompact (K : Set ℝ) : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, a n ∈ K) →
    ∃ (s : ℕ → ℕ) (x : ℝ), x ∈ K ∧ StrictMono s ∧
      ConvergesTo (fun n => a (s n)) x

/-
Two non-examples.  `(0, 1]` is not sequentially compact:
`1/(n+1)` lies in it and converges to `0 ∉ (0, 1]`.
Likewise `ℝ` is not sequentially compact:
`n → ∞` leaves every fixed bounded region.
Sequential compactness is strictly stronger than mere boundedness
— and it turns out (L29) it's *precisely* "closed and bounded."
-/

-- **Practice**: a singleton is sequentially compact.
example (p : ℝ) : IsSeqCompact ({p} : Set ℝ) := by
  sorry


-- ============================================================================
-- ## Part 3: Bolzano–Weierstrass (climax)
-- ============================================================================

/-
Every sequence inside a closed interval `[A, B]` has a convergent
subsequence with limit still in `[A, B]`.

Proof sketch (bisection).  For each `k`, maintain:

* a nested sub-interval `[L_k, R_k] ⊆ [A, B]` of length
    `(B − A) / 2^k`,
* an index `n_k` with `a n_k ∈ [L_k, R_k]` and `n_k < n_{k+1}`,
* the guarantee that `[L_k, R_k]` contains the sequence at infinitely
    many indices past `n_k`.

- The endpoints `L_k ↑` and `R_k ↓` are monotone and bounded, so by the
Monotone Convergence Theorem (L25) each converges.
- Their limits agree because `R_k − L_k → 0`, giving `x ∈ [A, B]`.
- The squeeze theorem (L24) applied to `L_k ≤ a n_k ≤ R_k` forces `a n_k → x`.

The recursive bisection proof in Lean is intricate enough that we mark the
theorem here as a `sorry` and treat it as a black box for the rest of the
file.  A full treatment is the subject of a follow-on exercise.
-/

theorem bolzano_weierstrass (A B : ℝ) (hAB : A ≤ B) :
    IsSeqCompact (Set.Icc A B) := by
  sorry

-- **Practice**: a union of two seq-compact sets is seq-compact.
example (K L : Set ℝ) (hK : IsSeqCompact K) (hL : IsSeqCompact L) :
    IsSeqCompact (K ∪ L) := by
  sorry


-- ============================================================================
-- ## Part 4: Extreme Value Theorem (maximum)
-- ============================================================================

/-
First: a continuous function on a sequentially compact set is bounded above.
This is the first place where compactness is genuinely used in an existence
argument.
-/

theorem f_bounded_above_on_seqcompact {K : Set ℝ} (_hKne : K.Nonempty) (hK : IsSeqCompact K)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c)  :
    BddAbove (f '' K) := by
  by_contra hub
  rw [not_bddAbove_iff] at hub
  -- For each n, pick xₙ ∈ K with f xₙ > n.
  have hexists : ∀ n : ℕ, ∃ x ∈ K, (n : ℝ) < f x := by
    intro n
    obtain ⟨y, hyK, hyn⟩ := hub (n : ℝ)
    obtain ⟨x, hxK, hxy⟩ := hyK
    use x, hxK
    rw [hxy]; exact hyn
  choose x hxK hxn using hexists
  -- use sequencial compactness to choose a subsequence x_{s_k} → x₀
  obtain ⟨s, x₀, hx₀K, hsmono, hconv⟩ := hK x hxK
  -- By continuity + forward sequential continuity, f (x (s k)) → f x₀.
  have hcont₀ : ContinuousAt f x₀ := hcont x₀ hx₀K
  have hfconv : ConvergesTo (fun k => f (x (s k))) (f x₀) := by
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := hcont₀ ε hε
    obtain ⟨N, hN⟩ := hconv δ hδ
    use N
    intro k hk
    exact hδprop (x (s k)) (hN k hk)
  -- But f (x (s k)) > s k ≥ k, so the subsequence is unbounded — contradicting
  -- convergence (in particular, the limit would need to be ≥ every integer).
  obtain ⟨N, hN⟩ := hfconv 1 (by norm_num)
  -- Choose M so that M ≥ f x₀ + 2 and M is a natural ≥ N.
  obtain ⟨M, hM_nat⟩ : ∃ M : ℕ, f x₀ + 2 < (M : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_gt (f x₀ + 2)
    exact ⟨M, hM⟩
  let k := max N M
  have hsk : (k : ℝ) ≤ (s k : ℝ) := by
    have := hsmono.id_le k
    exact_mod_cast this
  have h1 : f (x (s k)) > (s k : ℝ) := hxn (s k)
  have h2 : |f (x (s k)) - f x₀| < 1 := hN k (le_max_left _ _)
  rw [abs_lt] at h2
  have hMk : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right N M
  linarith

/-
EVT for maximum next.  EVT for minimum is obtained by applying EVT max  to `−f`.
-/

theorem evt_max {K : Set ℝ} (hK : IsSeqCompact K) (hKne : K.Nonempty)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c) :
    ∃ xmax ∈ K, ∀ x ∈ K, f x ≤ f xmax := by
  have hbdd : BddAbove (f '' K) := f_bounded_above_on_seqcompact hKne hK hcont
  have hfKne : (f '' K).Nonempty := hKne.image f
  set M := sSup (f '' K) with hM_def
  -- For each n, pick xₙ ∈ K with f xₙ > M − 1/(n+1).
  have hexists : ∀ n : ℕ, ∃ x ∈ K, M - 1 / ((n : ℝ) + 1) < f x := by
    intro n
    obtain ⟨y, hyfK, hyMn⟩ :=
      exists_between_sup_minus_eps (f '' K) hfKne hbdd (1 / ((n : ℝ) + 1))
        (by positivity)
    obtain ⟨x, hxK, hxy⟩ := hyfK
    use x, hxK
    rw [hxy]; exact hyMn
  choose x hxK hxn using hexists
  obtain ⟨s, x₀, hx₀K, hsmono, hconv⟩ := hK x hxK
  use x₀, hx₀K
  -- By continuity, f (x (s k)) → f x₀.
  have hcont₀ : ContinuousAt f x₀ := hcont x₀ hx₀K
  have hfconv : ConvergesTo (fun k => f (x (s k))) (f x₀) := by
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := hcont₀ ε hε
    obtain ⟨N, hN⟩ := hconv δ hδ
    use N
    intro k hk
    exact hδprop (x (s k)) (hN k hk)
  -- Squeeze: M − 1/(s k + 1) < f (x (s k)) ≤ M.
  have hfxM : ∀ k, f (x (s k)) ≤ M := fun k =>
    le_csSup hbdd ⟨x (s k), hxK (s k), rfl⟩
  have hfxLo : ∀ k, M - 1 / (((s k) : ℝ) + 1) ≤ f (x (s k)) :=
    fun k => le_of_lt (hxn (s k))
  -- The lower sequence `k ↦ M − 1/(s k + 1)` converges to M.
  have hlo_conv : ConvergesTo (fun k => M - 1 / (((s k) : ℝ) + 1)) M := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro k hk
    have hsk : N ≤ s k := le_trans hk (hsmono.id_le k)
    have hle : 1 / (((s k) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hsk 1
    have hnonneg : (0 : ℝ) ≤ 1 / (((s k) : ℝ) + 1) := by positivity
    rw [abs_of_nonpos (by linarith : M - 1 / (((s k) : ℝ) + 1) - M ≤ 0)]
    linarith
  -- The upper sequence `k ↦ M` converges to M.
  have hhi_conv : ConvergesTo (fun _ : ℕ => M) M := fun ε hε =>
    ⟨0, fun _ _ => by simp [hε]⟩
  -- Squeeze gives `f (x (s k)) → M`.
  have hsq : ConvergesTo (fun k => f (x (s k))) M :=
    squeeze_theorem _ _ _ M hfxLo hfxM hlo_conv hhi_conv
  -- Uniqueness: f x₀ = M.
  have hfx₀M : f x₀ = M := limit_unique _ _ _ hfconv hsq
  intro y hyK
  calc f y ≤ M := le_csSup hbdd ⟨y, hyK, rfl⟩
    _ = f x₀ := hfx₀M.symm


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

example (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ∀ c ∈ Set.Icc a b, ContinuousAt f c)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < f x) :
    ∃ m > 0, ∀ x ∈ Set.Icc a b, m ≤ f x := by
  sorry

example (a : ℕ → ℝ) (s : ℕ → ℕ) (x : ℝ)
    (ha : ConvergesTo a x) (hs : StrictMono s) :
    ConvergesTo (fun n => a (s n)) x := by
  sorry

/- Challenging -/

example {K : Set ℝ} (hK : IsSeqCompact K) (hKne : K.Nonempty)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c) :
    ∃ xmin ∈ K, ∀ x ∈ K, f xmin ≤ f x := by
  sorry

end L28
