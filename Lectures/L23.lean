import MIL.Common
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 23: Infimum, Separation, and Nested Intervals

New concepts: **`lowerBounds`, `BddBelow`, `IsGLB`, `sInf`, `csInf_le`, `le_csInf`**
Recall: **`le_antisymm`, `linarith`, `nlinarith`, `rcases`, `obtain`, `have`, `by_contra!`, `push_neg`**

## Overview

Today we develop the **infimum** as the mirror image of the supremum,
then use both notions together in the **separation theorem**.
The climax is the nested interval property:
*Nested closed intervals  share a common point*.

This is one of the first places where completeness really behaves like a global
geometric principle rather than just an isolated theorem about one set.

### An Interesting Fact: Cantor Used Nested Intervals Before the Diagonal Argument

In 1874 Cantor proved that `ℝ` is uncountable by constructing nested closed
intervals that avoid the first real number, then the second, then the third,
and so on.  Completeness guarantees that the shrinking family still has a point
inside every interval.  That point is not on the list.
-/


-- ============================================================================
-- ## Part 1: Lower Bounds and Infimum
-- ============================================================================

#check lowerBounds
#check BddBelow
#check IsGLB
#check IsGLB.csInf_eq  -- (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a
#check csInf_le
#check le_csInf
#check bddBelow_Icc
#check csInf_Icc -- (h : a ≤ b) : sInf (Set.Icc a b) = a

example [LE α] (s : Set α) : BddBelow s = (∃ x, x ∈ lowerBounds s) := by rfl

example : BddBelow (Set.Icc (0 : ℝ) 1) := bddBelow_Icc

example : sInf (Set.Icc (0 : ℝ) 1) = 0 := csInf_Icc zero_le_one

/-
For infimum, the roles of the two main theorems reverse.

 `csInf_le`: the infimum is below every element of the set.
 `le_csInf`: every lower bound is below the infimum.
-/

/-
`IsGLB S a` is the abstract statement that `a` really is the infimum of `S`.
Once we prove that, `IsGLB.csInf_eq` turns the order-theoretic statement into
an explicit equation about `sInf`.
-/

example : IsGLB (Set.Icc (1 : ℝ) 4) 1 := by
  have hne : (Set.Icc (1 : ℝ) 4).Nonempty := by apply (Set.nonempty_Icc).mpr (by norm_num)
  have hglb : IsGLB (Set.Icc (1 : ℝ) 4) (sInf (Set.Icc (1 : ℝ) 4)) := by
    exact isGLB_csInf hne (bddBelow_Icc : BddBelow (Set.Icc (1 : ℝ) 4))
  rw [csInf_Icc] at hglb
  exact hglb
  norm_num

example : sInf (Set.Icc (1 : ℝ) 4) = 1 := by
  have hne : (Set.Icc (1 : ℝ) 4).Nonempty := (Set.nonempty_Icc).mpr (by norm_num)
  have hglb : IsGLB (Set.Icc (1 : ℝ) 4) 1 := by
    have hsInf : IsGLB (Set.Icc (1 : ℝ) 4) (sInf (Set.Icc (1 : ℝ) 4)) := by
      exact isGLB_csInf hne (bddBelow_Icc : BddBelow (Set.Icc (1 : ℝ) 4))
    rw [csInf_Icc (show (1 : ℝ) ≤ 4 by norm_num)] at hsInf
    exact hsInf
  exact hglb.csInf_eq hne

theorem exists_between_inf_plus_eps
  (S : Set ℝ) (hS : S.Nonempty) (_hB : BddBelow S) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, x < sInf S + ε := by
  by_contra! h
  have hs : sInf S + ε ≤ sInf S := by
    apply le_csInf hS
    -- show sInf S + ε ∈ lowerBounds S
    intro x hx
    exact h x hx
  linarith

/-
Lean does not use the boundedness hypothesis syntactically in this proof, but
mathematically it is what makes `sInf S` the intended infimum of the set.
-/

-- Exercise (Part 1): Compute the infimum of a closed interval.
example : sInf {x : ℝ | 1 ≤ x ∧ x ≤ 4} = 1 := by
  sorry


-- ============================================================================
-- ## Part 2: The Separation Theorem
-- ============================================================================

/-
If every element of `S` is at most every element of `T`, then the whole set `S`
sits to the left of the whole set `T`.  So the supremum of `S` is at most the
infimum of `T`.
-/

theorem separation_theorem
    (S T : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
  (_hS_bdd : BddAbove S) (_hT_bdd : BddBelow T)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s ≤ t) :
    sSup S ≤ sInf T := by
  apply le_csInf hT
  -- show sSup S ∈ lowerBounds T
  intro t ht
  apply csSup_le hS
  intro s hs
  exact hsep s hs t ht

example (S : Set ℝ) (hS : S.Nonempty) (hAbove : BddAbove S) (hBelow : BddBelow S) :
    sInf S ≤ sSup S := by
  rcases hS with ⟨x, hx⟩
  have h1 : sInf S ≤ x := csInf_le hBelow hx
  have h2 : x ≤ sSup S := le_csSup hAbove hx
  linarith

example (S : Set ℝ) (hS : S.Nonempty) (hAbove : BddAbove S) (hBelow : BddBelow S) :
    0 ≤ sSup S - sInf S := by
  rcases hS with ⟨x, hx⟩
  have h1 : sInf S ≤ x := csInf_le hBelow hx
  have h2 : x ≤ sSup S := le_csSup hAbove hx
  linarith

/-
If a whole set is trapped in a closed interval, then both extremal objects
produced by completeness stay trapped in that same interval.
-/

theorem inf_sup_mem_Icc_of_subset
  (S : Set ℝ) (hS : S.Nonempty) {a b : ℝ} (hsubset : S ⊆ Set.Icc a b) :
    sInf S ∈ Set.Icc a b ∧ sSup S ∈ Set.Icc a b := by
  have hBelow : BddBelow S := by
    use a
    intro x hx
    exact (hsubset hx).1
  have hAbove : BddAbove S := by
    use b
    intro x hx
    exact (hsubset hx).2
  constructor
  · constructor
    · apply le_csInf hS
      intro x hx
      exact (hsubset hx).1
    · rcases hS with ⟨x, hx⟩
      apply le_trans (csInf_le hBelow hx)
      exact (hsubset hx).2
  · constructor
    · rcases hS with ⟨x, hx⟩
      exact ((hsubset hx).1).trans (le_csSup hAbove hx)
    · apply csSup_le hS
      intro x hx
      exact (hsubset hx).2

-- Exercise (Part 2): Infimum is monotone in the reverse direction.
example (S T : Set ℝ) (hST : S ⊆ T) (hS : S.Nonempty) (hT : BddBelow T) :
    sInf T ≤ sInf S := by
  sorry


-- ============================================================================
-- ## Part 3: The Nested Interval Property
-- ============================================================================

/-
Write `I n = [a n, b n]`, where `a n` is the left endpoint and `b n` is the
right endpoint.

The hypotheses say:

 `a n ≤ b n` for every `n`, so each interval is nonempty.
 `I (n + 1) ⊆ I n` for every `n`, so the intervals are nested.

This formulation keeps the geometry visible: the key hypothesis is inclusion of
intervals, not monotonicity of endpoint sequences.
-/

lemma nested_Icc_subset_of_le
    (a b : ℕ → ℝ)
    (hsub : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) :
    ∀ {m n : ℕ}, m ≤ n → Set.Icc (a n) (b n) ⊆ Set.Icc (a m) (b m) := by
  intro m n hmn
  induction' hmn with n hmn ih
  · intro x hx
    exact hx
  · exact Set.Subset.trans (hsub n) ih

lemma left_end_le_right_end_of_nested
    (a b : ℕ → ℝ)
    (hab : ∀ n, a n ≤ b n)
    (hsub : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) :
    ∀ m n, a m ≤ b n := by
  intro m n
  rcases le_total m n with hmn | hnm
  · have hsubset : Set.Icc (a n) (b n) ⊆ Set.Icc (a m) (b m) :=
      nested_Icc_subset_of_le a b hsub hmn
    have hmem : b n ∈ Set.Icc (a n) (b n) := by
      exact ⟨hab n, le_rfl⟩
    exact (hsubset hmem).1
  · have hsubset : Set.Icc (a m) (b m) ⊆ Set.Icc (a n) (b n) :=
      nested_Icc_subset_of_le a b hsub hnm
    have hmem : a m ∈ Set.Icc (a m) (b m) := by
      exact ⟨le_rfl, hab m⟩
    exact (hsubset hmem).2

/-
This is the completeness move behind the nested-interval theorem.

The hypothesis `a m ≤ b n` for all `m, n` says that the left endpoints and the
right endpoints form two separated sets.  We then apply the separation theorem
to the ranges of `a` and `b`, and completeness produces a single real lying in
every interval.
-/

lemma common_point_of_separated_endpoints
    (a b : ℕ → ℝ)
    (hcross : ∀ m n, a m ≤ b n) :
    ∃ c : ℝ, ∀ n, c ∈ Set.Icc (a n) (b n) := by
  let S : Set ℝ := Set.range a
  let T : Set ℝ := Set.range b
  have hS_nonempty : S.Nonempty := by
    refine ⟨a 0, ?_⟩
    dsimp [S]
    exact ⟨0, rfl⟩
  have hS_bdd : BddAbove S := by
    refine ⟨b 0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact hcross m 0
  have hT_nonempty : T.Nonempty := by
    refine ⟨b 0, ?_⟩
    dsimp [T]
    exact ⟨0, rfl⟩
  have hT_bdd : BddBelow T := by
    refine ⟨a 0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hcross 0 n
  have hsep : sSup S ≤ sInf T := by
    apply separation_theorem S T hS_nonempty hT_nonempty hS_bdd hT_bdd
    intro s hs t ht
    rcases hs with ⟨m, rfl⟩
    rcases ht with ⟨n, rfl⟩
    exact hcross m n
  refine ⟨sSup S, ?_⟩
  intro n
  constructor
  · have hmemS : a n ∈ S := by
      dsimp [S]
      exact ⟨n, rfl⟩
    exact le_csSup hS_bdd hmemS
  · have hmemT : b n ∈ T := by
      dsimp [T]
      exact ⟨n, rfl⟩
    exact hsep.trans (csInf_le hT_bdd hmemT)

theorem nested_interval_property
    (a b : ℕ → ℝ)
    (hab : ∀ n, a n ≤ b n)
    (hsub : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) :
    ∃ c : ℝ, ∀ n, c ∈ Set.Icc (a n) (b n) := by
  have hcross : ∀ m n, a m ≤ b n :=
    left_end_le_right_end_of_nested a b hab hsub
  exact common_point_of_separated_endpoints a b hcross

/-
In `ℚ`, nested closed intervals can have empty intersection.  The standard
example is a shrinking rational approximation to `√2`: the intervals close in
around a real number that is not rational.

What we proved above is only existence of a common point, not uniqueness.  To
force the intersection down to a single point, one also needs the interval
lengths to tend to `0`.
-/

-- Exercise (Part 3): A concrete nested family.
example (n : ℕ) : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / ((n : ℝ) + 1)) := by
  sorry


-- ============================================================================
-- ## Part 4: Applications
-- ============================================================================

theorem eq_of_sInf_eq_sSup
  (S : Set ℝ) (_hS : S.Nonempty) (hAbove : BddAbove S) (hBelow : BddBelow S)
    (hEq : sInf S = sSup S) :
    ∀ x ∈ S, x = sSup S := by
  intro x hx
  have h1 : sInf S ≤ x := csInf_le hBelow hx
  have h2 : x ≤ sSup S := le_csSup hAbove hx
  rw [hEq] at h1
  linarith

/-
A useful Stage 10 application is to apply the interval-trapping theorem to the
range of a function.
-/

example (f : ℕ → ℝ) (h : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) :
    sInf (Set.range f) ∈ Set.Icc (0 : ℝ) 1 ∧
      sSup (Set.range f) ∈ Set.Icc (0 : ℝ) 1 := by
  apply inf_sup_mem_Icc_of_subset
  · exact ⟨f 0, ⟨0, rfl⟩⟩
  · rintro x ⟨n, rfl⟩
    exact h n

-- Exercise (Part 4): The shrinking intervals `[0, 1 / (n + 1)]` intersect only at `0`.
example : (⋂ n : ℕ, Set.Icc (0 : ℝ) (1 / ((n : ℝ) + 1))) ⊆ ({0} : Set ℝ) := by
  intro x hx
  simp only [Set.mem_singleton_iff]
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

-- Warm-up
example : BddBelow (Set.Icc (3 : ℝ) 7) := by
  sorry

-- Warm-up
example : sInf (Set.Icc (3 : ℝ) 7) = 3 := by
  sorry

-- Warm-up
example (a b x : ℝ) (h : a ≤ b) (hx : x ∈ Set.Icc a b) :
    sInf (Set.Icc a b) ≤ x ∧ x ≤ sSup (Set.Icc a b) := by
  sorry

-- Core
example (S : Set ℝ) (hS : S.Nonempty) (hB : BddBelow S) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, x < sInf S + ε := by
  sorry

-- Core
example (S : Set ℝ) (a : ℝ) (hS : S.Nonempty) (hglb : IsGLB S a) :
    sInf S = a := by
  sorry

-- Core
example : IsGLB {x : ℝ | 1 ≤ x ∧ x ≤ 4} 1 := by
  sorry

-- Challenging
example (S T : Set ℝ) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (hBelowT : BddBelow T) (hAboveT : BddAbove T) :
    sInf T ≤ sInf S ∧ sSup S ≤ sSup T := by
  sorry

-- Challenging
example : sSup {x : ℝ | 0 ≤ x ∧ x ^ 3 ≤ 27} = 3 := by
  sorry

-- Challenging
example : sInf {x : ℝ | 1 ≤ x ∧ x ≤ 4} = 1 := by
  sorry
