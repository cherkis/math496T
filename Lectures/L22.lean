import MIL.Common
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 22: Supremum and the Completeness of `ℝ`

New concepts: **`Set.Icc`, `Set.Ioo`, `upperBounds`, `BddAbove`, `IsLUB`, `sSup`**
New tactic: **`by_contra!`** is `by_contra` with `push_neg`
Recall: **`linarith`, `nlinarith`, `positivity`, `push_cast`, `obtain`, `rcases`, `have`, `apply`, `refine`, `le_antisymm`**

## Overview

Today we study the **supremum** of a set of real numbers.  A supremum is the
smallest real number that bounds the set from above.
Difference between maximum and supremum.

The key practical idea is this: if `sSup S` is the supremum, then
- every element of `S` is less or equal to `sSup S`, and
- every upper bound of `S` is greater or equal to `sSup S`.
These two directions are exactly what we need for `le_antisymm` proofs.

### An Interesting Fact: Completeness Implies the Archimedean Property

In Lecture 20 we listed completeness and the Archimedean property side by side.
But one of them is actually redundant.  If `ℕ` were bounded above in `ℝ`, then
by completeness `ℕ` would give a supremum `s`.  The ε-approximation property would
produce some natural number `n` with `s - 1 < n`, so `n + 1 > s`.  That
contradicts `s` being an upper bound.  So completeness already forces `ℕ` to
be unbounded in `ℝ`.
-/


-- ============================================================================
-- ## Part 1: Intervals and Upper Bounds
-- ============================================================================

/-
We use closed intervals `Set.Icc a b = [a, b]` and
open intervals `Set.Ioo a b = (a, b)` throughout this lecture.

`Set.Ico a b` and `Set.Ioc a b` are half-closed intervals.
-/

#check Set.Icc
#check Set.Ioo

example (a b x : ℝ) : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b := by rfl
example (a b x : ℝ) : x ∈ Set.Ioo a b ↔ a < x ∧ x < b := by rfl

#check upperBounds -- : (s : Set α) → Set α
-- Bounded above
#check BddAbove -- (upperBounds s).Nonempty
-- is Least Upper Bound
#check IsLUB

example [LE α] (s : Set α) : BddAbove s = (∃ x, x ∈ upperBounds s) := by rfl

example : BddAbove (Set.Icc (0 : ℝ) 1) := by
  exact bddAbove_Icc

example : (Set.Icc (0 : ℝ) 1).Nonempty := by
  exact Set.nonempty_Icc.mpr (by norm_num)

example : (Set.Icc (0 : ℝ) 1).Nonempty := by
  use 1
  dsimp [Set.Icc]; constructor <;> linarith

/-
The midpoint of an open interval stays inside the interval.  This is the most
basic way to produce a new point strictly between two given reals.
-/

example (a b : ℝ) (h : a < b) : (a + b) / 2 ∈ Set.Ioo a b := by
  constructor <;> linarith


-- ============================================================================
-- ## Part 2: The Supremum API and the `le_antisymm` Pattern
-- ============================================================================

/-
The two fundamental theorems are:

 `le_csSup`: every element of the set is at most the supremum.
 `csSup_le`: every upper bound is at least the supremum.

Together they turn equality proofs into two inequality proofs.
-/

#check le_csSup  -- (BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s
#check csSup_le  -- (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a

example : sSup (Set.Icc (0 : ℝ) 1) = 1 := by
  apply le_antisymm
  · apply csSup_le
    · use 0; norm_num
    · intro x hx
      exact hx.2
  · apply le_csSup
    apply bddAbove_Icc
    simp

/-
The supremum of `(0, 1)` is still `1`, even though `1 ∉ (0, 1)`.
That is the difference between a **maximum** and a **supremum**.
-/

example : sSup (Set.Ioo (0 : ℝ) 1) = 1 := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  rw [csSup_Ioo h01]

/-
Now a predicate-defined set:

 `S = {x : ℝ | 0 ≤ x ∧ x ^ 2 ≤ 4}`.

Its supremum is `2`.
-/

example (a : α) (P : α → Prop) : a ∈ {x | P x} ↔ P a := by exact Set.mem_setOf

example (S : Set ℝ) (h : S = {x : ℝ | 0 ≤ x ∧ x ^ 2 ≤ 4}) : sSup S = 2 := by
  apply le_antisymm
  . apply csSup_le
    . use 2; simp [h,Set.mem_setOf]; linarith
    . intro x hx
      simp [h,Set.mem_setOf] at hx
      rcases hx with ⟨hx0, hx2⟩
      nlinarith
  . apply le_csSup
    use 2 <;> simp [h,Set.mem_setOf]
    intro x hx
    . obtain ⟨hx0, hx2⟩ := hx
      nlinarith
    . rw [h,Set.mem_setOf]
      constructor <;> linarith

-- Exercise (Part 2): An open interval has no maximum element.
example (a b : ℝ) (h : a < b) :
    ¬ ∃ m ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo a b, x ≤ m := by
  sorry


-- ============================================================================
-- ## Part 3: The ε-Approximation Property
-- ============================================================================

/-
This is the main working property of the supremum.

If `ε > 0`, then some point of the set lies above `sSup S - ε`.
So the supremum can be approached from below by actual elements of the set.
-/

-- NB : the `BddAbove` hypothesis is necessary, otherwise the supremum is `+∞` and the claim is false.
theorem exists_between_sup_minus_eps
  (S : Set ℝ) (hS : S.Nonempty) (_hB : BddAbove S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  by_contra! h
  -- push_neg at h
  have hs : sSup S ≤ sSup S - ε := by
    apply csSup_le hS
    intro x hx
    exact h x hx
  linarith

/-
If the supremum is positive, then the set contains a positive element.
Just apply the ε-approximation theorem with `ε = sSup S`.
-/

example (S : Set ℝ) (hS : S.Nonempty) (hB : BddAbove S) (hSup : 0 < sSup S) :
    ∃ x ∈ S, 0 < x := by
  obtain ⟨x, hxS, hx⟩ :=
    exists_between_sup_minus_eps S hS hB (sSup S) hSup
  refine ⟨x, hxS, ?_⟩
  linarith

-- Exercise (Part 3): If `b < sSup S`, then some element of `S` lies above `b`.
example (S : Set ℝ) (hS : S.Nonempty) (hB : BddAbove S) (b : ℝ)
    (hb : b < sSup S) :
    ∃ x ∈ S, b < x := by
  sorry


-- ============================================================================
-- ## Part 4: Completeness Implies Archimedean
-- ============================================================================

/-
We now formalize the interesting fact from the introduction.

If the range of `ℕ → ℝ : n ↦ n` were bounded above, its supremum would lead to a
contradiction by the ε-approximation theorem with `ε = 1`.
-/

theorem natCast_range_not_bddAbove :
    ¬ BddAbove (Set.range fun n : ℕ => (n : ℝ)) := by
  intro hB
  let S : Set ℝ := Set.range fun n : ℕ => (n : ℝ)
  have hS : S.Nonempty := by
    use 0
    dsimp [S,Set.mem_setOf]
    use 0
    push_cast
    rfl
  obtain ⟨x, hxS, hx⟩ := exists_between_sup_minus_eps S hS hB 1 (by norm_num)
  rcases hxS with ⟨n, hn⟩
  push_cast at hn
  have hsucc_mem : (((n + 1 : ℕ) : ℝ)) ∈ S := by
    dsimp [S,Set.mem_setOf]
    exact ⟨n + 1, rfl⟩
  have hsucc_le : (((n + 1 : ℕ) : ℝ)) ≤ sSup S := by
    exact le_csSup hB hsucc_mem
  push_cast at hsucc_le
  linarith

example (x : ℝ) : ∃ n : ℕ, x < (n : ℝ) := by
  by_contra hx
  apply natCast_range_not_bddAbove
  refine ⟨x, ?_⟩
  rintro y ⟨n, rfl⟩
  by_contra hnx
  exact hx ⟨n, lt_of_not_ge hnx⟩


-- ============================================================================
-- ## Part 5: Supremum of a Union
-- ============================================================================

/-
For nonempty bounded-above sets, the supremum of a union is the maximum of the
two individual suprema.
-/

#check csSup_union -- (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) : sSup (s ∪ t) = sSup s ⊔ sSup t
-- In our case `sSup s ⊔ sSup t` is `max (sSup s) (sSup t)`

example : sSup (Set.Icc (0 : ℝ) 2 ∪ Set.Icc (3 : ℝ) 5) = 5 := by
  have h₁ : BddAbove (Set.Icc (0 : ℝ) 2) := bddAbove_Icc
  have h₂ : (Set.Icc (0 : ℝ) 2).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  have h₃ : BddAbove (Set.Icc (3 : ℝ) 5) := bddAbove_Icc
  have h₄ : (Set.Icc (3 : ℝ) 5).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  rw [csSup_union h₁ h₂ h₃ h₄]
  rw [csSup_Icc (by norm_num), csSup_Icc (by norm_num)]
  norm_num

-- Exercise (Part 5): Supremum is monotone under inclusion.
example (S T : Set ℝ) (hST : S ⊆ T) (hS : S.Nonempty) (hT : BddAbove T) :
    sSup S ≤ sSup T := by
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

-- Warm-up
example (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (a + b) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

-- Warm-up
example (a b : ℝ) : Set.Ioo a b ⊆ Set.Icc a b := by
  intro x hx
  exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩

-- Core
example (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hne : S.Nonempty) :
    sSup S ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

-- Core
example (f : ℕ → ℝ) (h : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) :
    sSup (Set.range f) ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

-- Challenging
example : sSup {x : ℝ | 0 ≤ x ∧ x ^ 2 ≤ 2} ≤ 2 := by
  apply csSup_le
  · refine ⟨1, ?_⟩
    norm_num
  · intro x hx
    rcases hx with ⟨hx0, hx2⟩
    by_contra hgt
    have hxgt : 2 < x := by linarith
    nlinarith

-- Challenging: disprove the claim that `S ⊆ T` and `sSup S = sSup T` force `S = T`.
example :
    Set.Ioo (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 ∧
      Set.Ioo (0 : ℝ) 1 ≠ Set.Icc (0 : ℝ) 1 ∧
      sSup (Set.Ioo (0 : ℝ) 1) = sSup (Set.Icc (0 : ℝ) 1) := by
  refine ⟨Set.Ioo_subset_Icc_self, ?_⟩
  refine ⟨?_, ?_⟩
  · intro hEq
    have h : (0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [hEq]
      simp
    have h0 : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) 1 := by simp
    exact h0 h
  · rw [csSup_Ioo (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num), csSup_Icc (by norm_num)]
