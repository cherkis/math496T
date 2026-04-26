-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

--! # Homework 11: Topology, Continuity, IVT, and EVT

/-!
This homework covers Lectures 26-29.

Topics: open sets, closure points (sequential characterization),
ε-δ continuity, the Intermediate Value Theorem, and the Extreme Value
Theorem for sequentially compact subsets of `ℝ`.

**Total: 50 points.**

The definitions below reproduce those introduced in L26–L29 so that this
homework is self-contained.
-/

/-- A set `U ⊆ ℝ` is **open** if every point has an ε-neighborhood in `U`. -/
def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

/-- `x` is a **closure point** of `S` if every ε-neighborhood of `x` meets `S`. -/
def IsClosurePt (x : ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ S, |y - x| < ε

/-- `a n → L` in the ε-N sense. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

/-- `f` is **continuous at `c`** in the ε-δ sense. -/
def ContAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

/-- We already proved the Intermediate Value Theorem (IVT) -/
axiom IVT (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcont : ∀ c ∈ Set.Icc a b, ContAt f c)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0

/-- We also proved the Extreme Value Theorem (EVT) in lecture 29 -/
axiom evt_min (hab : (a:ℝ) ≤ b)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ Set.Icc a b, ContAt f c) :
    ∃ xmin ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f xmin ≤ f x

-- ============================================================================
-- Problem 1: Open intervals are open
-- ============================================================================

/-
Prove that the open interval `(a, b)` is open.
-/

#check min_le_right -- min a b ≤ b

example (a : ℝ) : 0<a → 0<√a := by apply Real.sqrt_pos_of_pos

example (a b c :ℝ) : a * b / c = a * (b/c) := by apply mul_div_assoc

@[autogradedProof 9]
theorem problem1 (a b : ℝ) : IsOpenSet (Set.Ioo a b) := by
  sorry
  done


-- ============================================================================
-- Problem 2: Sequence → closure point (forward direction)
-- ============================================================================

/-
If a sequence `a : ℕ → ℝ` takes values in `S` and converges to `x`,
then `x` is a closure point of `S`.
-/

example (a : ℝ) : a ≤ a := le_refl a

@[autogradedProof 7]
theorem problem2 (S : Set ℝ) (x : ℝ) (a : ℕ → ℝ)
    (haS : ∀ n, a n ∈ S) (hconv : ConvergesTo a x) :
    IsClosurePt x S := by
  sorry
  done


-- ============================================================================
-- Problems 3 and 4 : Identity and affine functions are continuous
-- ============================================================================

/-
4 (4 pts): The identity function is continuous at every point.
-/

@[autogradedProof 6]
theorem problem3 (c : ℝ) : ContAt (fun x => x) c := by
  sorry
  done

/-
4 (4 pts): Every affine function `x ↦ m * x + b` is continuous
at every `c`.
-/

@[autogradedProof 8]
theorem problem4 (m b c : ℝ) : ContAt (fun x => m * x + b) c := by
  sorry
  done


-- ============================================================================
-- Problem 5 : Fixed-point theorem via IVT (strict-sign form)
-- ============================================================================

/-
If `f : ℝ → ℝ` is continuous on `[0, 1]` with `0 < f 0` and `f 1 < 1`,
then `f` has a fixed point in `(0, 1)`: some `c ∈ (0, 1)` with `f c = c`.

Hint:
Either apply the Intermediate Value Theorem to a new function you introduce
or (longer) prove it directly via separations and connectedness of `[0, 1]` (L27).
-/

#check IVT -- (f : ℝ → ℝ) → ((a : ℝ) < b) → (∀ c ∈ Set.Icc a b, ContAt f c) → f a < 0 → 0 < f b → ∃ c ∈ Set.Ioo a b, f c = 0
#check sub_eq_zero -- a - b = 0 ↔ a = b

@[autogradedProof 13]
theorem problem5 (f : ℝ → ℝ)
    (hcont : ∀ c ∈ Set.Icc (0 : ℝ) 1, ContAt f c)
    (h0 : 0 < f 0) (h1 : f 1 < 1) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, f c = c := by
  sorry
  done

#check abs_add

-- ============================================================================
-- Problem 6 : Positive continuous functions have a positive lower
-- bound on a closed interval
-- ============================================================================

/-
If `f : ℝ → ℝ` is continuous on `[a, b]` and strictly positive there,
then `f` has a strictly positive lower bound:
there is `m > 0` with `m ≤ f x` for every `x ∈ [a, b]`.

Hint: the minimum half of the Extreme Value Theorem (L29) `evt_min` provides some
`xmin ∈ [a, b]` attaining the minimum of `f`; set `m := f xmin`.
-/

#check evt_min -- (a:ℝ ≤ b) → (∀ c ∈ Icc a b, ContAt f c)
               --  →  ∃ xmin ∈ Icc a b, ∀ x ∈ K, f xmin ≤ f x

@[autogradedProof 7]
theorem problem6 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ∀ c ∈ Set.Icc a b, ContAt f c)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < f x):
    ∃ m > 0, ∀ x ∈ Set.Icc a b, m ≤ f x := by
    sorry
    done
