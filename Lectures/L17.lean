import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Ring.Parity

/- # Lecture 17: The Schröder–Bernstein Theorem and Countability

New tactic: **refine**
Recall: **intro, apply, simp, rw, omega, by_contra**

## Overview

Last time: Cantor's theorem showed some infinities are strictly larger.
Today: the **Schröder–Bernstein theorem** (CSB) — two injections
(one each way) suffice for a bijection, no explicit construction needed.
-/


-- ============================================================================
-- ## Part 1: The Schröder–Bernstein Theorem
-- ============================================================================
/-
**Theorem** (Schröder–Bernstein, 1897):
If there exist injections f : α → β and g : β → α,
then there exists a bijection h : α → β.

In symbols: (α ↪ β) ∧ (β ↪ α) → (α ≃ β).

**Important**: Unlike many existence theorems, CSB does NOT require the
axiom of choice.  The bijection is constructed explicitly.

**The construction** (proof idea for Homework 6):

Given injections f : α → β and g : β → α, partition α into layers:

  A₀ = α \ g(β)           — elements with no g-preimage
  Aₙ₊₁ = (g ∘ f) '' Aₙ     — apply g ∘ f to the previous layer
  A = ⋃ₙ Aₙ                — the union of all layers

Then define:
  h(x) = f(x)      if x ∈ A
  h(x) = g⁻¹(x)   if x ∉ A   (well-defined since x ∈ range(g))

Why this works — three cases for injectivity:
 1. x₁, x₂ ∈ A: h = f on both, and f is injective.
 2. x₁, x₂ ∉ A: h = g⁻¹ on both, and g⁻¹ is injective (since g is).
 3. x₁ ∈ A, x₂ ∉ A: if h(x₁) = h(x₂) = b, then b = f(x₁) and g(b) = x₂.
   So x₂ = g(f(x₁)) ∈ Aₙ₊₁ ⊆ A — contradiction.

The full proof is Homework 6.
-/

/-
### New tactic: `refine`

`refine` is like `exact`, but lets you leave "holes" marked `?_`.
Each hole becomes a new goal.  For instance, `refine ⟨?_, ?_⟩` on a
conjunction splits it into two goals — one per component.
-/

-- We STATE CSB and use it freely; the proof is Homework 6.
theorem schroeder_bernstein {α β : Type*} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h := by
  sorry

-- Quick demo of CSB: |ℕ| = |ℤ| (proved in L16 via explicit bijection,
-- but now trivial via two injections).
example : ∃ h : ℕ → ℤ, Function.Bijective h := by
  refine schroeder_bernstein
    (f := fun n : ℕ => (n : ℤ))
    (g := fun z : ℤ => if z ≥ 0 then (2 * z).toNat else (-2 * z - 1).toNat) ?_ ?_
  · -- Injection ℕ → ℤ: the coercion n ↦ (n : ℤ)
    intro a b h; dsimp only at h; omega -- exact_mod_cast h
  · -- Injection ℤ → ℕ: same idea as zigzag from L16.
    -- z ↦ 2z if z ≥ 0, z ↦ -2z - 1 if z < 0
    intro a b h
    by_cases ha : a ≥ 0 <;> by_cases hb : b ≥ 0
    <;> simp [ha, hb] at h <;> omega


-- Exercises (Part 1)

-- (a) CSB is symmetric: we also get a bijection the other way.
theorem csb_symmetric {α β : Type*} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : β → α, Function.Bijective h := by
  sorry

-- (b) Use `refine` to structure a proof that id is bijective.
example : Function.Bijective (id : α → α) := by
  refine ⟨?_, ?_⟩
  · sorry
  · sorry


-- ============================================================================
-- ## Part 2: The Cantor Pairing Function
-- ============================================================================

/-
The **Cantor pairing function** encodes ℕ × ℕ into ℕ by walking along
successive anti-diagonals (where m + n is constant):

  (0,0) → 0
  (1,0) → 1,  (0,1) → 2
  (2,0) → 3,  (1,1) → 4,  (0,2) → 5
  (3,0) → 6,  (1,2) → 7,  (2,1) → 8,  (0,3) → 9
  ...

The formula:  cantorPair(m, n) = (m + n)(m + n + 1)/2 + n

The key observation: on anti-diagonal s (where m + n = s), the values
range from s(s+1)/2  (when n = 0) to s(s+1)/2 + s  (when n = s).
So knowing the output value tells you both which diagonal you're on
and where on it you are.
-/

def cantorPair : ℕ × ℕ → ℕ := fun ⟨m, n⟩ => (m + n) * (m + n + 1) / 2 + n

-- Verify on small values:
#eval cantorPair (0, 0)  -- 0
#eval cantorPair (1, 0)  -- 1
#eval cantorPair (0, 1)  -- 2
#eval cantorPair (2, 0)  -- 3

/-
### Proving injectivity of cantorPair

The proof has two steps:

**Step A** (same diagonal ⟹ same n):
If m₁ + n₁ = m₂ + n₂ = s, then
  cantorPair(m₁,n₁) = s(s+1)/2 + n₁  and  cantorPair(m₂,n₂) = s(s+1)/2 + n₂.
If these are equal, then n₁ = n₂, hence m₁ = m₂.

**Step B** (equal outputs ⟹ same diagonal):
Suppose cantorPair(m₁,n₁) = cantorPair(m₂,n₂) but s₁ = m₁+n₁ < s₂ = m₂+n₂.
The maximum value on diagonal s₁ is s₁(s₁+1)/2 + s₁ = (s₁+1)(s₁+2)/2 - 1.
The minimum value on diagonal s₂ is s₂(s₂+1)/2.
Since s₂ ≥ s₁+1, we have s₂(s₂+1)/2 ≥ (s₁+1)(s₁+2)/2 > s₁(s₁+1)/2 + s₁.
So the ranges don't overlap — contradiction.

Both steps ultimately reduce to natural-number arithmetic, which `omega`
handles after we unfold the definitions.
-/

-- A useful lemma: the division in cantorPair is exact.
-- On diagonal s, s*(s+1) is always even, so dividing by 2 loses nothing.
theorem cantorPair_formula (m n : ℕ) :
    cantorPair (m, n) = (m + n) * (m + n + 1) / 2 + n := by
  rfl

-- **Step A**: On the same anti-diagonal, cantorPair is determined by n.
theorem cantorPair_same_diag (m₁ n₁ m₂ n₂ : ℕ)
    (hdiag : m₁ + n₁ = m₂ + n₂)
    (hpair : cantorPair (m₁, n₁) = cantorPair (m₂, n₂)) :
    n₁ = n₂ := by
  -- Both sides simplify to s*(s+1)/2 + nᵢ where s = m₁ + n₁ = m₂ + n₂.
  simp only [cantorPair] at hpair
  -- Since the diagonal number is the same, the s*(s+1)/2 terms are equal.
  rw [hdiag] at hpair
  -- So n₁ = n₂.
  omega

-- **Step B**: Equal outputs ⟹ same anti-diagonal.
-- The key arithmetic fact: on diagonal s, cantorPair values satisfy
-- s*(s+1)/2 ≤ cantorPair(m,n) ≤ s*(s+1)/2 + s, where s = m + n.
-- So if s₁ ≠ s₂, the value ranges don't overlap.
theorem cantorPair_same_diag_of_eq (m₁ n₁ m₂ n₂ : ℕ)
    (hpair : cantorPair (m₁, n₁) = cantorPair (m₂, n₂)) :
    m₁ + n₁ = m₂ + n₂ := by
  have hdouble : ∀ m n : ℕ, 2 * cantorPair (m, n) = (m + n) * (m + n + 1) + 2 * n := by
    intro m n
    calc
      2 * cantorPair (m, n)
          = 2 * (((m + n) * (m + n + 1) / 2) + n) := by rfl
      _ = 2 * ((m + n) * (m + n + 1) / 2) + 2 * n := by
        rw [left_distrib]
      _ = (m + n) * (m + n + 1) + 2 * n := by
        rw [Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m + n))]
  have hdbl : (m₁ + n₁) * (m₁ + n₁ + 1) + 2 * n₁ =
      (m₂ + n₂) * (m₂ + n₂ + 1) + 2 * n₂ := by
    simpa only [hdouble m₁ n₁, hdouble m₂ n₂] using
      congrArg (fun t : ℕ => 2 * t) hpair
  have hn₁ : n₁ ≤ m₁ + n₁ := by omega
  have hn₂ : n₂ ≤ m₂ + n₂ := by omega
  -- We use `by_contra` and show the doubled value ranges do not overlap.
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hstrict :
        (m₁ + n₁) * (m₁ + n₁ + 1) + 2 * n₁ <
        (m₂ + n₂) * (m₂ + n₂ + 1) + 2 * n₂ := by
      nlinarith [hlt, hn₁, Nat.zero_le n₂]
    exact (Nat.ne_of_lt hstrict) hdbl
  · have hstrict :
        (m₂ + n₂) * (m₂ + n₂ + 1) + 2 * n₂ <
        (m₁ + n₁) * (m₁ + n₁ + 1) + 2 * n₁ := by
      nlinarith [hgt, hn₂, Nat.zero_le n₁]
    exact (Nat.ne_of_lt hstrict) hdbl.symm

-- **Theorem**: cantorPair is injective.
theorem cantorPair_injective : Function.Injective cantorPair := by
  intro ⟨m₁, n₁⟩ ⟨m₂, n₂⟩ hpair
  -- Step 1: they are on the same diagonal.
  have hdiag := cantorPair_same_diag_of_eq m₁ n₁ m₂ n₂ hpair
  -- Step 2: on the same diagonal, n determines everything.
  have hn := cantorPair_same_diag m₁ n₁ m₂ n₂ hdiag hpair
  -- Step 3: n₁ = n₂ and m₁ + n₁ = m₂ + n₂ imply m₁ = m₂.
  have hm : m₁ = m₂ := by omega
  -- Combine:
  exact Prod.ext hm hn


-- Exercises (Part 2)

-- (a) Verify cantorPair (3, 1) = 11
example : cantorPair (3, 1) = 11 := by native_decide

-- (b) What is the maximum value on anti-diagonal s = 4?
-- It should be cantorPair(4, 0) = 4*5/2 + 0 = 10.
example : cantorPair (4, 0) = 10 := by native_decide

-- (c) Prove: the function n ↦ (n, 0) is injective (the "trivial" pairing).
-- Use this style: introduce, simplify, close with `exact`.
example : Function.Injective (fun n : ℕ => (n, 0)) := by
  sorry


-- ============================================================================
-- ## Part 3: CSB in Action — ℕ × ℕ and ℚ Are Countable
-- ============================================================================

/-
Now we apply CSB together with cantorPair_injective.

For |ℕ| = |ℕ × ℕ|:
  • Injection ℕ → ℕ × ℕ:  n ↦ (n, 0)
  • Injection ℕ × ℕ → ℕ:  cantorPair

For |ℕ| = |ℚ|, we chain injections:
  ℚ → ℤ × ℕ → ℕ × ℕ → ℕ     (each step injective)
and compose with the trivial ℕ → ℚ.
-/

-- The trivial injection:
def natToNatPair : ℕ → ℕ × ℕ := fun n => (n, 0)

theorem natToNatPair_injective : Function.Injective natToNatPair := by
  intro a b h; simp [natToNatPair] at h; exact h

-- **Theorem**: |ℕ| = |ℕ × ℕ|.
theorem nat_prod_equinum : ∃ h : ℕ → ℕ × ℕ, Function.Bijective h :=
  schroeder_bernstein natToNatPair_injective cantorPair_injective

/-
For ℚ, we need an injection ℤ → ℕ (same idea as zagzig from L16)
and an injection ℚ → ℤ × ℕ (explained in the Addendum below).
-/

def intToNat : ℤ → ℕ := fun z =>
  if z ≥ 0 then (2 * z).toNat
  else ((-2 * z - 1)).toNat

theorem intToNat_injective : Function.Injective intToNat := by
  intro a b h
  simp only [intToNat] at h
  by_cases ha : a ≥ 0 <;> by_cases hb : b ≥ 0 <;> simp [ha, hb] at h <;> omega

-- The ℚ → ℤ × ℕ injection (see Addendum for `Rat.ext` explanation):
theorem rat_to_int_nat_inj :
    Function.Injective (fun q : ℚ => (q.num, q.den)) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 (by exact_mod_cast h.2)

theorem nat_to_rat_inj : Function.Injective (fun n : ℕ => (n : ℚ)) := by
    intro a b h; simp at h; exact h

-- **Theorem**: ℚ is countable.
theorem rat_countable : ∃ h : ℕ → ℚ, Function.Bijective h := by
  apply schroeder_bernstein
  · exact nat_to_rat_inj
  · -- Compose: ℚ → ℤ × ℕ → ℕ × ℕ → ℕ
    show Function.Injective (cantorPair ∘ (fun ⟨z, n⟩ => (intToNat z, n)) ∘
      (fun q : ℚ => (q.num, q.den)))
    apply Function.Injective.comp cantorPair_injective
    apply Function.Injective.comp _ rat_to_int_nat_inj
    intro ⟨z₁, n₁⟩ ⟨z₂, n₂⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨intToNat_injective h.1, h.2⟩


-- Exercises (Part 3)

-- (a) Use CSB to prove |ℕ × ℕ| = |ℕ| (bijection the other way):
example : ∃ h : ℕ × ℕ → ℕ, Function.Bijective h := by
  sorry

-- (b) Prove |ℕ| = |ℤ| using CSB:
example : ∃ h : ℕ → ℤ, Function.Bijective h := by
  sorry

-- (c) Prove that the product of two countable types is countable.
theorem countable_product {f : ℕ → α} {g : ℕ → β}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    ∃ h : ℕ → α × β, Function.Bijective h := by sorry


-- ============================================================================
-- ## Addendum: `Rat.ext` and `exact_mod_cast`
-- ============================================================================

/-
We used two Mathlib tools above without explanation.  Let's unpack them.

**`Rat.ext`**: Two rationals are equal iff their (reduced) numerators and
denominators agree.  The Lean signature is roughly:

  Rat.ext : q₁.num = q₂.num → q₁.den = q₂.den → q₁ = q₂

(The actual Mathlib signature may use `Nat.cast` for the denominator
comparison; `exact_mod_cast` handles the conversion.)

**`exact_mod_cast`**: Lean distinguishes between ℕ, ℤ, ℚ, etc.  When you
have `h : (a : ℕ) = (b : ℕ)` but need `(a : ℤ) = (b : ℤ)` (or vice versa),
`exact_mod_cast h` automatically inserts or removes coercions.

Think of `exact_mod_cast` as "`exact`, but smart about number type casts."
-/

-- **Example**: Two rationals with the same numerator and denominator are equal.
example (q₁ q₂ : ℚ) (hnum : q₁.num = q₂.num) (hden : q₁.den = q₂.den) :
    q₁ = q₂ := by
  exact Rat.ext hnum (by exact_mod_cast hden)

-- **Example**: `exact_mod_cast` bridges ℕ and ℤ coercions.
example (a b : ℕ) (h : (a : ℤ) = (b : ℤ)) : a = b := by
  exact_mod_cast h

-- Recall that in Part 3, `rat_to_int_nat_inj` used both tools:
--   exact Rat.ext h.1 (by exact_mod_cast h.2)
-- `Rat.ext` consumed the numerator equality directly;
-- `exact_mod_cast` bridged the ℕ vs cast comparison for the denominator.


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Use `exact_mod_cast` to prove:
example (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) : m = n := by
  sorry

-- (2) Verify cantorPair (0, 3) = 9:
example : cantorPair (0, 3) = 9 := by native_decide


-- ============================================================================
-- ### Core
-- ============================================================================

-- (3) Prove that (· ∘ f) is injective when f is bijective.
-- Use `refine` to set up the proof structure.
theorem comp_right_injective {f : α → β} (hf : Function.Bijective f) :
    Function.Injective (fun g : β → γ => g ∘ f) := by sorry

-- (4) Prove |ℕ → Bool| = |ℤ → Bool| using CSB.
theorem nat_bool_eq_int_bool :
    ∃ h : (ℕ → Bool) → (ℤ → Bool), Function.Bijective h := by
  sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (5) Prove: |(ℕ → Bool)| = |ℕ → (ℕ → Bool)|.
-- Hint: injection s ↦ (fun _ => s), and the reverse uses Cantor pairing.
theorem seq_of_seq_equinum :
    ∃ h : (ℕ → Bool) → (ℕ → (ℕ → Bool)), Function.Bijective h := by sorry
