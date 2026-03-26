import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/- # Lecture 19: Unique Existence and Chosen Witnesses

New concepts: `∃!`, `Classical.choose`, `Classical.choose_spec`, `noncomputable`
Recall: **use, constructor, intro, rcases, rw, simp, calc, exact, apply, omega, linarith, nlinarith**

## Overview

Today we focus on statements of the form `∃! x, P x`, which formalize
phrases like "the identity", "the solution", or "the chosen preimage."
We will practice:
 1. Proving unique-existence statements
 2. Using uniqueness to compare different witnesses
 3. Extracting witnesses with `Classical.choose`
 4. Building functions from existence proofs

The notes below keep the tutorial structure: worked examples first,
then exercises and challenge problems.
-/

/-
The remainder of these notes is organized in the tutorial style: brief
explanations, worked examples, exercises, and then challenge problems.

## Why `∃!` matters

In mathematics, we constantly say "the" — the identity element, the inverse,
the solution.  Each use of "the" is really a claim of unique existence.
When we write "let e be *the* identity of a group," we are asserting
`∃! e, ∀ g, e * g = g ∧ g * e = g`.  Without uniqueness, we could only
say "*an* identity" — and we would not know that two independently found
identities are the same.

## The definition

`∃! x, P x` unfolds to `∃ x, P x ∧ ∀ y, P y → y = x`.

To *prove* `∃! x, P x`, use `use witness` then prove two goals:
 • the property holds for the witness
 • any element satisfying the property equals the witness

To *use* a hypothesis `h : ∃! x, P x`, destructure with
  `rcases h with ⟨x, hx_prop, hx_uniq⟩`
getting `hx_prop : P x` and `hx_uniq : ∀ y, P y → y = x`.

For `Classical.choose`, keep two cases separate:
 • if `hEx : ∃ x, P x`, then `Classical.choose hEx` is a witness and
   `Classical.choose_spec hEx` proves the property
 • if `h : ∃! x, P x`, then `Classical.choose h` is the unique witness and
   `Classical.choose_spec h` packages both the property and uniqueness
-/


-- ============================================================================
-- ## Section 1: Proving `∃!` — Existence and Uniqueness
-- ============================================================================

/-
The basic pattern: `use witness; constructor; · prove property; · prove uniqueness`.
-/

-- **Worked example 1**: The additive identity of ℤ is unique.
-- This is why we say "THE zero" rather than "A zero."
example : ∃! e : ℤ, ∀ n : ℤ, e + n = n := by
  use 0
  constructor
  · -- 0 is an additive identity
    intro n; ring
  · -- any additive identity must be 0
    intro e' he'
    -- specialize he' to n = 0:
    have := he' 0
    rw [add_zero] at this
    exact this

-- **Alternative shorter proof**:
example : ∃! e : ℤ, ∀ n : ℤ, e + n = n := by
  refine ⟨0, by intro n; simp, ?_⟩
  intro e he
  simpa using he 0

-- **Worked example 2**: The equation 2x = 10 has a unique solution in ℕ.
example : ∃! x : ℕ, 2 * x = 10 := by
  use 5
  constructor
  · rfl
  · intro y hy; omega

-- **Alternative shorter proof**:
example : ∃! x : ℕ, 2 * x = 10 := by
  refine ⟨5, by norm_num, ?_⟩
  intro y hy
  omega


-- **Exercise 1.1**: The equation n + 7 = 10 has a unique solution in ℕ.
example : ∃! n : ℕ, n + 7 = 10 := by
  sorry

-- **Exercise 1.2**: The multiplicative identity of ℤ is unique.
-- (Why we say "the one.")
example : ∃! e : ℤ, ∀ n : ℤ, e * n = n := by
  sorry

-- **Exercise 1.3**: There is a unique integer n with n² = 0.
-- (Hint: `n ^ 2 = 0` in ℤ forces `n = 0`. Try `nlinarith` or `omega`.)
example : ∃! n : ℤ, n ^ 2 = 0 := by
  sorry

-- **Exercise 1.4**: There is a unique natural number n with n < 1.
example : ∃! n : ℕ, n < 1 := by
  sorry


-- ============================================================================
-- ## Section 2: Using `∃!` — Destructuring Hypotheses
-- ============================================================================

/-
When you *have* `h : ∃! x, P x`, you can extract three things:
 • the witness `x`
 • the property `hx : P x`
 • uniqueness `huniq : ∀ y, P y → y = x`

Pattern: `rcases h with ⟨x, hx, huniq⟩`

The uniqueness part is a powerful tool: it lets you *identify* any
element satisfying P with the witness.

A useful pattern is to compare your target to a canonical witness that
you already understand.
-/

-- **Worked example**: Uniqueness of the additive identity (using the hypothesis).
-- We are *given* that the identity is unique, and we extract the three parts.
example (h : ∃! e : ℤ, ∀ n, e + n = n) :
    ∀ a, (∀ n : ℤ, a + n = n) → a = 0 := by
  intro a ha
  rcases h with ⟨e, he, huniq⟩
  have h0 : ∀ n : ℤ, 0 + n = n := by
    intro n
    simp
  calc
    a = e := huniq a ha
    _ = 0 := by
      symm
      exact huniq 0 h0

-- **Alternative shorter proof**:
example (h : ∃! e : ℤ, ∀ n, e + n = n) :
    ∀ a, (∀ n : ℤ, a + n = n) → a = 0 := by
  intro a ha
  rcases h with ⟨e, _, huniq⟩
  calc
    a = e := huniq a ha
    _ = 0 := by
      symm
      exact huniq 0 (by simp)

-- Try this compare-to-a-canonical-witness approach yourself:

-- **Exercise 2.1**: Extract the witness and prove it equals 4.
example (h : ∃! n : ℕ, n * n = 16 ∧ n < 10) : ∀ m, m * m = 16 ∧ m < 10 → m = 4 := by
  sorry

-- **Exercise 2.2**: If ∃! x, 3 * x = 12, then the witness is positive.
example (h : ∃! x : ℕ, 3 * x = 12) : ∀ x, 3 * x = 12 → x > 0 := by
  sorry

-- **Exercise 2.3**: If ∃! e, ∀ n, e + n = n (over ℤ), then e ≤ 0.
-- (The unique additive identity is 0, which satisfies 0 ≤ 0.)
example (h : ∃! e : ℤ, ∀ n, e + n = n) :
    ∀ e, (∀ n : ℤ, e + n = n) → e ≤ 0 := by
  sorry


-- ============================================================================
-- ## Section 3: The Equality Pattern
-- ============================================================================

/-
The most important technique with `∃!`: if two elements both satisfy P,
and P has a unique solution, then the two elements are equal.

Pattern:
  Given `h : ∃! x, P x`, `ha : P a`, `hb : P b`,
  conclude `a = b` by:
    `rcases h with ⟨x, _, huniq⟩`
    `have : a = x := huniq a ha`
    `have : b = x := huniq b hb`
    then chain the equalities.

This is why uniqueness matters in algebra: it lets us prove that
independently constructed objects are the same.
-/

-- **Worked example**: Two additive identities must agree.
-- This is a fundamental algebraic fact: the proof that "the" identity
-- is well-defined.  The key step is still uniqueness: both a and b must
-- equal the same witness e.
example (h : ∃! e : ℤ, ∀ n, e + n = n)
    (a b : ℤ) (ha : ∀ n : ℤ, a + n = n) (hb : ∀ n : ℤ, b + n = n) :
    a = b := by
  rcases h with ⟨e, _, huniq⟩
  calc
    a = e := huniq a ha
    _ = b := (huniq b hb).symm

-- **Worked example**: Two fixed points of a function with a unique
-- fixed point must be equal.  Again, the whole argument is that both
-- points satisfy the same uniquely characterizing property.
example (f : ℤ → ℤ) (h : ∃! x, f x = x)
    (a b : ℤ) (ha : f a = a) (hb : f b = b) : a = b := by
  rcases h with ⟨x, _, huniq⟩
  calc
    a = x := huniq a ha
    _ = b := (huniq b hb).symm


-- **Exercise 3.1**: Unique right identity.
-- If there is a unique e with ∀ n, n * e = n, and both a and b satisfy
-- this, then a = b.
example (h : ∃! e : ℤ, ∀ n, n * e = n)
    (a b : ℤ) (ha : ∀ n : ℤ, n * a = n) (hb : ∀ n : ℤ, n * b = n) :
    a = b := by
  sorry

-- **Exercise 3.2**: Unique divisor.
-- If there is a unique d : ℕ with d ∣ 6 ∧ d > 4, and both a and b
-- satisfy this, then a = b.
example (h : ∃! d : ℕ, d ∣ 6 ∧ d > 4) (a b : ℕ)
    (ha : a ∣ 6 ∧ a > 4) (hb : b ∣ 6 ∧ b > 4) : a = b := by
  sorry

-- **Exercise 3.3**: Use uniqueness to derive a consequence.
-- If g has a unique zero, and both a and b are zeros of g, then
-- `g (a + b) = g (2 * a)`.
-- (Hint: first show `a = b` using uniqueness, then rewrite `a + b`.)
example (g : ℤ → ℤ) (h : ∃! x, g x = 0)
    (a b : ℤ) (ha : g a = 0) (hb : g b = 0) : g (a + b) = g (2 * a) := by
  sorry


-- ============================================================================
-- ## Section 4: `∃!` and `Classical.choose`
-- ============================================================================

/-
`Classical.choose` extracts a witness from an existential statement.
With `∃!`, it becomes especially useful because the chosen witness is
forced to be *the* witness.

If `hEx : ∃ x, P x`, then:
 • `Classical.choose hEx` is a witness
 • `Classical.choose_spec hEx` proves `P (Classical.choose hEx)`

If `h : ∃! x, P x`, then it is often cleaner to choose from `h` itself:
 • `Classical.choose h` is the unique witness
 • `(Classical.choose_spec h).1` is the property
 • `(Classical.choose_spec h).2` is the uniqueness statement

Key fact: if you independently find `c` with `P c`, then
  `c = Classical.choose h`
because uniqueness forces them to agree.
-/

-- **Worked example**: The chosen witness for ∃! n, n + 3 = 5 must be 2.
example (h : ∃! n : ℕ, n + 3 = 5) : Classical.choose h = 2 := by
  -- The spec gives us both the property and uniqueness:
  have hspec := Classical.choose_spec h
  -- hspec.1 : Classical.choose h + 3 = 5
  omega

-- **Worked example**: Any independently found witness equals the chosen one.
example (h : ∃! n : ℕ, n + 3 = 5) (c : ℕ) (hc : c + 3 = 5) :
    c = Classical.choose h := by
  exact (Classical.choose_spec h).2 c hc


-- **Exercise 4.1**: The chosen witness for ∃! n, 2 * n = 14 must be 7.
example (h : ∃! n : ℕ, 2 * n = 14) : Classical.choose h = 7 := by
  sorry

-- **Exercise 4.2**: If g is injective and x ∈ Set.range g, the unique
-- preimage extracted by Classical.choose satisfies g (choose hx) = x.
-- (This is `Classical.choose_spec` — verify you understand the types.)
section ExChoose42
open Classical
variable {α β : Type*}

example (g : β → α) (x : α) (hx : x ∈ Set.range g) :
    g (Classical.choose hx) = x := by
  sorry

end ExChoose42

-- **Exercise 4.3**: If ∃! b, g b = x (unique preimage under injection),
-- and we know g c = x, then c must be the chosen witness.
section ExChoose43
open Classical
variable {α β : Type*}

example (g : β → α) (x : α) (h : ∃! b, g b = x) (c : β) (hc : g c = x) :
  c = Classical.choose h := by
  sorry

end ExChoose43


-- ============================================================================
-- ## Section 4b: Functions Defined via `Classical.choose`
-- ============================================================================

/-
The payoff of `Classical.choose` is building actual *functions* from
existence proofs.  These functions are `noncomputable` — Lean cannot
execute them — but we can reason about them just fine.

In this section we are back to ordinary `∃` statements, so
`Classical.choose_spec` gives exactly the defining property we need.

The pattern:
 1. Define `f x := Classical.choose (proof that ∃ y, P x y)`
 2. The spec `Classical.choose_spec (...)` gives `P x (f x)`
 3. Use the spec to prove properties of f.
-/

-- **Worked example**: A right inverse of a surjection.
-- Given f surjective (∀ b, ∃ a, f a = b), define g(b) = some preimage of b.
section RightInvDemo
open Classical
variable {α β : Type*}

noncomputable def rInv (f : α → β) (hf : Function.Surjective f) : β → α :=
  fun b => Classical.choose (hf b)

-- The key property: f (rInv f hf b) = b.
-- Proof: just unfold and apply Classical.choose_spec.
theorem rInv_spec (f : α → β) (hf : Function.Surjective f) (b : β) :
    f (rInv f hf b) = b := by
  exact Classical.choose_spec (hf b)

-- Using the spec to prove f ∘ rInv = id:
theorem rInv_right_inverse (f : α → β) (hf : Function.Surjective f) :
    ∀ b, f (rInv f hf b) = b := by
  intro b
  exact rInv_spec f hf b

end RightInvDemo


-- **Exercise 4b.1**: Define a left inverse of an injection.
-- If g is injective, define lInv on the range of g using Classical.choose,
-- and send everything outside the range to a default element.
-- Then prove the key property: lInv (g b) = b for all b.
section ExLeftInv
open Classical
variable {α β : Type*}

noncomputable def lInv (g : β → α) (_hg : Function.Injective g)
    [Nonempty β] : α → β :=
  fun x => if hx : x ∈ Set.range g
    then Classical.choose hx
    else Classical.arbitrary β

-- Prove: lInv sends g(b) back to b.
-- Hint: first prove `hx : g b ∈ Set.range g`.  After `simp [lInv, hx]`,
-- the remaining goal is an equality in β.  Use injectivity to reduce it
-- to `g (Classical.choose hx) = g b`, then finish with `Classical.choose_spec`.
theorem lInv_spec (g : β → α) (hg : Function.Injective g)
    [Nonempty β] (b : β) :
    lInv g hg (g b) = b := by
  sorry

end ExLeftInv


-- **Exercise 4b.2**: A "square root" function on ℕ via choose.
-- Given: every perfect square has a square root.
-- Define `sqrtOf` on perfect squares and prove its defining property.
section ExSqrt
open Classical

-- We take as given that n is a perfect square:
noncomputable def sqrtOf (n : ℕ) (hn : ∃ k, k * k = n) : ℕ :=
  Classical.choose hn

-- Prove the defining property.
-- Hint: this is exactly `Classical.choose_spec hn`, after unfolding `sqrtOf`.
theorem sqrtOf_spec (n : ℕ) (hn : ∃ k, k * k = n) :
    (sqrtOf n hn) * (sqrtOf n hn) = n := by
  sorry

end ExSqrt


-- **Exercise 4b.3**: A selection function on a family of nonempty sets.
-- Given a family of nonempty sets S : ι → Set α, define a function
-- that picks one element from each S i.
section ExSelection
open Classical
variable {α ι : Type*}

noncomputable def selectFrom (S : ι → Set α) (hS : ∀ i, ∃ x, x ∈ S i) :
    ι → α :=
  fun i => Classical.choose (hS i)

-- Prove: the selected element is in the set.
-- Hint: apply `Classical.choose_spec` to the existence proof `hS i`.
theorem selectFrom_mem (S : ι → Set α) (hS : ∀ i, ∃ x, x ∈ S i) (i : ι) :
    selectFrom S hS i ∈ S i := by
  sorry

end ExSelection


-- ============================================================================
-- ## Section 5: Challenge Problems
-- ============================================================================

/-
These problems combine multiple techniques from the tutorial.
In each case, try to identify the main pattern first:
 prove `∃!`, compare two witnesses, or read information off `Classical.choose_spec`.
-/

-- **Challenge 1**: Prove ∃! and then use it.
-- There is a unique natural number that is both prime and even.
-- (You may use `Nat.Prime` and `Even`.  The witness is 2.)
-- Hint: use `2` as the witness.  For uniqueness, apply
-- `Nat.Prime.eq_two_of_even` to any prime even number.  `norm_num` can
-- verify the witness properties.
example : ∃! p : ℕ, Nat.Prime p ∧ Even p := by
  sorry

-- **Challenge 2**: Unique preimage under an injective function.
-- Prove the full statement: injection + membership in range → ∃!.
-- Then use that theorem, or the same uniqueness pattern directly, to show
-- that two preimages of the same x agree.
section Challenge2
variable {α β : Type*}

theorem unique_preimage' (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) : ∃! b : β, g b = x := by
  sorry

theorem preimages_agree (g : β → α) (hg : Function.Injective g)
    (x : α) (b₁ b₂ : β) (h₁ : g b₁ = x) (h₂ : g b₂ = x) : b₁ = b₂ := by
  sorry

end Challenge2

-- **Challenge 3**: Turn existence into unique existence.
-- If f : ℤ → ℤ satisfies |f(a) - f(b)| < |a - b| for all a ≠ b,
-- then f has at most one fixed point.  Combine that uniqueness argument
-- with a given fixed point to prove an `∃!` statement.
-- Hint: after choosing a fixed point x, assume y is another one.  If
-- `x ≠ y`, the contraction hypothesis gives `|x - y| < |x - y|`, which is impossible.
example (f : ℤ → ℤ)
  (hcontract : ∀ a b : ℤ, a ≠ b → |f a - f b| < |a - b|)
  (hfix : ∃ x : ℤ, f x = x) :
  ∃! x : ℤ, f x = x := by
  sorry

-- **Challenge 4**: Compose uniqueness.
-- If ∃! x, P x and ∃! y, Q y, and the unique x satisfying P also
-- satisfies Q, then x = the unique y satisfying Q.
-- Hint: the property `Q x` lets you apply the uniqueness part of
-- `Classical.choose_spec hQ` directly.
example {α : Type*} (P Q : α → Prop)
  (_hP : ∃! x, P x) (hQ : ∃! y, Q y)
  (x : α) (_hx : P x) (hxQ : Q x) :
  x = Classical.choose hQ := by
  sorry
