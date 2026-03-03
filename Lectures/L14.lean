import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Ring.Parity

/- # Lecture 14: Functions — Injectivity, Surjectivity, and Composition

New tactic: **funext**  (function extensionality)
Preview: **choose, aesop**  (used more heavily in the next lecture)
Recall: **intro, apply, use, obtain, ext, simp, constructor, rw, calc, omega, norm_num, ring, linarith**

## Overview

A **function** f : α → β assigns to each element of α exactly one element
of β.  This is the most fundamental notion.

Today we study three central properties:
  • **Injective**: different inputs give different outputs
  • **Surjective** (onto): every element of the codomain is hit
  • **Bijective**: both injective and surjective

We also study **composition** and prove that these properties are
preserved under composition.

For now, the key message: **injectivity, surjectivity, and bijectivity** are
the tools that let us compare the "sizes" of sets.
-/


-- ============================================================================
-- ## Key Definitions (Mathlib)
-- ============================================================================

-- The core definitions live in the `Function` namespace:
#check @Function.Injective   -- ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
#check @Function.Surjective  -- ∀ b, ∃ a, f a = b
#check @Function.Bijective   -- Injective f ∧ Surjective f

-- Composition:
#check @Function.comp        -- (β → γ) → (α → β) → (α → γ)
-- In Lean, `g ∘ f` is notation for `Function.comp g f`.

-- Identity:
#check @id                   -- α → α

-- Function extensionality:
-- Two functions are equal iff they agree on every input.
#check @funext               -- (∀ x, f x = g x) → f = g


-- ============================================================================
-- ## Part 1: Functions — The Basics
-- ============================================================================

/-
In Lean, a function `f : α → β` is a primitive concept — it's a term of
function type.  The **domain** is `α`, the **codomain** is `β`.

**Important distinction**: the **codomain** is part of the type of f.
The **range** (or image) is `Set.range f = { b : β | ∃ a, f a = b }`,
which may be a proper subset of the codomain.

Example: `f : ℤ → ℤ` given by `f(n) = n²` has codomain ℤ, but its
range is only the set of perfect squares {0, 1, 4, 9, 16, ...}.
-/

-- Range of a function:
#check @Set.range  -- {b | ∃ a, f a = b}

-- Example: the range of (· + 1) on ℕ is the positive naturals
example : Set.range (fun n : ℕ => n + 1) = { m : ℕ | 0 < m } := by
  ext m
  simp [Set.mem_range]
  done

-- Function extensionality: two functions are equal iff they agree on all inputs.
-- This is the tactic `funext`.
example : (fun n : ℕ => n + 0) = id := by
  funext n
  dsimp [id]

-- A more algebraic example:
example : (fun n : ℤ => n * 1 + 0) = id := by
  funext n
  dsimp [id]
  ring


-- Exercises (Part 1)

-- (a) Prove that `f: ℕ → ℕ: n ↦ 2 * n` and `f: ℕ → ℕ: n ↦  n + n` are the same function:
example : (fun n : ℕ => 2 * n) = (fun n : ℕ => n + n) := by
  sorry

-- (b) Prove that 0 is in the range of `f:ℤ → ℤ: n ↦ 3 * n`:
example : (0 : ℤ) ∈ Set.range (fun n : ℤ => 3 * n) := by
  sorry

-- (c) Prove that 5 is NOT in the range of `f: ℕ → ℕ: n ↦ 2 * n`:
example : (5 : ℕ) ∉ Set.range (fun n : ℕ => 2 * n) := by
  sorry


-- ============================================================================
-- ## Part 2: Injectivity
-- ============================================================================

/-
A function `f : α → β` is **injective** (one-to-one) if
  ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂.
Different inputs always give different outputs.

The **contrapositive** is often more intuitive:
  a₁ ≠ a₂ → f a₁ ≠ f a₂.
-/

-- Example: the function n ↦ n + 3 is injective on ℕ
example : Function.Injective (fun n : ℕ => n + 3) := by
  -- dsimp [Function.Injective]
  intro a b h
  -- h : a + 3 = b + 3
  simp at h
  exact h

-- Example: the function n ↦ 2n + 1 is injective on ℤ
example : Function.Injective (fun n : ℤ => 2 * n + 1) := by
  intro a b h
  -- h : 2 * a + 1 = 2 * b + 1
  linarith

-- Non-example: the function n ↦ n² is NOT injective on ℤ
-- because f(1) = f(-1) = 1 but 1 ≠ -1.
example : ¬ Function.Injective (fun n : ℤ => n ^ 2) := by
  intro h
  dsimp [Function.Injective] at h
  -- h says: for all a b, a² = b² → a = b.
  -- Specialize to 1 and -1:
  have : (1 : ℤ) = -1 := h (by norm_num) -- : (1 : ℤ) ^ 2 = (-1) ^ 2)
  -- we did not name this hypothesis, so Lean called it `this`!
  norm_num at this

/-
Note: n ↦ n² IS injective on ℕ (since there are no negatives),
but NOT on ℤ.  Injectivity depends on the domain!

This is easy to see: if a² = b² with a, b ∈ ℕ,
then (a - b)(a + b) = 0.  Since a + b ≥ 0 and a, b ≥ 0, we get a = b.
On ℤ the factorization (a - b)(a + b) = 0 allows a = -b ≠ a.
-/


-- Exercises (Part 2)

-- (a) Prove that `f: ℤ → ℤ : n ↦ 5 * n - 3` is injective:
example : Function.Injective (fun n : ℤ => 5 * n - 3) := by
  sorry

-- (b) Prove that `f: ℕ → ℕ: n ↦ 3 * n` is injective:
example : Function.Injective (fun n : ℕ => 3 * n) := by
  sorry

-- (c) Show that the constant function is NOT injective (when there's more
-- than one element). We prove it fails by finding a counterexample.
example : ¬ Function.Injective (fun _ : ℕ => (0 : ℕ)) := by
  sorry

-- (d) Show that `f: ℤ → ℤ : n ↦ n % 3` is NOT injective:
example : ¬ Function.Injective (fun n : ℤ => n % 3) := by
  sorry


-- ============================================================================
-- ## Part 3: Surjectivity
-- ============================================================================

/-
A function `f : α → β` is **surjective** (onto) if
  ∀ b : β, ∃ a : α, f a = b.

Every element of the codomain is the image of some element of the domain.
-/

-- Example: the function n ↦ n + 1 is surjective on ℤ
-- (Given any b : ℤ, use witness a = b - 1.)
example : Function.Surjective (fun n : ℤ => n + 1) := by
  intro b
  use b - 1
  ring

-- Example: the function n ↦ 2n is surjective on ℤ? NO!
-- 1 is not in the range (no integer n satisfies 2n = 1).
example : ¬ Function.Surjective (fun n : ℤ => 2 * n) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  -- hn : 2 * n = 1
  simp at hn
  omega

-- Example: the function n ↦ n + 1 is NOT surjective on ℕ
-- because 0 is not in the range.
example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  dsimp at hn
  omega

/-
**Key observation**: the SAME formula can be surjective or not depending
on the domain and codomain!
  • n ↦ n + 1 from ℤ to ℤ: surjective (witness: b - 1)
  • n ↦ n + 1 from ℕ to ℕ: NOT surjective (0 has no preimage)
-/


-- Exercises (Part 3)

-- (a) Prove that `f: ℤ → ℤ : n ↦ n - 7` is surjective:
example : Function.Surjective (fun n : ℤ => n - 7) := by
  sorry

-- (b) Prove that `f: ℤ → ℤ : n ↦ 3 * n + 2` is NOT surjective:
-- (Hint: can you hit 0? What would n have to be?)
example : ¬ Function.Surjective (fun n : ℤ => 3 * n + 2) := by
  sorry

-- (c) The identity function is surjective:
example : Function.Surjective (id : ℕ → ℕ) := by
  sorry

-- (d) Challenge: Show that `f: ℕ → ℕ : n ↦ n / 2` is surjective.
-- (Here / is natural number division, so 0/2 = 0, 1/2 = 0, 2/2 = 1, 3/2 = 1, ...)
-- Hint: what witness should you use for a given b?
example : Function.Surjective (fun n : ℕ => n / 2) := by
  sorry


-- ============================================================================
-- ## Part 4: Bijectivity
-- ============================================================================

/-
A function `f : α → β` is **bijective** if it is both injective and surjective.

  Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f

A bijection is a **one-to-one correspondence**.

**Galileo's paradox revisited**: The function n ↦ 2n is a bijection
from ℕ to the set of even natural numbers.  So ℕ and the even numbers
have the same "size" — even though one is a proper subset of the other!
This is the hallmark of infinite sets.

**Dedekind's definition of infinity (1888)**: A set is *infinite* if and
only if it admits a bijection with a proper subset of itself.
-/

-- Example: the function n ↦ n + 3 is bijective on ℤ
example : Function.Bijective (fun n : ℤ => n + 3) := by
  constructor
  · -- Injective:
    intro a b h; linarith
  · -- Surjective:
    intro b; use b - 3; ring

-- Non-example: n ↦ n + 1 on ℕ is injective but NOT bijective
-- (it's not surjective, so it can't be bijective)
example : Function.Injective (fun n : ℕ => n + 1) ∧
          ¬ Function.Bijective (fun n : ℕ => n + 1) := by
  constructor
  · intro a b h; simp at h; exact h
  · intro ⟨_, hsurj⟩
    obtain ⟨n, hn⟩ := hsurj 0
    dsimp at hn
    omega


-- Exercises (Part 4)

-- (a) Prove that `f: ℤ → ℤ, n ↦ 1 - n` is bijective:
-- (This is the "reflection" around 1/2.)
example : Function.Bijective (fun n : ℤ => 1 - n) := by
  sorry

-- (b) Prove that `f: ℤ → ℤ, n ↦  2 * n` is NOT bijective:
example : ¬ Function.Bijective (fun n : ℤ => 2 * n) := by
  sorry

-- (c) Prove that `f: ℤ → ℤ, n ↦ 2 * n + 1` is NOT surjective,
-- and conclude it's not bijective:
example : ¬ Function.Bijective (fun n : ℤ => 2 * n + 1) := by
  sorry


-- ============================================================================
-- ## Part 5: Composition of Functions
-- ============================================================================

/-
Given `f : α → β` and `g : β → γ`, the **composition** `g ∘ f : α → γ`
is defined by `(g ∘ f)(x) = g(f(x))`.

In Lean, `g ∘ f` is notation for `Function.comp g f`.

Read `g ∘ f` as "g after f".

**The key theorems** (which we will prove):
  1. Composition of injections is an injection.
  2. Composition of surjections is a surjection.
  3. Composition of bijections is a bijection.

These are tremendously useful: they let us build complex bijections
from simple ones, piece by piece.
-/

-- Example: composing n ↦ n + 1 and n ↦ 2n gives n ↦ 2n + 2
example : (fun n : ℤ => 2 * n) ∘ (fun n : ℤ => n + 1) = (fun n => 2 * n + 2) := by
  funext n
  simp [Function.comp]
  ring

-- Example: composing n ↦ 2n and n ↦ n + 1 gives n ↦ 2n + 1
-- (Composition is NOT commutative in general!)
example : (fun n : ℤ => n + 1) ∘ (fun n : ℤ => 2 * n) = (fun n => 2 * n + 1) := by
  funext n
  simp [Function.comp]

-- Composition with id does nothing:
example (f : α → β) : f ∘ id = f := by
  funext x; rfl

example (f : α → β) : id ∘ f = f := by
  funext x; rfl


-- **Theorem**: Composition of injective functions is injective.
-- This is `Function.Injective.comp` in Mathlib.
theorem inj_comp {f : α → β} {g : β → γ}
    (hg : Function.Injective g) (hf : Function.Injective f) :
    Function.Injective (g ∘ f) := by
  intro a₁ a₂ h
  -- h : g(f(a₁)) = g(f(a₂))
  -- Since g is injective: f(a₁) = f(a₂)
  have h₁ : f a₁ = f a₂ := hg h
  -- Since f is injective: a₁ = a₂
  exact hf h₁

-- **Theorem**: Composition of surjective functions is surjective.
-- This is `Function.Surjective.comp` in Mathlib.
theorem surj_comp {f : α → β} {g : β → γ}
    (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Surjective (g ∘ f) := by
  intro c
  -- Need: ∃ a, g(f(a)) = c
  -- Since g is surjective: ∃ b, g(b) = c
  obtain ⟨b, hb⟩ := hg c
  -- Since f is surjective: ∃ a, f(a) = b
  obtain ⟨a, ha⟩ := hf b
  -- Then g(f(a)) = g(b) = c
  use a
  show g (f a) = c
  rw [ha, hb]

-- **Corollary**: Composition of bijections is a bijection.
theorem bij_comp {f : α → β} {g : β → γ}
    (hg : Function.Bijective g) (hf : Function.Bijective f) :
    Function.Bijective (g ∘ f) := by
  obtain ⟨hg_inj, hg_surj⟩ := hg
  obtain ⟨hf_inj, hf_surj⟩ := hf
  exact ⟨inj_comp hg_inj hf_inj, surj_comp hg_surj hf_surj⟩


-- Exercises (Part 5)

-- (a) Prove that composing n ↦ n + 1 with n ↦ n + 1 gives n ↦ n + 2:
example : (fun n : ℤ => n + 1) ∘ (fun n : ℤ => n + 1) = (fun n => n + 2) := by
  sorry

-- (b) Use inj_comp to prove that `f: ℤ → ℤ, n ↦ 2 * n + 3` is injective,
-- by writing it as a composition:
-- `f = (· + 3) ∘ (2 * ·)`
example : Function.Injective (fun n : ℤ => 2 * n + 3) := by
  sorry

-- (c) Show that if g ∘ f is injective, then f is injective.
-- (We don't need any assumption on g!)
-- This is a very useful "test": to show f is injective, it suffices to
-- find ANY g such that g ∘ f is injective.
theorem inj_of_comp_inj {f : α → β} {g : β → γ}
    (h : Function.Injective (g ∘ f)) : Function.Injective f := by
  sorry

-- (d) Show that if g ∘ f is surjective, then g is surjective.
-- (We don't need any assumption on f!)
theorem surj_of_comp_surj {f : α → β} {g : β → γ}
    (h : Function.Surjective (g ∘ f)) : Function.Surjective g := by
  sorry


-- ============================================================================
-- ## Part 6: Converses and Counterexamples
-- ============================================================================

/-
We proved above:
  • g ∘ f injective  → f injective
  • g ∘ f surjective → g surjective

What about the converses?
  • g ∘ f injective  → g injective?   **FALSE!**
  • g ∘ f surjective → f surjective?  **FALSE!**
-/

-- Counterexample: g ∘ f injective does NOT imply g injective.
-- Strategy: let f land in a "nice" subset of β where g is injective,
-- even though g fails injectivity elsewhere.
-- Here: f(n) = 2n (lands in even numbers), g(n) = n / 2 (integer division).
-- Then g ∘ f = identity (injective!), but g(0) = g(1) = 0 (not injective).
example : ∃ (f g : ℤ → ℤ),
    Function.Injective (g ∘ f) ∧ ¬ Function.Injective g := by
  -- f(n) = 2 * n  (injective, range = even numbers)
  -- g(n) = n / 2   (not injective: g(0) = g(1) = 0)
  -- g ∘ f = n ↦ (2n)/2 = n, which is injective
  use (fun n => 2 * n), (fun n => n / 2)
  constructor
  · intro a b h
    simp [Function.comp] at h
    omega
  · intro h
    have : (0 : ℤ) = 1 := h (show (0 : ℤ) / 2 = 1 / 2 from by norm_num)
    norm_num at this


-- Exercises (Part 6)

-- (a) Provide a counterexample showing g ∘ f surjective does NOT imply f surjective:
example : ∃ (f g : ℤ → ℤ),
    Function.Surjective (g ∘ f) ∧ ¬ Function.Surjective f := by
  sorry

-- (b) Conversely, prove the TRUE statement: if g ∘ f is bijective,
-- then f is injective AND g is surjective.
theorem bij_comp_parts {f : α → β} {g : β → γ}
    (h : Function.Bijective (g ∘ f)) :
    Function.Injective f ∧ Function.Surjective g := by
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Prove `f: ℤ → ℤ, n ↦ -n` is injective:
example : Function.Injective (fun n : ℤ => -n) := by sorry

-- (2) Prove `f: ℤ → ℤ, n ↦ n + 100` is surjective:
example : Function.Surjective (fun n : ℤ => n + 100) := by sorry

-- (3) Prove `f: ℤ → ℤ, n ↦ -n` is bijective:
example : Function.Bijective (fun n : ℤ => -n) := by sorry

-- (4) Composing `f: ℤ → ℤ, n ↦ -n` with itself gives the identity:
example : (fun n : ℤ => -n) ∘ (fun n : ℤ => -n) = id := by sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Prove that `f: ℤ × ℤ → ℤ, p ↦ p.1 + p.2` is surjective:
-- (Given b, what pair (a₁, a₂) maps to it?)
example : Function.Surjective (fun p : ℤ × ℤ => p.1 + p.2) := by sorry

-- (6) Prove that `f: ℤ × ℤ → ℤ, p ↦ p.1 + p.2` is NOT injective:
example : ¬ Function.Injective (fun p : ℤ × ℤ => p.1 + p.2) := by sorry

-- (7) The "swap" function on pairs is bijective:
example : Function.Bijective (fun p : ℤ × ℤ => (p.2, p.1)) := by sorry

-- (8) Prove that if f: α → β is injective and g: α → γ is injective,
-- then α → β × γ: x ↦ (f x, g x) is injective.
-- (This generalizes: injectivity is "preserved by pairing".)

-- Recall
#check Prod.ext_iff -- x = y ↔ x.1 = y.1 ∧ x.2 = y.2

theorem inj_pair {f : α → β} {g : α → γ}
    (hf : Function.Injective f) :
    Function.Injective (fun x => (f x, g x)) := by sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (9) Prove: f is injective if and only if f ∘ g₁ = f ∘ g₂ → g₁ = g₂
-- for all g₁ g₂ : γ → α.
-- (**Injective functions are precisely the "left-cancellable" functions**.)
-- We prove one direction here (the other needs the `choose` tactic from
-- the next lecture).
theorem inj_iff_left_cancel {f : α → β} :
    Function.Injective f →
    ∀ (γ : Type*) (g₁ g₂ : γ → α), f ∘ g₁ = f ∘ g₂ → g₁ = g₂ := by sorry

/- In category theory **injective** and **surjective** maps are called **monic** and **epic** which are defined by
**Monic** : `f ∘ g = f ∘ h ⇒ g = h`
and
**Epic** : `g ∘ f = h ∘ f ⇒ g = h`
-/

-- (10) CHALLENGE: If f ∘ f = f and f is injective, then f = id.
-- (An injective idempotent on the same type must be the identity.)
theorem inj_idempotent_is_id {f : α → α}
    (hff : f ∘ f = f) (hinj : Function.Injective f) : f = id := by sorry

-- (11) CHALLENGE: Prove that the "diagonal" function is injective.
-- (This foreshadows Cantor's diagonal argument in Stage 8!)
-- The diagonal function sends a to the constant function (fun _ => a).
theorem diagonal_injective (b : β) :
    Function.Injective (fun a : α => (fun _ : β => a)) := by sorry
