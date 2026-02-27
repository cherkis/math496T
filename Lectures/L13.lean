import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Data.Int.Basic

/- # Lecture 13: Quotient Types and Modular Arithmetic

New tactics/tools: **Quotient.mk, Quotient.sound, Quotient.exact, Quotient.lift, Quotient.ind, rename_i, congr**
Recall: **unfold, omega, constructor, norm_num, linarith, ring**

## Overview

In Lecture 12 we proved that an equivalence relation partitions a type
into equivalence classes — but those classes were *sets* living inside
the original type.  A **quotient type** goes further: it creates a
genuinely new type whose *elements are* the equivalence classes.

Why does this matter?  Because we can define **functions** on this new
type and prove **properties** about it.  The essential requirement is
**well-definedness**: the result must not depend on which representative
we pick from a class.

Our running example: **ℤ/nℤ**, the integers modulo n.
-/


-- ============================================================================
-- ## Key Definitions (Quotient API)
-- ============================================================================

-- The Quotient API is built into Lean:
#check @Quotient          -- Quotient (s : Setoid α) : Sort u
#check @Quotient.mk       -- sends a : α to its equivalence class
#check @Quotient.sound    -- a ≈ b  →  ⟦a⟧ = ⟦b⟧
#check @Quotient.exact    -- ⟦a⟧ = ⟦b⟧  →  a ≈ b
#check @Quotient.lift     -- lifts f : α → β to the quotient (well-definedness)
#check @Quotient.lift₂    -- lifts a binary function (two-variable well-definedness)
#check @Quotient.ind      -- proves ∀ q, P q by checking ∀ a, P ⟦a⟧

-- Recall from Lecture 12:
#check @Setoid            -- bundles a relation with a proof of Equivalence
#check @Equivalence


-- ============================================================================
-- ## Recall from Lecture 12
-- ============================================================================

def CongMod (n : ℕ) (a b : ℤ) : Prop := (n : ℤ) ∣ (a - b)

theorem congMod_equivalence (n : ℕ) : Equivalence (CongMod n) where
  refl  := by intro a; simp [CongMod]
  symm  := by intro a b ⟨k, hk⟩; exact ⟨-k, by linarith⟩
  trans := by intro a b c ⟨k, hk⟩ ⟨l, hl⟩; exact ⟨k + l, by linarith⟩

instance congModSetoid (n : ℕ) : Setoid ℤ where
  r     := CongMod n
  iseqv := congMod_equivalence n

-- The quotient type: elements of IntMod n *are* residue classes.
-- (We write IntMod to avoid conflict with Mathlib's ZMod.)
abbrev IntMod (n : ℕ) := Quotient (congModSetoid n)


-- ============================================================================
-- ## Part 1: The Quotient Type and Quotient.mk
-- ============================================================================

/-
`Quotient s` is a type! Here `s` is a `Setoid`.
`Quotient.mk s a` sends an element `a : α` to its equivalence class in
The notation `⟦a⟧` is shorthand for `Quotient.mk _ a`
when Lean can infer the setoid from context.

This is the **canonical projection** (or quotient map): the function
  π : ℤ → ℤ/nℤ    defined by    π(a) = [a].
-/

-- Creating elements of IntMod 5:
def bar3  : IntMod 5 := Quotient.mk (congModSetoid 5) 3
def bar3' : IntMod 5 := Quotient.mk _ 3   -- Lean infers the setoid
def bar3'' : IntMod 5 := ⟦3⟧              -- shorthand notation
example : bar3 = bar3' := rfl
example : bar3' = bar3'' := rfl

-- Different integers can represent the same class:
-- 3 and 8 are both in [3] mod 5.  (We prove this in Part 2.)
#check (⟦3⟧ : IntMod 5)
#check (⟦8⟧ : IntMod 5)

-- Every integer gives an element of IntMod n:
example (a : ℤ) : IntMod 5 := ⟦a⟧

-- Exercises (Part 1)

-- (a) Construct the element [2] in IntMod 7:
example : IntMod 7 := sorry

-- (b) Construct [0] in IntMod 3:
example : IntMod 3 := sorry


-- ============================================================================
-- ## Part 2: Quotient.sound and Quotient.exact
-- ============================================================================

/-
The two fundamental facts about equality in a quotient type:

  **Quotient.sound**: if `a ≈ b` then `⟦a⟧ = ⟦b⟧`
    (related elements map to the same class)

  **Quotient.exact**: if `⟦a⟧ = ⟦b⟧` then `a ≈ b`
    (equal classes means the elements are related)

Here `a ≈ b` is notation for `Setoid.r a b`,
which for `congModSetoid n` is `CongMod n a b`.
-/

-- Example: ⟦3⟧ = ⟦8⟧ in IntMod 5  (since 5 ∣ 3 - 8)
example : (⟦3⟧ : IntMod 5) = ⟦8⟧ := by
  apply Quotient.sound
  -- dsimp [HasEquiv.Equiv, congModSetoid,CongMod]
  -- norm_num
  -- dsimp [HasEquiv.Equiv, congModSetoid] -- Can be done with `dsimp` and seeing the abbreviation meaning.
  -- Goal: 3 ≈ 8, i.e. CongMod 5 3 8
  show CongMod 5 3 8
  unfold CongMod
  norm_num

-- Example: ⟦0⟧ = ⟦12⟧ in IntMod 4
example : (⟦0⟧ : IntMod 4) = ⟦12⟧ := by
  apply Quotient.sound
  show CongMod 4 0 12
  unfold CongMod; norm_num

-- Example: extracting the relation from an equality
example (h : (⟦17⟧ : IntMod 5) = ⟦2⟧) : CongMod 5 17 2 :=
  Quotient.exact h

-- Packaging both directions:
theorem intmod_eq_iff (n : ℕ) (a b : ℤ) :
    (⟦a⟧ : IntMod n) = ⟦b⟧ ↔ CongMod n a b := by
    constructor
    apply Quotient.exact
    apply @Quotient.sound _ (congModSetoid n)
    done
  -- ⟨Quotient.exact, fun h => Quotient.sound h⟩

-- Distinct classes: ⟦1⟧ ≠ ⟦2⟧ in IntMod 5
example : (⟦1⟧ : IntMod 5) ≠ ⟦2⟧ := by
  intro h
  have : CongMod 5 1 2 := Quotient.exact h
  -- this : CongMod 5 1 2, i.e. (5 : ℤ) ∣ (1 - 2)
  unfold CongMod at this; norm_num at this

-- Exercises (Part 2)

-- (a) Prove ⟦7⟧ = ⟦2⟧ in IntMod 5:
example : (⟦7⟧ : IntMod 5) = ⟦2⟧ := by
  sorry


-- (b) Prove ⟦0⟧ = ⟦9⟧ in IntMod 3:
example : (⟦0⟧ : IntMod 3) = ⟦9⟧ := by
  sorry

-- (c) Prove ⟦1⟧ ≠ ⟦3⟧ in IntMod 4:
example : (⟦1⟧ : IntMod 4) ≠ ⟦3⟧ := by
  sorry


-- ============================================================================
-- ## Part 3: Quotient.lift — Well-Defined Functions
-- ============================================================================

/-
To define a function `f : Quotient s → β`, we must provide:
  (1) a function `g : α → β` on representatives, and
  (2) a proof that `g` respects the equivalence relation:
      `∀ a b, a ≈ b → g a = g b`

This is the mathematical notion of **well-definedness**: the output
depends only on the class, not on the choice of representative.

`Quotient.lift g proof` is the resulting function on the quotient.
-/

-- Example: is a residue class divisible by 3?
-- We lift the function (fun a => 3 ∣ a) from ℤ to IntMod 3.
def isDivisibleBy3 : IntMod 3 → Prop :=
  Quotient.lift (fun a : ℤ => (3 : ℤ) ∣ a)
    (by
      simp
      -- Must show: CongMod 3 a b → (3 ∣ a) = (3 ∣ b)
      intro a b hab
      -- hab : a ≈ b, which is CongMod 3 a b by definition
      -- dsimp [HasEquiv.Equiv, congModSetoid] at hab
      change CongMod 3 a b at hab
      unfold CongMod at hab
      constructor
      · intro ha; obtain ⟨k, hk⟩ := hab; omega
      · intro hb; obtain ⟨k, hk⟩ := hab; omega)

-- Verify it computes correctly:
example : isDivisibleBy3 ⟦6⟧ := by
  show (3 : ℤ) ∣ 6
  norm_num

example : ¬ isDivisibleBy3 ⟦7⟧ := by
  show ¬ (3 : ℤ) ∣ 7; omega

-- Non-example: absolute value is NOT well-defined on IntMod 5.
-- 3 ≡ -2 (mod 5), but |3| ≠ |-2|.
example : CongMod 5 3 (-2) ∧ |3| ≠ |(-2 : ℤ)| := by
  constructor
  · unfold CongMod; norm_num
  · norm_num

-- Exercises (Part 3)

-- (a) Define a function that checks whether a class in IntMod 2 is even:
def isEvenClass : IntMod 2 → Prop :=
  sorry

-- (b) Verify: isEvenClass ⟦4⟧ holds:
example : isEvenClass ⟦4⟧ := by sorry
-- (c) Show that squaring is NOT well-defined as a function IntMod 3 → ℤ.
-- Find a, b with CongMod 3 a b but a^2 ≠ b^2.
example : ∃ a b : ℤ, CongMod 3 a b ∧ a ^ 2 ≠ b ^ 2 := by
  sorry


-- ============================================================================
-- ## Part 4: Quotient.ind — Proving Properties
-- ============================================================================

/-
To prove `∀ q : Quotient s, P q`, it suffices to prove `∀ a : α, P ⟦a⟧`.
This is because every element of the quotient is of the form `⟦a⟧` for
some representative `a`.

Tactic: `induction' q using Quotient.ind` replaces `q` with `⟦a⟧`.
-/
#check Quotient -- Quotient (s : Setoid α) : Sort u

-- Example: every element of IntMod 2 is ⟦0⟧ or ⟦1⟧.
theorem intmod2_cases (q : IntMod 2) : q = ⟦0⟧ ∨ q = ⟦1⟧ := by
  induction q using Quotient.ind -- better `induction' q using Quotient.ind with a` to get the name `a` for the representative
  rename_i a
  -- Key: reduce to the canonical representative a % 2
  have key : (⟦a⟧ : IntMod 2) = ⟦a % 2⟧ := by
    apply Quotient.sound
    show CongMod 2 a (a % 2)
    exact ⟨a / 2, by omega⟩
  rw [key]
  -- omega knows a % 2 ∈ {0, 1}
  have hrems : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hrems with h | h
  . simp [h]
  . simp [h]

-- Example: the canonical projection is surjective.
theorem mk_surjective (n : ℕ) :
    Function.Surjective (Quotient.mk (congModSetoid n)) := by
  intro q
  induction q using Quotient.ind
  rename_i a
  exact ⟨a, rfl⟩

-- Exercises (Part 4)

-- (a) Prove that every element of IntMod 3 equals ⟦0⟧, ⟦1⟧, or ⟦2⟧:
theorem intmod3_cases (q : IntMod 3) :
    q = ⟦0⟧ ∨ q = ⟦1⟧ ∨ q = ⟦2⟧ := by
       sorry

-- (b) Prove reflexivity via Quotient.ind:
example (n : ℕ) : ∀ q : IntMod n, q = q := by sorry


-- ============================================================================
-- ## Part 5: Addition on ℤ/nℤ — Putting It Together
-- ============================================================================

/-
We now build addition on `IntMod n` from scratch.  The recipe:
  1. Prove that integer addition **respects** congruence mod n.
  2. Use `Quotient.lift₂` to define addition on the quotient.
  3. Use `Quotient.ind` + `congr` + `ring` to prove algebraic properties.
-/

-- Step 1: Addition respects congruence.
theorem congMod_add {n : ℕ} {a₁ b₁ a₂ b₂ : ℤ}
    (h1 : CongMod n a₁ b₁) (h2 : CongMod n a₂ b₂) :
    CongMod n (a₁ + a₂) (b₁ + b₂) := by
  unfold CongMod at *
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨k + l, by linarith⟩

-- Step 2: Define addition on IntMod n.
def IntMod.add (n : ℕ) : IntMod n → IntMod n → IntMod n :=
  Quotient.lift₂ (fun a b : ℤ => (⟦a + b⟧ : IntMod n))
    (by
      intro a₁ a₂ b₁ b₂ h1 h2
      apply Quotient.sound
      exact congMod_add h1 h2)

-- Step 3: Verify it computes correctly.
example : IntMod.add 5 ⟦3⟧ ⟦4⟧ = (⟦7⟧ : IntMod 5) := by rfl

-- Step 4: Prove commutativity.
-- The `congr 1` tactic reduces ⟦expr1⟧ = ⟦expr2⟧ to expr1 = expr2.
theorem IntMod.add_comm (n : ℕ) (a b : IntMod n) :
    IntMod.add n a b = IntMod.add n b a := by
  induction' a using Quotient.ind with p
  induction' b using Quotient.ind with q
  -- rename_i a b
  show (⟦p + q⟧ : IntMod n) = ⟦q + p⟧
  congr 1; ring

-- Step 5: Zero is the right identity.
theorem IntMod.add_zero (n : ℕ) (a : IntMod n) :
    IntMod.add n a ⟦0⟧ = a := by
  induction a using Quotient.ind
  rename_i a
  show (⟦a + 0⟧ : IntMod n) = ⟦a⟧
  congr 1; ring

-- Exercises (Part 5)

-- (a) Verify: ⟦4⟧ + ⟦4⟧ = ⟦3⟧ in IntMod 5  (since 8 ≡ 3 mod 5):
example : IntMod.add 5 ⟦4⟧ ⟦4⟧ = (⟦3⟧ : IntMod 5) := by sorry

-- (b) Prove associativity:
theorem IntMod.add_assoc (n : ℕ) (a b c : IntMod n) :
    IntMod.add n (IntMod.add n a b) c = IntMod.add n a (IntMod.add n b c) := by sorry

-- (c) Prove zero is the left identity:
theorem IntMod.zero_add (n : ℕ) (a : IntMod n) :
    IntMod.add n ⟦0⟧ a = a := by sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Prove ⟦10⟧ = ⟦3⟧ in IntMod 7:
example : (⟦10⟧ : IntMod 7) = ⟦3⟧ := by sorry

-- (2) Prove ⟦-1⟧ = ⟦4⟧ in IntMod 5:
example : (⟦-1⟧ : IntMod 5) = ⟦4⟧ := by sorry

-- (3) Prove ⟦0⟧ ≠ ⟦1⟧ in IntMod 3:
example : (⟦0⟧ : IntMod 3) ≠ ⟦1⟧ := by sorry

-- (4) Use Quotient.exact to extract a divisibility statement:
example (h : (⟦17⟧ : IntMod 5) = ⟦2⟧) : CongMod 5 17 2 := by sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Prove that congruence mod n respects negation:
theorem congMod_neg {n : ℕ} {a b : ℤ} (h : CongMod n a b) :
    CongMod n (-a) (-b) := by sorry

-- (6) Define negation on IntMod n using Quotient.lift:
def IntMod.neg (n : ℕ) : IntMod n → IntMod n :=
  Quotient.lift (fun a : ℤ => (⟦-a⟧ : IntMod n))
    (by
      intro a b hab
      apply Quotient.sound
      exact congMod_neg hab)

-- (7) Verify: IntMod.neg 5 ⟦3⟧ = ⟦2⟧  (since -3 ≡ 2 mod 5):
example : IntMod.neg 5 ⟦3⟧ = (⟦2⟧ : IntMod 5) := by sorry

-- (8) Prove the additive inverse property:
theorem IntMod.add_neg (n : ℕ) (a : IntMod n) :
    IntMod.add n a (IntMod.neg n a) = ⟦0⟧ := by sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (9) Prove that congruence mod n respects multiplication.
-- Hint: use the identity a₁ * a₂ - b₁ * b₂ = a₁ * (a₂ - b₂) + (a₁ - b₁) * b₂.
theorem congMod_mul {n : ℕ} {a₁ b₁ a₂ b₂ : ℤ}
    (h1 : CongMod n a₁ b₁) (h2 : CongMod n a₂ b₂) :
    CongMod n (a₁ * a₂) (b₁ * b₂) := by sorry

-- (10) Define multiplication on IntMod n:
def IntMod.mul (n : ℕ) : IntMod n → IntMod n → IntMod n :=
  Quotient.lift₂ (fun a b : ℤ => (⟦a * b⟧ : IntMod n))
    (by
      intro a₁ a₂ b₁ b₂ h1 h2
      apply Quotient.sound
      exact congMod_mul h1 h2)

-- (11) Prove commutativity of multiplication:
theorem IntMod.mul_comm (n : ℕ) (a b : IntMod n) :
    IntMod.mul n a b = IntMod.mul n b a := by sorry

-- (12) Prove ⟦1⟧ is the multiplicative identity:
theorem IntMod.mul_one (n : ℕ) (a : IntMod n) :
    IntMod.mul n a ⟦1⟧ = a := by sorry

-- (13) CHALLENGE: Prove left-distributivity.
theorem IntMod.mul_add (n : ℕ) (a b c : IntMod n) :
    IntMod.mul n a (IntMod.add n b c) =
    IntMod.add n (IntMod.mul n a b) (IntMod.mul n a c) := by sorry
