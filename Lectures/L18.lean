import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Countable.Basic

/- # Lecture 18: Constructing Functions from Existence Proofs

New concepts: `Classical.choose`, `Classical.choose_spec`, `∃!`,
  `noncomputable`, `local notation`, `abbrev`,
  implicit vs explicit `variable`, `if h : P then … else …`
Recall: **simp, rcases, intro, apply, use, obtain, omega**

## Overview

In Lecture 15 we proved
- every surjection has a right inverse and
- every injection has a left inverse.
We used the `choose` *tactic* — which works inside proofs.
But what if we want to *define a function* from an existence proof?
For instance, to build the Schröder–Bernstein bijection h, we need
to *define* h(x) = g⁻¹(x) when x ∉ A — and this requires extracting a
witness from the existence proof `∃ b, g b = x`.

Today we learn the tools for this:
 1. `Classical.choose` / `Classical.choose_spec` — extracting witnesses
 2. Lean scaffolding for organizing larger proofs
 3. `∃!` — uniqueness and why it makes `Classical.choose` predictable
 4. Piecewise function definitions via dependent `if`

### An Interesting Fact: When Does a Proof Need the Axiom of Choice?

Felix Bernstein proved the Schröder–Bernstein theorem in 1897 — at age 19.
His proof is *choice free*: it builds the bijection step by step, without
invoking the axiom of choice.  Ernst Schröder published his own proof in
1898, but it was later found to contain a subtle error — and the mistake was
precisely in *how* he extracted witnesses from existence statements.  The
lesson: being explicit about *when* and *how* you turn "there exists" into
"here is one" is not pedantry — it is the difference between a correct
proof and a flawed one.  Today's tools make this distinction precise.
-/


-- ============================================================================
-- ## Part 1: From `choose` (Tactic) to `Classical.choose` (Term)
-- ============================================================================

/-
**The Axiom of Choice**, informally: if for every `x` there exists a `y`
with some property `P(x, y)`, we can simultaneously select one such `y` for
each `x` — obtaining a *function* `x ↦ y`.

In Lecture 15 the `choose` tactic did this inside proofs:
given `h : ∀ x, ∃ y, P x y`, it produced `f : α → β` and `hf : ∀ x, P x (f x)`.

But `choose` only works in *tactic mode* (inside `by ...`).  To **define**
a function as a Lean term, we need `Classical.choose`.

`Classical.choose`: Given a proof `h : ∃ b, P b`, the term
  `Classical.choose h`
is an element of the type of b — a *witness*.

`Classical.choose_spec`: Given the same `h`, the term
  `Classical.choose_spec h`
is a proof of `P (Classical.choose h)` — the *property* of the witness.

**Why `noncomputable`?**  `Classical.choose` uses the axiom of choice —
Lean cannot *compute* the witness, only *reason* about it.  Any definition
using `Classical.choose` must be marked `noncomputable`.
-/

open Classical in
#check @Classical.choose      -- {α : Sort u} → (∃ a:α, p a) → α
#check @Classical.choose_spec -- (h : ∃ a, p a) → p (Classical.choose h)

-- **Worked example**: Building a right inverse of a surjection.
-- In L15 we proved surjections have right inverses using the `choose` tactic.
-- Now we BUILD the right inverse as an actual function definition.

section RightInverse

open Classical

variable {α β : Type*}

noncomputable def rightInv (f : α → β) (hf : Function.Surjective f) : β → α :=
  fun b => Classical.choose (hf b)

-- The defining property: f (rightInv f hf b) = b.
theorem rightInv_spec (f : α → β) (hf : Function.Surjective f) (b : β) :
    f (rightInv f hf b) = b :=
  Classical.choose_spec (hf b)

-- rightInv is indeed a right inverse:
theorem rightInv_is_right_inverse (f : α → β) (hf : Function.Surjective f) :
    Function.RightInverse (rightInv f hf) f := by
  intro b
  exact rightInv_spec f hf b

end RightInverse


-- Exercise (Part 1): Given an injection g, extract a preimage from Set.range g.
-- Fill in the `sorry`.
section ExPart1
open Classical
variable {α β : Type*}

example (g : β → α) (x : α) (hx : x ∈ Set.range g) :
    g (Classical.choose hx) = x := by
  sorry

end ExPart1


-- ============================================================================
-- ## Part 2: Lean Scaffolding for Larger Proofs
-- ============================================================================

/-
As proofs grow (like the Schröder–Bernstein construction in your homework),
we need organizational tools.

`section` / `end`:  A scoping block.  Variables and notations declared
inside disappear at the `end`.

`variable`:  Declares names available throughout the section.
 • `variable {α β : Type*}` — *implicit*: Lean infers α, β from context.
 • `variable (f : α → β)`   — *explicit*: you must pass f to definitions.
   Use explicit when the variable appears in the *statement* of a definition
   (e.g., `A_all f g` in your homework).
 • `variable (hf : Function.Injective f)` — an explicit hypothesis.

`local notation`:  A shorthand that exists only inside the current section.
  `local notation "A" => A_all f g` lets you write `A` instead of `A_all f g`.
  Outside the section, `A` reverts to its usual meaning.  This is how the
  homework file writes `local notation "h" => h_def f g hg`.

`notation` (global) vs `local notation`:  Global notation persists
forever — use it sparingly.  `local notation` is preferred for proofs.

`abbrev` vs `def`:  Both define a name, but `abbrev` is *transparent*
to `simp` (it unfolds automatically), while `def` is *opaque*
(you need `simp [name]` to unfold it).
-/

-- Demo: abbrev vs def
section AbbrevDemo
variable {α β : Type*} (f : α → β)

abbrev myRange := Set.range f
def myRange' := Set.range f

-- With abbrev, simp sees through the definition:
example (x : α) : f x ∈ myRange f := by
  simp [Set.mem_range]

-- With def, we need to explicitly unfold:
example (x : α) : f x ∈ myRange' f := by
  simp [Set.mem_range] -- this does NOT work because myRange' is opaque
  -- simp [myRange', Set.mem_range]

end AbbrevDemo


-- Demo: section with variable and local notation
section NotationDemo
variable (f : α → β)
local notation "R" => Set.range f

-- Inside the section, "R" stands for Set.range f:
example : R = Set.range f := by rfl

end NotationDemo
-- Outside the section, "R" no longer has that meaning.


-- Exercise (Part 2): Write a section with a local notation and use it.
-- (This is just for practice — uncomment and fill in.)
-- section MySection
-- variable (k : ℕ)
-- local notation "S" => k * (k + 1) / 2
-- example : 2 * S =  k * (k + 1) / 2 := by sorry
-- end MySection


-- ============================================================================
-- ## Part 3: Uniqueness Makes Choice Predictable
-- ============================================================================

/-
`Classical.choose` gives us *some* witness — but *which* one?  In general,
we cannot say.  Two proofs of the same `∃ b, P b` might in principle lead
`Classical.choose` to pick different elements.

*Uniqueness changes everything.*

`∃!` (exists-unique): The statement `∃! b, P b` means "there exists
a *unique* b satisfying P."  It unfolds to `∃ b, P b ∧ ∀ b', P b' → b' = b`.

The key insight: when `∃! b, P b` holds, `Classical.choose` becomes
predictable.  If you independently find *any* `c` satisfying `P c`, then
`c` must equal the chosen witness — because there is only one.
-/

-- Example: there is exactly one natural number n with n + 3 = 5.
example : ∃! n : ℕ, n + 3 = 5 := by
  use 2
  constructor
  · -- existence: 2 + 3 = 5
    linarith
  · -- uniqueness: if n + 3 = 5 then n = 2
    intro n' hn'
    linarith

-- Destructuring ∃! with rcases — here we actually USE both parts:
example (h : ∃! n : ℕ, n + 3 = 5) : ∀ m, m + 3 = 5 → m = 2 := by
  rcases h with ⟨n, hn_prop, hn_uniq⟩
  -- hn_prop : n + 3 = 5          (the property)
  -- hn_uniq : ∀ m, m + 3 = 5 → m = n  (uniqueness)
  intro m hm
  have : m = n := hn_uniq m hm    -- uniqueness tells us m = n
  linarith                         -- and n + 3 = 5 forces n = 2

/-
For `∃!`:  If `h : ∃! b, P b`, then `h.exists` gives `∃ b, P b ∧ ...`,
and `(Classical.choose_spec h.exists).1` gives the property,
while `(Classical.choose_spec h.exists).2` gives uniqueness.

The key pattern (used in your homework):
  Given `h : ∃! b, P b` and `hc : P c`,
  `(Classical.choose_spec h.exists).2 c hc` proves `c = Classical.choose h.exists`.
-/

-- Example: if ∃! n, n + 3 = 5, then the chosen witness must be 2.
example (h : ∃! n : ℕ, n + 3 = 5) : Classical.choose h.exists = 2 := by
  have hspec := Classical.choose_spec h.exists
  omega

-- **Application**: Unique preimages under injective functions.
-- If g is injective and x ∈ range g, there is a UNIQUE preimage.
-- This is exactly the situation in the SB construction: g is injective,
-- so for x ∉ A we can unambiguously define h(x) = g⁻¹(x).
section UniquePreimage
open Classical
variable {α β : Type*}

theorem unique_preimage (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) :
    ∃! b : β, g b = x := by
  obtain ⟨b, hb⟩ := hx
  use b
  simp
  constructor
  . exact hb
  . intro y hy
    apply hg
    rw [hb,hy]

-- If g c = x, then c equals the Classical.choose witness:
theorem preimage_unique (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) (c : β) (hc : g c = x) :
    c = Classical.choose (unique_preimage g hg x hx).exists := by
    set b := Classical.choose (unique_preimage g hg x hx).exists
    have hgb : g b = x := Classical.choose_spec (unique_preimage g hg x hx).exists
    show c = b
    apply hg
    rw [hc, hgb]

-- same proof concisely:
theorem preimage_unique' (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) (c : β) (hc : g c = x) :
    c = Classical.choose (unique_preimage g hg x hx).exists := by
  have hb := Classical.choose_spec (unique_preimage g hg x hx).exists
  exact hg (by rw [hc, hb])

end UniquePreimage

-- Note: when a computable representative exists (e.g., `a % 3` for
-- mod-3 equivalence classes on ℕ), no axiom of choice is needed.
-- On abstract types, `Classical.choose` is essential.

-- Exercise (Part 3): Prove that the chosen witness for ∃! n, n * 2 = 10
-- must equal 5.
example (h : ∃! n : ℕ, n * 2 = 10) : Classical.choose h.exists = 5 := by
  sorry


-- ============================================================================
-- ## Part 4: Piecewise Definitions
-- ============================================================================

/-
**Piecewise functions with `if h : P then … else …`.**

Unlike regular `if P then … else …`, the "dependent if" `if h : P then … else …`
makes the hypothesis `h : P` (or `h : ¬P`) available in the respective branch.
This is essential for defining functions like the SB bijection:
  h(x) = f(x)        if x ∈ A
  h(x) = g⁻¹(x)     if x ∉ A   ← needs the proof that x ∉ A to invoke choose!

In Lean, this is:
  `if xA : x ∈ A then f x else Classical.choose (hx_in_range_g xA)`
(where `hx_in_range_g` is a proof that `x ∉ A → x ∈ Set.range g`, so
`Classical.choose` can pick the preimage `g⁻¹(x)`).
The name `xA` binds the hypothesis `x ∈ A` or `x ∉ A` in each branch.

**Contrast**: regular `if` vs dependent `if`:
  Regular:   `if x > 0 then 1 else 0` — you do NOT get x > 0 as a hypothesis.
  Dependent: `if h : x > 0 then ... else ...` — you DO get h in each branch.
-/

-- Example: a piecewise bijection on ℤ.
-- Send nonnegatives to even numbers and negatives to odd numbers.
-- This echoes the ℤ ↔ ℕ ideas from Lecture 16, and foreshadows the SB
-- homework where h behaves differently on A and Aᶜ.
noncomputable def pwBij (x : ℤ) : ℤ :=
  if h : x ≥ 0 then 2 * x
               else 2 * x - 1

-- Prove pwBij agrees with 2 * x on nonnegatives:
theorem pwBij_nonneg (x : ℤ) (hx : x ≥ 0) : pwBij x = 2 * x := by
  simp [pwBij, hx]

-- Prove pwBij agrees with 2 * x - 1 on negatives:
theorem pwBij_neg (x : ℤ) (hx : ¬ (x ≥ 0)) : pwBij x = 2 * x - 1 := by
  simp [pwBij, hx]

-- The key proof pattern: `simp [defName, hypothesis]` handles piecewise defs.

-- Exercise (Part 4): Prove pwBij sends 0 to 0 and -1 to -3.
example : pwBij 0 = 0 := by
  sorry

example : pwBij (-1) = -3 := by
  sorry

-- Illustrating `Classical.choose_spec` with a piecewise definition.
-- Define a function that echoes the SB pattern:
--   on A, apply f directly; off A, pick the preimage under g.
section ChooseSpecPiecewise
open Set Classical
variable {α : Type*} (g : ℕ → α) (A : Set α)

noncomputable def sbLike (f : α → α)
    (hcompl : ∀ x : α, x ∉ A → x ∈ range g) (x : α) : α :=
  if hx : x ∈ A then f x
  else g (Classical.choose (hcompl x hx))

-- The key point: in the `else` branch, `Classical.choose` picks some `n : ℕ`
-- with `g n = x`.  How do we *know* it satisfies `g n = x`?
-- Answer: `Classical.choose_spec` recovers exactly that fact.
theorem sbLike_off_A (f : α → α)
    (hcompl : ∀ x : α, x ∉ A → x ∈ range g) (x : α) (hx : x ∉ A) :
    g (Classical.choose (hcompl x hx)) = x := by
  exact Classical.choose_spec (hcompl x hx)

end ChooseSpecPiecewise


-- ============================================================================
-- ## Addendum: Mathlib's `Countable` Typeclass
-- ============================================================================

-- Comment on `noncomputable` with `∃!`:
/-
Even with `∃!`, the definition remains noncomputable in Lean because `Classical.choose` is the mechanism for extracting the witness — and `Classical.choose` is axiomatically non-computational regardless of whether the existential is unique.

The reason is that uniqueness is a property (a proof-level statement), not a procedure. Knowing that there is exactly one `b` with `P b` tells you that the answer is determined, but it doesn't tell Lean how to find it. The type theory underlying Lean enforces a strict separation between proofs (which live in Prop and are erased at runtime) and data (which can be computed). The uniqueness proof `∀ b', P b' → b' = b` lives in `Prop` — it can't be executed as code.
-/

-- Mathlib packages the cardinality results we've been proving by hand.
-- `Countable α` asserts `∃ f : α → ℕ, Function.Injective f`.
#check (inferInstance : Countable ℕ)
#check (inferInstance : Countable ℤ)


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Prove: there is a unique natural number n with n + 5 = 8.
example : ∃! n : ℕ, n + 5 = 8 := by
  sorry

-- (2) Given h, what are the types of Classical.choose h and
-- Classical.choose_spec h?  Write #check statements to verify.
section WarmUp2
variable (h : ∃ n : ℕ, n > 100)
#check Classical.choose h         -- ℕ
#check Classical.choose_spec h    -- Classical.choose h > 100
end WarmUp2

-- (3) Define an abbrev and prove a simple fact about it:
abbrev myTriple (n : ℕ) : ℕ := 3 * n

example : myTriple 4 = 12 := by
  sorry

-- (4) Write a local notation for Set.range and use it:
section WarmUp4
variable {α β : Type*} (f : α → β)
local notation "ran" => Set.range f

example (x : α) : f x ∈ ran := by
  sorry

end WarmUp4


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Build a left inverse of an injection using Classical.choose.
-- (Analogous to Part 1's right inverse of a surjection.)
section Core5
open Classical
variable {α β : Type*}

noncomputable def leftInv (g : β → α) (hg : Function.Injective g)
    [Nonempty β] : α → β :=
  fun x => if hx : x ∈ Set.range g
    then Classical.choose hx
    else Classical.arbitrary β

-- Prove the defining property:
theorem leftInv_spec (g : β → α) (hg : Function.Injective g)
    [Nonempty β] (b : β) :
    leftInv g hg (g b) = b := by
  sorry

end Core5

-- (6) Prove: if ∃! b, g b = x and ∃! b, g b = y, with x ≠ y,
-- then the chosen witnesses are different.
section Core6
open Classical
variable {α β : Type*}

theorem unique_witnesses_differ (g : β → α)
    (x y : α) (hx : ∃! b, g b = x) (hy : ∃! b, g b = y) (hne : x ≠ y) :
    Classical.choose hx.exists ≠ Classical.choose hy.exists := by
  sorry

end Core6

-- (7) Define a piecewise function and prove it agrees with f₁ on S.
section Core7
variable {α β : Type*}

noncomputable def piecewise (f₁ f₂ : α → β) (S : Set α) [DecidablePred (· ∈ S)]
    (x : α) : β :=
  if h : x ∈ S then f₁ x else f₂ x

theorem piecewise_on_S (f₁ f₂ : α → β) (S : Set α) [DecidablePred (· ∈ S)]
    (x : α) (hx : x ∈ S) :
    piecewise f₁ f₂ S x = f₁ x := by
  sorry

end Core7

-- (8) Prove pwBij is injective using a 4-case split.
-- This foreshadows the HW07 injectivity proof.
-- Hint: by_cases hx : x ≥ 0 <;> by_cases hy : y ≥ 0
theorem pwBij_injective : Function.Injective pwBij := by
  sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (9) Build g_inv on Set.range g and prove key properties.
section Chall9
open Classical
variable {α β : Type*}

noncomputable def gInv (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) : β :=
  Classical.choose hx

theorem gInv_spec (g : β → α) (hg : Function.Injective g)
    (x : α) (hx : x ∈ Set.range g) :
    g (gInv g hg x hx) = x :=
  Classical.choose_spec hx

-- Prove gInv is injective on the range (i.e., distinct range elements
-- have distinct preimages):
theorem gInv_injective (g : β → α) (hg : Function.Injective g)
    (x y : α) (hx : x ∈ Set.range g) (hy : y ∈ Set.range g)
    (heq : gInv g hg x hx = gInv g hg y hy) : x = y := by
  sorry

end Chall9

-- (10) Prove: if Countable α and f : α → β is surjective, then Countable β.
-- Hint: look at `Countable.of_surjective` or build the injection by hand.
theorem countable_of_surjective {α β : Type*} [Countable α]
    (f : α → β) (hf : Function.Surjective f) :
    Countable β := by
  sorry

-- (11) Define a piecewise function on ℕ:
--   h(n) = n / 2       if n is even
--   h(n) = (n + 1) / 2 if n is odd
-- and prove: h(n) ≤ n for all n.
def halfish (n : ℕ) : ℕ :=
  if h : n % 2 = 0 then n / 2
  else (n + 1) / 2

theorem halfish_le (n : ℕ) : halfish n ≤ n := by
  sorry
