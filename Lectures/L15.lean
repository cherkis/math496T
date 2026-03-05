import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Ring.Parity

/- # Lecture 15: Image, Preimage, and Inverse Functions

New tactics: **choose, aesop**
Recall: **funext, intro, apply, use, obtain, ext, simp, constructor, rw, calc, omega,
         norm_num, ring, linarith, push_neg**

## Overview

In Lecture 14 we studied *properties* of functions (injective, surjective,
bijective) and how they behave under composition.  Today we study what
functions *do to sets*: how they
- push sets forward (**image**) and
- pull sets backward (**preimage**).

Then we connect injectivity and surjectivity to the existence of
**inverse functions** — and encounter the **axiom of choice**.

### A Surprising Asymmetry

Preimage behaves perfectly: it preserves unions, intersections, and
complements.
Forward image, by contrast, preserves unions but
**not** intersections and **not** complements.

Why?  Membership in `f⁻¹' T` is a simple test: "is f(x) in T?"
Membership in `f '' S` is an existential claim: "there exists some x in S
with f(x) = y."  Existential statements distribute over ∨ (union)
but not over ∧ (intersection).

This is the logic–sets dictionary from Lectures 10–11 at work once more.

### An Interesting Fact: The Axiom of Choice

We will prove that every injective function has a **left inverse** and
every surjective function has a **right inverse**.  The first is
constructive.  The second requires choosing, for each element b of the
codomain, some preimage a with f(a) = b — but which one?

The **axiom of choice** says: whenever every element has at least one
preimage, we can simultaneously select one for each.  In Lean this is
the `choose` tactic.  Remarkably, the statement "every surjection has
a right inverse" is *equivalent* to the axiom of choice — one of the
most debated principles in the foundations of mathematics since
Zermelo introduced it in 1904.
-/


-- ============================================================================
-- ## Key Definitions (Mathlib)
-- ============================================================================

-- Image and preimage of sets:
#check @Set.image         -- f '' S = { y | ∃ x ∈ S, f x = y }
#check @Set.preimage      -- f ⁻¹' T = { x | f x ∈ T }

-- Membership lemmas:
#check @Set.mem_image     -- y ∈ f '' S ↔ ∃ x ∈ S, f x = y
#check @Set.mem_preimage  -- x ∈ f ⁻¹' T ↔ f x ∈ T

-- Image and preimage with set operations:
#check @Set.image_union       -- f '' (S ∪ T) = f '' S ∪ f '' T
#check @Set.preimage_union    -- f ⁻¹' (S ∪ T) = f ⁻¹' S ∪ f ⁻¹' T
#check @Set.preimage_inter    -- f ⁻¹' (S ∩ T) = f ⁻¹' S ∩ f ⁻¹' T
#check @Set.preimage_compl    -- f ⁻¹' Tᶜ = (f ⁻¹' T)ᶜ

-- Left and right inverse:
#check @Function.LeftInverse   -- (g : β → α) (f : α → β) : g ∘ f = id  (i.e. ∀ x, g (f x) = x)
#check @Function.RightInverse  -- (g : β → α) (f : α → β) : f ∘ g = id  (i.e. ∀ y, f (g y) = y)

-- The `choose` tactic (axiom of choice):
-- Given `h : ∀ x, ∃ y, P x y`, the tactic `choose f hf using h`
-- produces `f : α → β` and `hf : ∀ x, P x (f x)`.


-- ============================================================================
-- ## Part 1: Image of a Set
-- ============================================================================

/-
Given `f : α → β` and `S : Set α`, the **image** of S under f is:

  f '' S = { y : β | ∃ x ∈ S, f x = y }

In Lean notation: `f '' S` (with two single-quote marks).

**To prove** `y ∈ f '' S`:
  Provide a witness `x`, prove `x ∈ S`, and prove `f x = y`.
  Pattern: `exact ⟨x, hx, rfl⟩` or `use x`

**To use** `h : y ∈ f '' S`:
  Extract the witness: `obtain ⟨x, hx, hfx⟩ := h`
  Now `hx : x ∈ S` and `hfx : f x = y`.
-/

section ImagePreimage
variable {α β γ : Type*}
variable (f : α → β)

-- Example: 9 is in the image of (· ^ 2) applied to {3, 4, 5}
example : (9 : ℤ) ∈ (fun n : ℤ => n ^ 2) '' {3, 4, 5} := by
  use 3
  constructor
  · dsimp [Membership.mem,Set.Mem,Set.instInsert,Set.insert]
    left
    rfl  -- left; rfl
  · norm_num

-- Example: the image of ℕ under (· * 2) consists of even numbers
example : (fun n : ℕ => n * 2) '' {n : ℕ | True} = {m : ℕ | 2 ∣ m} := by
  ext m
  simp [Set.mem_image]
  constructor
  · rintro ⟨n, -, rfl⟩; exact ⟨n,by apply mul_comm⟩
  · rintro ⟨k, rfl⟩; exact ⟨k,mul_comm k 2⟩

-- The range of f is the image of the entire domain:
-- Set.range f = f '' Set.univ
example : Set.range f = f '' Set.univ := by
  ext y; simp [Set.mem_range]

-- **Image preserves union** (and this is an equality, not just ⊆):
-- f '' (S ∪ T) = f '' S ∪ f '' T
-- The proof mirrors:  ∃ x, (x ∈ S ∨ x ∈ T) ∧ f x = y
--                   ↔ (∃ x ∈ S, f x = y) ∨ (∃ x ∈ T, f x = y)
variable (S T : Set α)

-- ## You will prove the following in your HOMEWORK
example : f '' (S ∪ T) = f '' S ∪ f '' T := by
  sorry -- HOMEWORK

-- **Image does NOT preserve intersection** in general!
-- f '' (S ∩ T) ⊆ f '' S ∩ f '' T  (always true)
-- f '' (S ∩ T) = f '' S ∩ f '' T  (can FAIL — unless f is injective)

-- The inclusion ⊆ always holds:
example : f '' (S ∩ T) ⊆ f '' S ∩ f '' T := by
  sorry -- HOMEWORK

-- Counterexample for the reverse:
example : ∃ (f : ℤ → ℤ) (S T : Set ℤ),
    ¬ (f '' S ∩ f '' T ⊆ f '' (S ∩ T)) := by
  sorry -- HOMEWORK


-- Exercises (Part 1)

-- (a) Show that 8 is in the image of (· + 3) applied to {5}:
example : (8 : ℤ) ∈ (fun n : ℤ => n + 3) '' {5} := by
  sorry

-- (b) Show that the image of {0, 1, 2} under (· * 2) is {0, 2, 4}:
example : (fun n : ℕ => n * 2) '' {0, 1, 2} = {0, 2, 4} := by
  sorry

-- (c) Prove: if S ⊆ T then f '' S ⊆ f '' T (image is monotone):
example (h : S ⊆ T) : f '' S ⊆ f '' T := by
  sorry

-- (d) Prove: S ⊆ f ⁻¹' (f '' S) ("S is contained in the preimage of its image"):
-- This says: if x ∈ S, then f(x) ∈ f '' S.
example : S ⊆ f ⁻¹' (f '' S) := by
  sorry


-- ============================================================================
-- ## Part 2: Preimage of a Set
-- ============================================================================

/-
Given `f : α → β` and `T : Set β`, the **preimage** of T under f is:

  f ⁻¹' T = { x : α | f x ∈ T }

The notation is `f ⁻¹' T` (with ⁻¹' , not to be confused with an inverse
function — this is an operation on *sets*, not on elements).

**To prove** `x ∈ f ⁻¹' T`:
  Show `f x ∈ T`.  (This is definitionally the same thing.)

**To use** `h : x ∈ f ⁻¹' T`:
  You have `h : f x ∈ T`.

**Preimage is much better behaved** than image because it's defined by a
*simple test* (is f(x) in T?) rather than an *existential claim*.
-/

variable (U V : Set β)

-- Example: 3 is in the preimage of {9} under (· ^ 2)
example : (3 : ℤ) ∈ (fun n : ℤ => n ^ 2) ⁻¹' {9} := by
  show (3 : ℤ) ^ 2 ∈ ({9} : Set ℤ)
  norm_num

-- **Preimage preserves unions:**
example : f ⁻¹' (U ∪ V) = f ⁻¹' U ∪ f ⁻¹' V := by
  sorry -- HOMEWORK

-- **Preimage preserves intersections:**
example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  sorry -- HOMEWORK

-- **Preimage preserves complements:**
example : f ⁻¹' Uᶜ = (f ⁻¹' U)ᶜ := by
  ext x
  simp [Set.mem_preimage, Set.mem_compl_iff]

/-
**Summary of the asymmetry:**

  Operation      Image f ''       Preimage f ⁻¹'
  ─────────────────────────────────────────────────
  Union          = (preserves)    = (preserves)
  Intersection   ⊆ only           = (preserves)
  Complement    neither ⊆ nor ⊇   = (preserves)

Preimage preserves everything because `f x ∈ S ∩ T ↔ f x ∈ S ∧ f x ∈ T`
is just a logical equivalence — no existential quantifiers involved.

Image loses information because it introduces ∃, and ∃ doesn't commute
with ∧ or ¬.
-/

/- You can try proving that
`∀ A, f(A)ᶜ ⊆ f(Aᶜ)` if `f` is surjective and
`∀ A, f(A)ᶜ ⊇ f(Aᶜ)` if `f` is injective !
Thus, the two are equal if `f` is bijective.
-/

-- Exercises (Part 2)

-- (a) Show that 4 ∈ preimage of {0, 1, 2} under (· % 3) on ℕ:
-- (Since 4 % 3 = 1, and 1 ∈ {0, 1, 2}.)
example : (4 : ℕ) ∈ (fun n : ℕ => n % 3) ⁻¹' {0, 1, 2} := by
  sorry

-- (b) Prove: preimage preserves subset (monotonicity):
-- If U ⊆ V then f ⁻¹' U ⊆ f ⁻¹' V.
example (h : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  sorry

-- (c) Prove: f '' (f ⁻¹' U) ⊆ U ("the image of the preimage is contained in U"):
example : f '' (f ⁻¹' U) ⊆ U := by
  sorry

-- (d) Prove: preimage of the entire codomain is everything:
example : f ⁻¹' (Set.univ : Set β) = Set.univ := by
  sorry

-- (e) Challenge: Prove that if f is surjective, then
-- U ⊆ f '' (f ⁻¹' U)  (so combined with (c), we get equality).
example (hf : Function.Surjective f) : U ⊆ f '' (f ⁻¹' U) := by
  sorry


-- ============================================================================
-- ## Part 3: Fibers
-- ============================================================================

/-
The **fiber** of f over a point b ∈ β is the preimage of {b}:

  f ⁻¹' {b} = { x : α | f x = b }

This is the set of all elements that f maps to b — the "level set" at b.

Fibers connect functions to equivalence relations:
  Define a ~ b  ↔  f(a) = f(b).
This is an equivalence relation (the **kernel** of f — we saw this in
Lecture 12 as `fKernel`).  Its equivalence classes are exactly the
fibers of f!

**Key facts:**
  • If f is injective, every fiber has at most one element.
  • If f is surjective, every fiber is nonempty.
  • If f is bijective, every fiber is a singleton.
  • The fibers partition the domain (they are disjoint and cover α).
-/

-- Example: the fiber of (· % 3 : ℤ → ℤ) over 0 is the multiples of 3
example : (fun n : ℤ => n % 3) ⁻¹' {0} = {n : ℤ | 3 ∣ n} := by
  ext x
  simp [Set.mem_preimage, Set.mem_setOf_eq]

-- Example: fibers of an injective function have at most one element.
-- We state this as: if f is injective and a, b are in the same fiber, then a = b.
example {f : α → β} (hinj : Function.Injective f) (b : β)
    {x y : α} (hx : x ∈ f ⁻¹' {b}) (hy : y ∈ f ⁻¹' {b}) :
    x = y := by
  simp [Set.mem_preimage] at hx hy
  -- hx : f x = b,  hy : f y = b
  exact hinj (by rw [hx, hy])

-- Example: fibers of a surjective function are nonempty.
example {f : α → β} (hsurj : Function.Surjective f) (b : β) :
    (f ⁻¹' {b}).Nonempty := by
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨a, by simp [Set.mem_preimage, ha]⟩

-- The fibers are pairwise disjoint (for distinct points):
example {f : α → β} {b₁ b₂ : β} (hne : b₁ ≠ b₂) :
    Disjoint (f ⁻¹' {b₁}) (f ⁻¹' {b₂}) := by
  rw [Set.disjoint_iff]
  intro x ⟨h1, h2⟩
  simp [Set.mem_preimage] at h1 h2
  exact hne (h1 ▸ h2)

-- The fibers cover the whole domain:
example : ⋃ b : β, f ⁻¹' {b} = Set.univ := by
  ext x
  simp [Set.mem_iUnion, Set.mem_preimage]


-- Exercises (Part 3)

-- (a) Show that the fiber of (fun n : ℤ => n % 2) over 1 contains 7:
example : (7 : ℤ) ∈ (fun n : ℤ => n % 2) ⁻¹' {1} := by
  sorry

-- (b) Prove: the fiber of the identity function over b is {b}:
example (b : β) : (id : β → β) ⁻¹' {b} = {b} := by
  sorry

-- (c) Prove: x ∈ f ⁻¹' {f x} (every element is in its own fiber):
example (x : α) : x ∈ f ⁻¹' {f x} := by
  sorry

-- (d) Challenge: Prove that the image of a fiber is contained in
-- the singleton (and equals it if x is in the range).
example (b : β) : f '' (f ⁻¹' {b}) ⊆ {b} := by
  sorry


-- ============================================================================
-- ## Part 4: Left Inverses and Right Inverses
-- ============================================================================

/-
**Left inverse**: g is a left inverse of f if `g ∘ f = id`, i.e.
  ∀ x, g(f(x)) = x.
This means g "undoes" f.

**Right inverse**: g is a right inverse of f if `f ∘ g = id`, i.e.
  ∀ y, f(g(y)) = y.
This means f "undoes" g.

(In category theory,
- a left inverse is called a **retraction** and
- a right inverse is called a **section**.)

The fundamental connection:
  • f has a left inverse  →  f is injective
  • f has a right inverse →  f is surjective

We will also prove the converses, which require more work.
-/

-- Easy direction 1: left inverse → injective
-- If g ∘ f = id and f(a) = f(b), then a = g(f(a)) = g(f(b)) = b.
theorem left_inv_injective {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) : Function.Injective f := by
  intro a b hab
  -- h : ∀ x, g (f x) = x
  have ha := h a  -- ha : g (f a) = a
  have hb := h b  -- hb : g (f b) = b
  rw [← ha, ← hb, hab]

-- Easy direction 2: right inverse → surjective
-- If f ∘ g = id, then for any b, f(g(b)) = b, so g(b) is a preimage of b.
theorem right_inv_surjective {f : α → β} {g : β → α}
    (h : Function.RightInverse g f) : Function.Surjective f := by
  intro b
  -- h : ∀ y, f (g y) = y
  use g b
  exact h b

/-
Now for the **converses**. These are deeper.

**Injective → has a left inverse** (assuming α is nonempty).
If f is injective, we can define g : β → α by:
  g(y) = the unique x with f(x) = y, if y is in the range of f
  g(y) = some default element,       if y is not in the range of f

This is constructive — we don't need the axiom of choice because the
preimage of each point in the range is unique (by injectivity).
-/

example : f (g a) = (f ∘ g) a := by exact?

-- Injective → has a left inverse (assuming domain is nonempty)
theorem inj_has_left_inv {f : α → β} [Nonempty α]
    (hf : Function.Injective f) :
    ∃ g : β → α, Function.LeftInverse g f := by
  -- For each b in the range of f, there's a unique preimage.
  -- For b outside the range, pick any element of α.
  -- Lean's `Function.invFun` does exactly this.
  use Function.invFun f
  intro a
  show ((Function.invFun f) ∘ f) a = a
  rw [Function.invFun_comp hf]
  simp

/-
**Surjective → has a right inverse.**  This is where the axiom of choice
makes its appearance!

If f is surjective, then ∀ b, ∃ a, f(a) = b.  We need to *simultaneously
choose* one such a for every b.  This is exactly what the axiom of choice
provides — and in Lean, the `choose` tactic.

**The `choose` tactic:**
  Given `h : ∀ x, ∃ y, P x y`
  `choose g hg using h` produces:
    `g : α → β`
    `hg : ∀ x, P x (g x)`
It extracts a choice function from the existential.
-/

-- Surjective → has a right inverse (uses axiom of choice!)
theorem surj_has_right_inv {f : α → β}
    (hf : Function.Surjective f) :
    ∃ g : β → α, Function.RightInverse g f := by
  -- hf : ∀ b, ∃ a, f a = b
  -- We use `choose` to extract a function g from this:
  choose g hg using hf
  -- g : β → α
  -- hg : ∀ b, f (g b) = b
  exact ⟨g, hg⟩

-- Let's see `choose` in action with a simpler example:
example (h : ∀ n : ℕ, ∃ m : ℕ, m = n + 1) : ∃ f : ℕ → ℕ, ∀ n, f n = n + 1 := by
  choose f hf using h
  exact ⟨f, hf⟩


-- Exercises (Part 4)

-- (a) Verify that (· - 3) is a left inverse of (· + 3) on ℤ:
example : Function.LeftInverse (fun n : ℤ => n - 3) (fun n : ℤ => n + 3) := by
  sorry

-- (b) Verify that (· - 3) is also a right inverse of (· + 3) on ℤ:
example : Function.RightInverse (fun n : ℤ => n - 3) (fun n : ℤ => n + 3) := by
  sorry

-- (c) Show that a left inverse of an injective function is surjective.
-- Hint: if g ∘ f = id, then for any a : α, g(f(a)) = a, so a is in the range of g.
theorem left_inv_surj {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) : Function.Surjective g := by
  sorry

-- (d) Challenge: Use `choose` to show that if every fiber of f is nonempty,
-- then f has a right inverse.
-- (This is just surjectivity rephrased in terms of fibers.)
example {f : α → β} (h : ∀ b : β, (f ⁻¹' {b}).Nonempty) :
    ∃ g : β → α, ∀ b, f (g b) = b := by
  sorry

-- (e) Prove: if f has both a left inverse g and a right inverse h,
-- then g = h.  (The two-sided inverse is unique!)
theorem left_right_inv_unique {f : α → β} {g h : β → α}
    (hg : Function.LeftInverse g f) (hh : Function.RightInverse h f) :
    g = h := by
  sorry


-- ============================================================================
-- ## Part 5: Inverse Functions for Bijections
-- ============================================================================

/-
If f is **bijective** (both injective and surjective), then it has both
a left inverse and a right inverse — and by the uniqueness result above,
they must be the same function!

This unique function is THE **inverse** of f, written f⁻¹ in mathematics
(and `Function.invFun f` or `Equiv.invFun` in Lean/Mathlib).

**Properties of the inverse of a bijection:**
  1. f⁻¹ ∘ f = id   (left inverse)
  2. f ∘ f⁻¹ = id   (right inverse)
  3. f⁻¹ is itself bijective
  4. (f⁻¹)⁻¹ = f
-/

-- Building the inverse of a bijection step by step:
-- From surjectivity, we get a right inverse using choose.
-- From injectivity, this right inverse is also a left inverse.

theorem bij_has_inv {f : α → β}
    (hf : Function.Bijective f) :
    ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  obtain ⟨hinj, hsurj⟩ := hf
  -- Use surjectivity + choice to get a right inverse:
  choose g hg using hsurj
  use g
  constructor
  · -- Left inverse: g(f(a)) = a for all a.
    -- We know f(g(f(a))) = f(a)  (from hg applied to f(a)).
    -- Since f is injective, g(f(a)) = a.
    intro a
    have : f (g (f a)) = f a := hg (f a)
    exact hinj this
  · -- Right inverse: f(g(b)) = b for all b.
    exact hg

-- The inverse of a bijection is bijective.
theorem bij_inv_bij {f : α → β} {g : β → α}
    (hL : Function.LeftInverse g f) (hR : Function.RightInverse g f) :
    Function.Bijective g := by
  constructor
  · -- g is injective: if g(b₁) = g(b₂), apply f to both sides.
    -- f(g(b₁)) = f(g(b₂)), i.e. b₁ = b₂  (since f ∘ g = id).
    intro b₁ b₂ h
    have h₁ := hR b₁  -- f (g b₁) = b₁
    have h₂ := hR b₂  -- f (g b₂) = b₂
    rw [← h₁, ← h₂, h]
  · -- g is surjective: for any a, g(f(a)) = a, so f(a) is a preimage.
    intro a
    use f a
    exact hL a


-- Exercises (Part 5)

-- (a) Prove that (fun n : ℤ => n + 5) is bijective and
-- (fun n : ℤ => n - 5) is its inverse:
example : Function.Bijective (fun n : ℤ => n + 5) ∧
    Function.LeftInverse (fun n : ℤ => n - 5) (fun n : ℤ => n + 5) ∧
    Function.RightInverse (fun n : ℤ => n - 5) (fun n : ℤ => n + 5) := by
  sorry

-- (b) Prove: if g is a left inverse of f and f is surjective, then
-- g is also a right inverse of f.
-- (Surjectivity + left inverse gives a full inverse.)
theorem left_inv_of_surj_is_right_inv {f : α → β} {g : β → α}
    (hg : Function.LeftInverse g f) (hf : Function.Surjective f) :
    Function.RightInverse g f := by
  sorry

-- (c) Prove: the composition of two bijections has an inverse that is
-- the composition of the individual inverses in reverse order.
-- That is: if g₂ ∘ g₁ is the inverse of f₁ ∘ f₂, and the individual
-- inverses are composed correctly.
-- We prove: (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹  (the "socks and shoes" property).
theorem inv_comp {f : α → β} {g : β → γ}
    {f_inv : β → α} {g_inv : γ → β}
    (hf : Function.LeftInverse f_inv f) (hf' : Function.RightInverse f_inv f)
    (hg : Function.LeftInverse g_inv g) (hg' : Function.RightInverse g_inv g) :
    Function.LeftInverse (f_inv ∘ g_inv) (g ∘ f) := by
  sorry


end ImagePreimage


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

section EndExercises
variable {α β : Type*}
variable (f : α → β)


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Prove: image of empty set is empty.
example : f '' (∅ : Set α) = ∅ := by sorry

-- (2) Prove: preimage of empty set is empty.
example : f ⁻¹' (∅ : Set β) = ∅ := by sorry

-- (3) Prove: 10 is in the image of (· + 3) applied to {7}:
example : (10 : ℤ) ∈ (fun n : ℤ => n + 3) '' {7} := by sorry

-- (4) Prove that (· + 1) and (· - 1) are two-sided inverses on ℤ:
example : Function.LeftInverse (fun n : ℤ => n - 1) (fun n : ℤ => n + 1) ∧
          Function.RightInverse (fun n : ℤ => n - 1) (fun n : ℤ => n + 1) := by sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Prove: the image of a union under any function equals the union of images.
-- (This is the fundamental fact that image preserves unions.)
variable (S T : Set α) (U V : Set β)

example : f '' (S ∪ T) = f '' S ∪ f '' T := by sorry

-- (6) Prove: preimage distributes over intersection.
example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by sorry

-- (7) Prove: if f is injective, then f '' (S ∩ T) = f '' S ∩ f '' T.
-- (Injectivity repairs the failure of image to preserve intersections!)
example (hf : Function.Injective f) :
    f '' (S ∩ T) = f '' S ∩ f '' T := by sorry

-- (8) Prove: the restriction of an injective function is injective.
-- Here we model "restriction" by composing with a function from a subtype.
-- If f : α → β is injective, then for any S : Set α,
-- the function (fun x : S => f x) is injective.
example (hf : Function.Injective f) (S : Set α) :
    Function.Injective (fun x : S => f x) := by sorry

-- (9) Use `choose` to prove: if for every y ∈ U there exists x with
-- f x = y, then U ⊆ Set.range f.
example (h : ∀ y ∈ U, ∃ x, f x = y) : U ⊆ Set.range f := by sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (10) Prove: image commutes with indexed union.
-- f '' (⋃ i, A i) = ⋃ i, f '' (A i)
variable {ι : Type*} (A : ι → Set α)

example : f '' (⋃ i, A i) = ⋃ i, f '' (A i) := by sorry

-- (11) CHALLENGE: If f is bijective with inverse g, then for any S : Set α,
-- g '' (f '' S) = S.  ("The inverse undoes the image.")
example {f : α → β} {g : β → α}
    (hL : Function.LeftInverse g f) (hR : Function.RightInverse g f)
    (S : Set α) :
    g '' (f '' S) = S := by sorry

-- (12) CHALLENGE: Prove that the indicator function (characteristic function)
-- of a set S determines S.  That is: if the indicator functions of S and T
-- are equal, then S = T.
-- The indicator function of S maps x to 1 if x ∈ S and 0 otherwise.
-- In Lean: `Set.indicator S (fun _ => (1 : ℕ))`
example (S T : Set α) :
    Set.indicator S (fun _ => (1 : ℕ)) = Set.indicator T (fun _ => 1) → S = T := by sorry

-- (13) CHALLENGE: Prove that preimage preserves indexed intersections.
-- f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
variable (B : ι → Set β)

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) := by sorry


end EndExercises
