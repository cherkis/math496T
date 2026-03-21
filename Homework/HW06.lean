-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

/-! # Homework 6: The Schröder–Bernstein Theorem
Based on Lectures 16–17 (Cardinality).
-/

variable {α β : Type*}

-- ============================================================================
-- ## Problems 1–4: Preparation for Schröder–Bernstein Proof (50 points)
-- ============================================================================

/-!
**The Schröder–Bernstein Theorem**: If there exist injections
f : α → β and g : β → α,
then there exists a bijection α ↔ β.

**The construction**:
  A₀ = α \ range(g)            (elements of α not in the image of g)
  Aₙ₊₁ = (g ∘ f) '' Aₙ          (apply g ∘ f to the previous layer)
  A_all = ⋃ₙ Aₙ                 (the union of all layers)

Then define:
  h(x) = f(x)        if x ∈ A_all
  h(x) = g⁻¹(x)     if x ∉ A_all

We must show h is well-defined (g⁻¹(x) exists when x ∉ A_all) and bijective.
-/

-- We work with explicit injections:
variable {f : α → β} {g : β → α}
variable (hf : Function.Injective f)
variable (hg : Function.Injective g)

-- Define the layers:
-- Start with a complement of the image of g
noncomputable  def sbA₀ (g : β → α) : Set α := (Set.range g)ᶜ

-- Then apply g ∘ f repeatedly to get the layers
noncomputable def sbLayer (f : α → β) (g : β → α) : ℕ → Set α
  | 0     => sbA₀ g
  | n + 1 => (g ∘ f) '' sbLayer f g n

-- form their union
noncomputable def sbA_all (f : α → β) (g : β → α) : Set α :=
  ⋃ n, sbLayer f g n

-- Recall the names of some basic set theory theorems:
example (A : Set α) : (Aᶜ)ᶜ =A := compl_compl A
example (A : Set α) (x : α) : x ∈ Aᶜ ↔ x ∉ A := Set.mem_compl_iff A x
example (A : Set α) (x : α) : x ∉ Aᶜ ↔ x ∈ A := @Set.notMem_compl_iff _ A x
#check Set.mem_iUnion_of_mem -- i : (ha : a ∈ s i) → a ∈ ⋃ i, s i

-- (1) Prove: if x ∉ A_all, then x ∈ range(g).
-- Since A₀ = (range g)ᶜ, and A_all ⊇ A₀, if x ∉ A_all then x ∉ A₀,
-- which means x ∈ range(g).
@[autogradedProof 13]
theorem problem1 {x : α} (hx : x ∉ sbA_all f g) :
    x ∈ Set.range g := by
  sorry
  done

-- (2) Key lemma: if x ∈ sbLayer f g n for some n, then
-- g(f(x)) ∈ sbLayer f g (n+1).
@[autogradedProof 12]
theorem problem2 {x : α} {n : ℕ} (hx : x ∈ sbLayer f g n) :
    g (f x) ∈ sbLayer f g (n + 1) := by
  sorry
  done

-- (3) Key lemma: if x ∉ A_all, then g⁻¹(x) is well-defined.
-- Since x ∈ range(g) (by problem 1), there exists b with g(b) = x.
-- Moreover, b is unique (since g is injective).
-- NOTE:
-- (∃ x, p x) ∧ (∀ y, p y → y = x) is the definition of ∃! x, p x.
@[autogradedProof 12]
theorem problem3 {x : α} (hx : x ∉ sbA_all f g) (hg : Function.Injective g) :
    ∃! b : β, g b = x := by
  sorry
  done


#check Set.mem_iUnion -- : x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i

-- (4) Key lemma: if x ∉ A_all, and g(b) = x, then b ≠ f(y) for any y ∈ A_all.
-- Proof idea: if b = f(y) for some y ∈ A_all, then x = g(b) = g(f(y)).
-- Since y ∈ sbLayer f g n for some n, g(f(y)) ∈ sbLayer f g (n+1) ⊆ A_all.
-- use problem2
-- But x ∉ A_all — contradiction.
@[autogradedProof 13]
theorem problem4 (x : α) (hx : x ∉ sbA_all f g) (b : β) (hb : g b = x)
    (y : α) (hy : y ∈ sbA_all f g) : b ≠ f y := by
  sorry
  done