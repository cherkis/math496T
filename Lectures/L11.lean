import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Algebra.Ring.Parity

/- # Lecture 11: Sets and Set Operations (Part II)
   Indexed Families, Cartesian Product, Power Set

Reviewing tactics: **ext, have, suffices, show, change, simp, tauto**
and quantifier tactics: **intro, use, obtain** — now in a set-theoretic context.

## Overview

Lecture 10: set operations ARE logical connectives.

  ∩ = ∧,   ∪ = ∨,   ᶜ = ¬,   ⊆ = →,   extensionality = ↔

Today we extend this to **indexed families** of sets, where:
  ⋃ i, A i  =  ∃ i, ...     (indexed union ↔ existential quantifier)
  ⋂ i, A i  =  ∀ i, ...     (indexed intersection ↔ universal quantifier)

This completes the logic–sets dictionary from Lecture 10.
-/


-- ============================================================================
-- ## Key Definitions and Theorems to Know
-- ============================================================================

-- Indexed union and intersection:
#check @Set.mem_iUnion   -- x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i
#check @Set.mem_iInter   -- x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i

-- Useful characterizations of subset with indexed operations:
#check @Set.iUnion_subset_iff  -- ⋃ i, A i ⊆ B ↔ ∀ i, A i ⊆ B
#check @Set.subset_iInter_iff  -- B ⊆ ⋂ i, A i ↔ ∀ i, B ⊆ A i

-- De Morgan for indexed families:
#check @Set.compl_iUnion  -- (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ
#check @Set.compl_iInter  -- (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ

-- Cartesian product of sets:
#check @Set.mem_prod  -- p ∈ A ×ˢ B ↔ p.1 ∈ A ∧ p.2 ∈ B

-- Power set:
#check @Set.mem_powerset_iff  -- A ∈ 𝒫 B ↔ A ⊆ B


section IndexedFamilies
variable {α ι : Type*}
variable (A B : ι → Set α)
variable (S T : Set α)

-- ============================================================================
-- ## Part 1: Indexed Union  (⋃ i, A i)
-- ============================================================================

/-
The indexed union `⋃ i, A i` is the set of all elements that belong
to at least one of the sets `A i`.

  x ∈ ⋃ i, A i  ↔  ∃ i, x ∈ A i

To PROVE `x ∈ ⋃ i, A i`:
  Provide a witness index `i` and show `x ∈ A i`.
  Tactic pattern: `rw [Set.mem_iUnion]; use i; ...`
  or equivalently: `simp only [Set.mem_iUnion]; use i; ...`

To USE `h : x ∈ ⋃ i, A i`:
  Extract a witness: `obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h`
  or: `rw [Set.mem_iUnion] at h; obtain ⟨i, hi⟩ := h`
-/

-- Example: Each A i is contained in the union
example (j : ι) : A j ⊆ ⋃ i, A i := by
  intro x hx
  rw [Set.mem_iUnion]
  use j

-- The above is also `Set.subset_iUnion_of_subset j`

-- Example: If every A i ⊆ S, then the union ⊆ S
example (h : ∀ i, A i ⊆ S) : ⋃ i, A i ⊆ S := by
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact h i hi

-- The above is exactly `Set.iUnion_subset_iff.mpr h`, but the manual
-- proof shows how ⋃ unfolds to ∃.


-- ============================================================================
-- ## Part 2: Indexed Intersection  (⋂ i, A i)
-- ============================================================================

/-
The indexed intersection `⋂ i, A i` is the set of all elements that
belong to every one of the sets `A i`.

  x ∈ ⋂ i, A i  ↔  ∀ i, x ∈ A i

To PROVE `x ∈ ⋂ i, A i`:
  Show `x ∈ A i` for every `i`.
  Tactic pattern: `rw [Set.mem_iInter]; intro i; ...`

To USE `h : x ∈ ⋂ i, A i`:
  Specialize to a particular index: `have hi := Set.mem_iInter.mp h i`
  or: `rw [Set.mem_iInter] at h; have hi := h i`
-/

-- Example: The intersection is contained in each A j
example (j : ι) : ⋂ i, A i ⊆ A j := by
  intro x hx
  rw [Set.mem_iInter] at hx
  exact hx j

-- Example: If S ⊆ every A i, then S ⊆ the intersection
example (h : ∀ i, S ⊆ A i) : S ⊆ ⋂ i, A i := by
  intro x hx
  rw [Set.mem_iInter]
  intro i
  exact h i hx


-- ============================================================================
-- ## Part 3: The Complete Logic–Sets Dictionary
-- ============================================================================

/-
We can now complete the correspondence between logic and sets.
Notice the introduction/elimination duality: each logical connective
has rules for how to PROVE it and how to USE it.

  Logic          Set operation        To Prove             To Use
  ─────────────────────────────────────────────────────────────────
  P ∧ Q          x ∈ A ∩ B           • constructor         • obtain ⟨ha,hb⟩
                                     • ⟨ , ⟩               • .left
                                                           • .right

  P ∨ Q          x ∈ A ∪ B           • left                • rcases
                                     • right               • obtain (ha | hb)

  ¬ P            x ∈ Aᶜ              • intro               • apply
                                     • absurd              • contrapose

  P → Q          A ⊆ B               • intro x hx          • apply
                                                           • specialize

  P ↔ Q          A = B               • constructor         • rw
                                                           • h.mp
                                                           • h.mpr

  ∃ i, P i       x ∈ ⋃ i, A i        • use i               • obtain ⟨i, hi⟩
                                                           • rcases ⟨i, hi⟩

  ∀ i, P i       x ∈ ⋂ i, A i        • intro i             • apply
                                                           • specialize

This is the entire propositional + predicate logic from Lectures 1-6,
now appearing as set theory!
The introduction/elimination structure is universal across all these concepts.
-/


-- ============================================================================
-- ## Part 4: Properties of Indexed Unions and Intersections
-- ============================================================================

-- Indexed union is monotone: if each A i ⊆ B i, then ⋃ A i ⊆ ⋃ B i
example (h : ∀ i, A i ⊆ B i) : ⋃ i, A i ⊆ ⋃ i, B i := by
  intro x hx
  rw [Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  use i
  exact h i hi

-- Intersection distributes over union
-- S ∩ (⋃ i, A i) = ⋃ i, (S ∩ A i)
-- Compare with:  P ∧ (∃ i, Q i) ↔ ∃ i, (P ∧ Q i)
example : S ∩ (⋃ i, A i) = ⋃ i, (S ∩ A i) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hS, i, hAi⟩
    exact ⟨i, hS, hAi⟩
  · rintro ⟨i, hS, hAi⟩
    exact ⟨hS, i, hAi⟩

-- Union distributes over intersection
-- S ∪ (⋂ i, A i) = ⋂ i, (S ∪ A i)
-- Compare with:  P ∨ (∀ i, Q i) ↔ ∀ i, (P ∨ Q i)
example : S ∪ (⋂ i, A i) = ⋂ i, (S ∪ A i) := by
  ext x
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · rintro (hS | hA)
    · intro i; left; exact hS
    · intro i; right; exact hA i
  · intro h
    by_cases hS : x ∈ S
    · left; exact hS
    · right; intro i
      rcases h i with hS' | hAi
      · contradiction
      · exact hAi


-- ============================================================================
-- ## Part 5: De Morgan's Laws for Indexed Families
-- ============================================================================

/-
These generalize De Morgan's laws from Lecture 10:

  (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ    "not (exists i) = forall i, not"
  (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ    "not (forall i) = exists i, not"

The first is constructive. The second requires classical logic (by_cases).
-/

-- De Morgan I: complement of union = intersection of complements
-- This is ¬ (∃ i, x ∈ A i) ↔ ∀ i, x ∉ A i
example : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ := by
  ext x
  rw [Set.mem_compl_iff,Set.mem_iUnion,Set.mem_iInter]
  push_neg
  rfl

-- De Morgan II: complement of intersection = union of complements
-- This is ¬ (∀ i, x ∈ A i) ↔ ∃ i, x ∉ A i   (requires classical logic!)
example : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion]
  push_neg
  rfl


-- ============================================================================
-- ## Part 6: Concrete ℕ-Indexed Examples
-- ============================================================================

/-
Let's see indexed operations in action with concrete families
indexed by ℕ. We use set-builder notation { m : ℕ | ... }.
-/

-- Define a family: A n = { m : ℕ | m ≤ n }
-- So A 0 = {0}, A 1 = {0,1}, A 2 = {0,1,2}, ...
-- These are called __sections__
-- The union ⋃ n, A n should be all of ℕ.

def A_le (n : ℕ) : Set ℕ := { m : ℕ | m ≤ n }

-- Every natural number is in some A_le n (namely, in A_le m itself)
example : ⋃ n, A_le n = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, A_le,Set.mem_univ,Set.mem_setOf_eq]
  simp
  use x  -- witness: i = x, of x ≤ x

-- The intersection ⋂ n, A_le n = {0}
-- (only 0 is ≤ every n)
example : ⋂ n, A_le n = {0} := by
  ext x
  simp only [Set.mem_iInter, A_le, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    -- x ≤ n for all n; in particular x ≤ 0
    have h0 := h 0
    linarith
  · intro h
    rw [h]
    intro n
    linarith

-- Another family: B n = { m : ℕ | n ∣ m } (multiples of n)
-- The intersection ⋂ n, B n should be {0} (only 0 is divisible by every n).

def B_div (n : ℕ) : Set ℕ := { m : ℕ | n ∣ m }

-- 0 is in every B_div n
example : (0 : ℕ) ∈ ⋂ n, B_div n := by
  rw [Set.mem_iInter]
  intro n
  show n ∣ 0
  exact dvd_zero n


-- ============================================================================
-- ## Part 7: Cartesian Product
-- ============================================================================

/-
The Cartesian product of two sets `S` and `T` is written `S ×ˢ T` in Mathlib.
Its elements are pairs `(a, b)` with `a ∈ S` and `b ∈ T`.

  p ∈ S ×ˢ T  ↔  p.1 ∈ S ∧ p.2 ∈ T

This is another instance of "sets = logic": the product is ∧!
-/

variable {β : Type*}
variable (U : Set α) (V : Set β)

-- Example: a pair is in the product iff both components are in the respective sets
example (a : α) (b : β) : (a, b) ∈ U ×ˢ V ↔ a ∈ U ∧ b ∈ V := by
  exact Set.mem_prod

-- Example: product is monotone in first argument
example (hU : U ⊆ S) : U ×ˢ V ⊆ S ×ˢ V := by
  intro p hp
  rw [Set.mem_prod] at hp ⊢
  exact ⟨hU hp.1, hp.2⟩

-- Example: product with empty set is empty
example : U ×ˢ (∅ : Set β) = ∅ := by
  ext p
  simp [Set.mem_prod]


-- ============================================================================
-- ## Part 8: Power Set
-- ============================================================================

/-
The power set `𝒫 S` is the set of all subsets of S.
In Lean, it's type is `Set (Set α)` — a set of sets!

  A ∈ 𝒫 S  ↔  A ⊆ S

Note the typing: `A : Set α` and `𝒫 S : Set (Set α)`, so `A ∈ 𝒫 S` makes sense.
-/

-- Example: every set is in the power set of univ
example : S ∈ 𝒫 (Set.univ : Set α) := by
  rw [Set.mem_powerset_iff]
  exact Set.subset_univ S

-- Example: the empty set is in every power set
example : (∅ : Set α) ∈ 𝒫 S := by
  rw [Set.mem_powerset_iff]
  exact Set.empty_subset S

-- Example: S is in its own power set
example : S ∈ 𝒫 S := by
  rw [Set.mem_powerset_iff]

-- Example: power set is monotone
example (h : S ⊆ T) : 𝒫 S ⊆ 𝒫 T := by
  intro A hA
  rw [Set.mem_powerset_iff] at hA ⊢
  exact Set.Subset.trans hA h


end IndexedFamilies


-- ============================================================================
-- ## Exercises
-- ============================================================================

section Exercises
variable {α ι : Type*}
variable (A B : ι → Set α)
variable (S T : Set α)


-- ────────────────────────────────────────────────────────────
-- Group 1: Indexed Union
-- ────────────────────────────────────────────────────────────

-- 1a. If A i ⊆ S for all i, then ⋃ i, A i ⊆ S
-- (We proved this as an example; now do it yourself.)
example (h : ∀ i, A i ⊆ S) : ⋃ i, A i ⊆ S := by
  sorry

-- 1b. ⋃ i, A i = ⋃ i, A i ∪ ∅
-- (Union with empty set doesn't change anything.)
example : ⋃ i, A i = ⋃ i, (A i ∪ ∅) := by
  sorry

-- 1c. If ∀ i, A i ⊆ B i, then ⋃ i, A i ⊆ ⋃ i, B i (monotonicity)
example (h : ∀ i, A i ⊆ B i) : ⋃ i, A i ⊆ ⋃ i, B i := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 2: Indexed Intersection
-- ────────────────────────────────────────────────────────────

-- 2a. If S ⊆ A i for all i, then S ⊆ ⋂ i, A i
example (h : ∀ i, S ⊆ A i) : S ⊆ ⋂ i, A i := by
  sorry

-- 2b. ⋂ i, A i ⊆ ⋂ i, A i ∪ S
-- (Each A i is contained in A i ∪ S, so the intersection is too.)
example : ⋂ i, A i ⊆ ⋂ i, (A i ∪ S) := by
  sorry

-- 2c. If ∀ i, A i ⊆ B i, then ⋂ i, A i ⊆ ⋂ i, B i (monotonicity)
example (h : ∀ i, A i ⊆ B i) : ⋂ i, A i ⊆ ⋂ i, B i := by
  sorry

-- 2d. Indexed intersection is contained in indexed union
-- (assuming the index type is nonempty)
example [Nonempty ι] : ⋂ i, A i ⊆ ⋃ i, A i := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 3: Distributivity
-- ────────────────────────────────────────────────────────────

-- 3a. S ∩ (⋃ i, A i) = ⋃ i, (S ∩ A i)
-- (Intersection distributes over indexed union.)
example : S ∩ (⋃ i, A i) = ⋃ i, (S ∩ A i) := by
  sorry

-- 3b. S ∪ (⋂ i, A i) = ⋂ i, (S ∪ A i)
-- (Union distributes over indexed intersection.)
example : S ∪ (⋂ i, A i) = ⋂ i, (S ∪ A i) := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 4: De Morgan's Laws for Indexed Families
-- ────────────────────────────────────────────────────────────

-- 4a. (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ
example : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ := by
  sorry

-- 4b. (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ
-- Hint: use push_neg or by_cases
example : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 5: Concrete ℕ-indexed exercises
-- ────────────────────────────────────────────────────────────

-- 5a. Show that 5 ∈ ⋃ n, A_le n
example : (5 : ℕ) ∈ ⋃ n, A_le n := by
  sorry

-- 5b. Show that 0 ∈ ⋂ n, A_le n
example : (0 : ℕ) ∈ ⋂ n, A_le n := by
  sorry

-- 5c. Define C n = { m : ℕ | m < n }. Show ⋃ n, C n = Set.univ.
def C_lt (n : ℕ) : Set ℕ := { m : ℕ | m < n }

example : ⋃ n, C_lt n = Set.univ := by
  sorry

-- 5d. Show that ⋂ n, C_lt n = ∅.
-- (There is no natural number that is < every n; in particular not < 0.)
example : ⋂ n, C_lt n = ∅ := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 6: Cartesian Product
-- ────────────────────────────────────────────────────────────

variable {β : Type*}
variable (U : Set α) (V W : Set β)

-- 6a. Product is monotone in the second argument
example (hV : V ⊆ W) : U ×ˢ V ⊆ U ×ˢ W := by
  sorry

-- 6b. Product distributes over union (in second argument)
-- U ×ˢ (V ∪ W) = (U ×ˢ V) ∪ (U ×ˢ W)
example : U ×ˢ (V ∪ W) = (U ×ˢ V) ∪ (U ×ˢ W) := by
  sorry

-- 6c. Product distributes over intersection (in second argument)
-- U ×ˢ (V ∩ W) = (U ×ˢ V) ∩ (U ×ˢ W)
example : U ×ˢ (V ∩ W) = (U ×ˢ V) ∩ (U ×ˢ W) := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 7: Power Set
-- ────────────────────────────────────────────────────────────

-- 7a. If S ⊆ T, then 𝒫 S ⊆ 𝒫 T (monotonicity)
example (h : S ⊆ T) : 𝒫 S ⊆ 𝒫 T := by
  sorry

-- 7b. S ∩ T ∈ 𝒫 S
example : S ∩ T ∈ 𝒫 S := by
  sorry

-- 7c. If S ∈ 𝒫 T and U ∈ 𝒫 T, then S ∪ U ∈ 𝒫 T
-- (The power set is closed under union.)
example (hA : S ∈ 𝒫 T) (hB : U ∈ 𝒫 T) : (S ∪ U) ∈ 𝒫 T := by
  sorry


-- ────────────────────────────────────────────────────────────
-- Group 8: Challenge Problems
-- ────────────────────────────────────────────────────────────

-- CHALLENGE 1: Indexed union of intersections ⊆ intersection of indexed unions
-- ⋃ i, (A i ∩ S) ⊆ (⋃ i, A i) ∩ S
example : ⋃ i, (A i ∩ S) ⊆ (⋃ i, A i) ∩ S := by
  sorry

-- CHALLENGE 2: Actually, the above is an equality.
-- Prove the reverse inclusion to show it.
example : (⋃ i, A i) ∩ S ⊆ ⋃ i, (A i ∩ S) := by
  sorry

-- CHALLENGE 3: ⋂ i, (A i ∪ S) ⊇ (⋂ i, A i) ∪ S
example : (⋂ i, A i) ∪ S ⊆ ⋂ i, (A i ∪ S) := by
  sorry




end Exercises
