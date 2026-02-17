import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Parity

/- # Lecture 10: Sets and Set Operations (Part I)
New tactics: **ext, show, change, have, suffices**

## Sets in Lean
In Lean/Mathlib, `Set α` is defined as `α → Prop`.
A set is its membership predicate!
So `x ∈ S` is just `S x` — the proposition that `x` satisfies the predicate.

This means:
- Intersection `∩` is `And` (∧)
- Union `∪` is `Or` (∨)
- Complement `ᶜ` is `Not` (¬)
- Empty set `∅` is `False`
- Universal set `Set.univ` is `True`
- Subset `⊆` is `∀ x, x ∈ S → x ∈ T`

All the propositional logic from Lectures 1–6 applies directly!
-/


-- ## Key Definitions and Theorems to Know

-- How Lean thinks about sets:
#check Set            -- Set α is α → Prop
#check @Set.subset_def  -- A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B

-- Set operations unfolded to logic:
#check @Set.mem_inter_iff  -- x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B
#check @Set.mem_union      -- x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
#check @Set.mem_compl_iff  -- x ∈ Aᶜ ↔ x ∉ A
#check @Set.mem_diff       -- x ∈ A \ B ↔ x ∈ A ∧ x ∉ B

-- Empty set and universal set:
#check @Set.mem_empty_iff_false  -- x ∈ (∅ : Set α) ↔ False
#check @Set.mem_univ             -- x ∈ Set.univ  (this is a proof, not an ↔)

-- Extensionality — the key to proving set equality:
#check @Set.ext_iff  -- A = B ↔ ∀ x, x ∈ A ↔ x ∈ B

-- Set-builder notation (comprehension):
-- { x : α | P x } is notation for the set of all x satisfying P
-- Membership: x ∈ { y : α | P y } is definitionally equal to P x
#check @Set.mem_setOf_eq  -- x ∈ { y | P y } = P x

section SetBasics
variable {α : Type*}
variable (A B C : Set α)
variable (x : α)

-- ============================================================================
-- ## Part 1: Subset Proofs
-- ============================================================================

/-
To prove `A ⊆ B`, we must show: for all x, if x ∈ A then x ∈ B.
In Lean, this is just `intro x hx` followed by showing `x ∈ B`.
This is exactly the pattern we used for proving implications!
-/

-- Example: Every set is a subset of itself (reflexivity of ⊆)
example : A ⊆ A := by
  intro x hx
  exact hx

-- Example: Intersection is contained in each factor
example : A ∩ B ⊆ A := by
  intro x hx
  -- hx : x ∈ A ∩ B, which means x ∈ A ∧ x ∈ B
  exact hx.left

example : A ∩ B ⊆ B := by
  intro x hx
  exact hx.right

-- Example: Each set is contained in their union
example : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx

-- Example: Subset transitivity
-- Note the use of the `have` tactic to introduce an intermediate fact.
example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  have hxB : x ∈ B := hAB hx
  exact hBC hxB

-- Exercises: Subset proofs

example : A ∩ B ⊆ B ∩ A := by
  sorry

example : B ⊆ A ∪ B := by
  sorry

example (hAB : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  sorry

example (hAB : A ⊆ B) : A ⊆ B ∪ C := by
  sorry

example : A \ B ⊆ A := by
  sorry

-- ============================================================================
-- ## Part 2: The `ext` Tactic — Proving Set Equality
-- ============================================================================

/-
To prove two sets are equal, we use **extensionality**:
  A = B  iff  ∀ x, x ∈ A ↔ x ∈ B

The `ext x` tactic does exactly this: it introduces an arbitrary element `x`
and changes the goal from `A = B` to `x ∈ A ↔ x ∈ B`.
Then we prove the equivalence using `constructor` (just like in Lectures 3–4).
-/

-- Example: Intersection is commutative
example : A ∩ B = B ∩ A := by
  ext x
  -- Goal: x ∈ A ∩ B ↔ x ∈ B ∩ A
  constructor
  · intro ⟨ha, hb⟩
    exact ⟨hb, ha⟩
  · intro ⟨hb, ha⟩
    exact ⟨ha, hb⟩

-- Example: Union is commutative
example : A ∪ B = B ∪ A := by
  ext x
  constructor
  · rintro (ha | hb)
    · right; exact ha
    · left; exact hb
  · rintro (hb | ha)
    · right; exact hb
    · left; exact ha


-- ============================================================================
-- ## Part 3: The `show` and `change` Tactics
-- ============================================================================

/-
`show` lets you state what the current goal is, making the proof more readable.
`change` lets you replace the goal with something definitionally equal.

These are especially useful with sets, because `x ∈ A ∩ B` is
*definitionally equal* to `x ∈ A ∧ x ∈ B`, and sometimes Lean
displays the goal in a form that is hard to read.
-/

-- Example using `show` and `change`
example (x : α) (hA : x ∈ A) (hB : x ∈ B) : x ∈ A ∩ B := by
  show x ∈ A ∧ x ∈ B  -- clarify what the goal really is
  exact ⟨hA, hB⟩

-- Example: Set-builder notation
-- { x : α | P x } is a set defined by a predicate
example : (3 : ℕ) ∈ { n : ℕ | n > 2 } := by
  -- The goal is: 3 > 2
  show 3 > 2
  norm_num

example : (1 : ℕ) ∉ { n : ℕ | n > 2 } := by
  show ¬ (1 > 2)
  norm_num

-- `change` can rewrite the goal to a definitionally equal one
example : (5 : ℕ) ∈ { n : ℕ | 2 ∣ n + 1} := by
  change 2 ∣ 5 + 1
  norm_num

-- Recall `simp only` from Lecture 3: can perform simplification using only a specified list of rules or definitions or equivalences.
-- It can unfold set membership automatically:
example (x : α) (hA : x ∈ A) (hB : x ∈ B) : x ∈ A ∩ B := by
  simp only [Set.mem_inter_iff]   -- unfolds ∩ to ∧
  exact ⟨hA, hB⟩


-- ============================================================================
-- ## Part 4: The `have` and `suffices` Tactics
-- ============================================================================

/-
`have` introduces a new intermediate fact into the context.
It is like a "Claim" or "Note that" in a human proof.

`suffices` works in the other direction:
it says "it suffices to show P" and then you must
(1) show P implies the original goal, and
(2) prove P.
-/

-- Example using `have`
example (hAB : A ⊆ B) (hBC : B ⊆ C) (hx : x ∈ A) : x ∈ C := by
  have hxB : x ∈ B := hAB hx   -- "Note that x ∈ B since A ⊆ B."
  have hxC : x ∈ C := hBC hxB  -- "Note that x ∈ C since B ⊆ C."
  exact hxC

-- Example using `suffices`
example (hAB : A ⊆ B) (hx : x ∈ A) : x ∈ B ∪ C := by
  suffices hxB : x ∈ B by   -- "It suffices to show x ∈ B."
    left                     -- "Then x ∈ B ∪ C by the left disjunct."
    exact hxB
  exact hAB hx               -- "And x ∈ B follows from A ⊆ B."


-- ============================================================================
-- ## Part 5: Set Operations as Logic
-- ============================================================================

/-
This is the key insight: set operations ARE logical connectives!

  Set operation        Logic            Lean tactic pattern
  ─────────────        ─────            ────────────────────
  x ∈ A ∩ B           A ∧ B            constructor / ⟨ , ⟩ / obtain ⟨ , ⟩
  x ∈ A ∪ B           A ∨ B            left / right / rcases
  x ∈ Aᶜ              ¬ A              intro / apply
  x ∈ A \ B           A ∧ ¬B           constructor / obtain ⟨ , ⟩
  A ⊆ B               ∀ x, A → B       intro x hx
  A = B               ∀ x, A ↔ B       ext x; constructor

So every proof you did in Lectures 1–6 has a set-theory twin!
-/

-- Example: ∩ distributes over ∪ (compare with P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) from L04)
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨hA, hB | hC⟩
    · left; exact ⟨hA, hB⟩
    · right; exact ⟨hA, hC⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩


-- ============================================================================
-- ## Part 6: Using `simp` with Set Lemmas
-- ============================================================================

/-
You can also use `simp` with set membership lemmas to unfold set operations
into pure logic, and then use `tauto` to finish.
This is a powerful combination for set identities.
-/

-- Example: Same proof as above, but using simp + tauto
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

-- Example: Complement of complement
example : Aᶜᶜ = A := by
  ext x
  simp [Set.mem_compl_iff]


-- ============================================================================
-- ## Exercises
-- ============================================================================

-- Group 1: Subset proofs (use intro, exact, have)

example : A ∩ B ⊆ A ∪ C := by
  sorry

example (h : A ⊆ B) (h' : A ⊆ C) : A ⊆ B ∩ C := by
  sorry

example : A \ B ⊆ Bᶜ := by
  sorry


-- Group 2: Set equalities using `ext` (use ext, constructor, intro, exact, etc.)

-- Union is associative
example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  sorry

-- Intersection is associative
example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  sorry

-- A ∩ A = A (idempotence)
example : A ∩ A = A := by
  sorry

-- A ∪ A = A (idempotence)
example : A ∪ A = A := by
  sorry

-- Intersection with empty set
example : A ∩ ∅ = ∅ := by
  sorry

-- Union with empty set
example : A ∪ ∅ = A := by
  sorry

-- Intersection with universal set
example : A ∩ Set.univ = A := by
  sorry

-- Union with universal set
example : A ∪ Set.univ = Set.univ := by
  sorry


-- Group 3: Harder set equalities (use ext, constructor, rintro, obtain, etc.)
-- These mirror propositional logic equivalences from Lectures 3–4!

-- ∪ distributes over ∩ (compare with P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R))
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

-- Set difference in terms of intersection and complement
example : A \ B = A ∩ Bᶜ := by
  sorry

-- A ∩ complement = empty  (compare with P ∧ ¬P → False)
example : A ∩ Aᶜ = ∅ := by
  sorry

-- Complement of union (De Morgan — preview for next lecture)
-- Hint: This is ¬ (P ∨ Q) ↔ ¬P ∧ ¬Q, which you proved in L04!
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry

-- Complement of intersection (De Morgan — preview for next lecture)
-- Hint: you may need `by_cases` or `tauto` for this one, since it uses classical logic.
example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  sorry


-- Group 4: Mixed exercises using `have`, `suffices`, `show`, `change`

-- If A ⊆ B, then A ∩ C ⊆ B ∩ C (monotonicity of ∩)
-- Use `have` to name intermediate facts
example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  sorry

-- Absorption law: A ∩ (A ∪ B) = A
-- Use `suffices` or a direct proof
example : A ∩ (A ∪ B) = A := by
  sorry

-- Absorption law: A ∪ (A ∩ B) = A
example : A ∪ (A ∩ B) = A := by
  sorry


-- Group 5: Set-builder notation / comprehension

-- These exercises use { x | P x } notation

example : (2 : ℤ) ∈ { x : ℤ | x > 0 } := by
  sorry

example : (7 : ℕ) ∈ { n : ℕ | ∃ m, n = 2 * m + 1 } := by
  sorry

example : { n : ℕ | ∃ m, n = 2 * m } ⊆ { n : ℕ | ∃ m, n = 2 * m ∨ n = 2 * m + 1 } := by
  sorry

-- CHALLENGE: Show that the set of even numbers and the set of odd numbers
-- cover all natural numbers. You may use the lemma `Nat.even_or_odd`.
#check Nat.even_or_odd
example : { n : ℕ | ∃ m, n = 2 * m } ∪ { n : ℕ | ∃ m, n = 2 * m + 1 } = Set.univ := by
  sorry


end SetBasics
