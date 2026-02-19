-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod

/-! # Homework 3: Sets and Set Operations
Based on Lectures 10–11. Prove properties of sets using
extensionality, indexed families, cartesian products, and power sets.
-/

section

variable {α ι : Type*}
variable (A : ι → Set α)
variable (S T U : Set α)

-- Symmetric difference: elements in exactly one of S and T.
-- Use `ext`, `constructor`, and careful case analysis.
@[autogradedProof 10]
theorem problem1 : (S \ T) ∪ (T \ S) = (S ∪ T) \ (S ∩ T) := by
  sorry
  done

-- Complement of a union with an indexed union.
-- Combine De Morgan for indexed unions with De Morgan for binary union.
@[autogradedProof 10]
theorem problem2 : (S ∪ ⋃ i, A i)ᶜ = Sᶜ ∩ ⋂ i, (A i)ᶜ := by
  sorry
  done

-- Power set of an intersection equals the intersection of power sets.
-- Unfold `𝒫` using `Set.mem_powerset_iff` and use the fact that
-- `X ⊆ S ∩ T ↔ X ⊆ S ∧ X ⊆ T`.
@[autogradedProof 10]
theorem problem3 : 𝒫 (S ∩ T) = 𝒫 S ∩ 𝒫 T := by
  sorry
  done

-- Subset and complement interaction.
-- If S ⊆ T, then the complement of T is contained in the complement of S.
-- This is the contrapositive for sets!
-- Then use this to show: if S ⊆ T, then S ∩ Tᶜ = ∅.
@[autogradedProof 10]
theorem problem4 (h : S ⊆ T) : S ∩ Tᶜ = ∅ := by
  sorry
  done

-- Cartesian product meets indexed intersection.
-- Prove: (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i)
-- Unfold using `Set.mem_prod` and `Set.mem_iInter`,
-- then specialize the hypotheses.
variable {β : Type*}
variable (B : ι → Set β)

@[autogradedProof 10]
theorem problem5 : (⋂ i, A i) ×ˢ (⋂ i, B i) ⊆ ⋂ i, (A i ×ˢ B i) := by
  sorry
  done

end
