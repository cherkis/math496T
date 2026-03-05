-- import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

/-! # Homework 5: Functions, Cancellation, and Images/Preimages
-/

section

variable {α β γ δ : Type*}

/- In category theory **injective** and **surjective** maps are called **monic** and **epic**. They are defined by
**Monic** : `f ∘ g = f ∘ h ⇒ g = h`
and
**Epic** : `g ∘ f = h ∘ f ⇒ g = h`
-/

-- (1) Injective iff left-cancellable.
@[autogradedProof 11]
theorem problem1 (c : γ) (f : α → β) :
    Function.Injective f ↔
    ∀ (g₁ g₂ : γ → α), f ∘ g₁ = f ∘ g₂ → g₁ = g₂ := by
  sorry
  done

-- (2) Injective idempotent is identity.
@[autogradedProof 7]
theorem problem2 {f : α → α}
    (hff : f ∘ f = f) (hinj : Function.Injective f) : f = id := by
  sorry
  done

-- Set-theoretic part
variable (f : α → β)
variable (S T : Set α)
variable (U V : Set β)

-- (3) Preimage respects intersection.
@[autogradedProof 4]
theorem problem3 : f ⁻¹' (U ∩ V) = (f ⁻¹' U) ∩ (f ⁻¹' V) := by
  sorry
  done

-- (4) Preimage respects union.
@[autogradedProof 4]
theorem problem4 : f ⁻¹' (U ∪ V) = (f ⁻¹' U) ∪ (f ⁻¹' V) := by
  sorry
  done

-- (5) Preimage respects complement.
@[autogradedProof 4]
theorem problem5 : f ⁻¹' (Uᶜ) = (f ⁻¹' U)ᶜ := by
  sorry
  done

-- (6) Image respects union.
@[autogradedProof 4]
theorem problem6 : f '' (S ∪ T) = (f '' S) ∪ (f '' T) := by
  sorry
  done

-- (7) Image/preimage Galois connection.
@[autogradedProof 6]
theorem problem7 : f '' S ⊆ U ↔ S ⊆ f ⁻¹' U := by
  sorry
  done

-- (8) Image does not generally respect intersection.
-- Provide an explicit counterexample where equality fails.
@[autogradedProof 5]
theorem problem8 :
    ∃ (A B : Set ℕ) (g : ℕ → ℕ),
      (g '' (A ∩ B)) ≠ (g '' A ∩ g '' B) := by
  sorry
  done

-- (9) Cancellation application.
-- Show that if g ∘ f is bijective, then f is injective and g is surjective.
@[autogradedProof 5]
theorem problem9 {f₁ : α → β} {g : β → γ}
    (h : Function.Bijective (g ∘ f₁)) :
    Function.Injective f₁ ∧ Function.Surjective g := by
  sorry
  done

end
