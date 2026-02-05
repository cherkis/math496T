-- import AutograderLib
import Mathlib.Tactic

/-! # Homework 1
To begin with let prove the basic properties of ∧, ∨, and ¬.
-/

section

variable (P Q R T: Prop)

-- Commutativity
@[autogradedProof 5]
theorem problem1 : P ∧ Q ↔ Q ∧ P := by
  sorry
  done

@[autogradedProof 5]
theorem problem2 : P ∨ Q ↔ Q ∨ P := by
  sorry
  done

 -- Associativity
@[autogradedProof 5]
theorem problem3 : (P ∧ Q) ∧ R ↔ Q ∧ (P ∧ R) := by
  sorry
  done

@[autogradedProof 5]
theorem problem4 : (P ∨ Q) ∨ R ↔ Q ∨ (P ∨ R) := by
  sorry
  done

-- Distributivity of ∧ over ∨
@[autogradedProof 5]
theorem problem5 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
  done

-- Distributivity of ∨ over ∧
@[autogradedProof 5]
theorem problem6 : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry
  done

@[autogradedProof 5]
theorem problem7 : (P ∧ ¬ Q) → ¬ (P → Q) := by
  sorry
  done

@[autogradedProof 5]
theorem problem8 : ∀ S : Prop, ¬ P → (P → S) := by
  sorry
  done

-- This might require some logical thinking first
@[autogradedProof 5]
theorem problem9 : ∃ Q, ∀ P, P ∨ Q ↔ Q := by
  sorry
  done

@[autogradedProof 5]
theorem problem10 : ∃ Q, ∀ P, P ∨ Q ↔ P := by
  sorry
  done

end
