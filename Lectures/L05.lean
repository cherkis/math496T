import MIL.Common

/- # Lecture 5

Proposition/Hypothesis     Implication:  Conjunction               Disjunction                  Equivalence
Formation                  `P → Q`        `P ∧ Q`                    `P ∨ Q`                     `P ↔ Q`

Construction                `intro`       `constructor`            `left` or `right`            `constructor`

Elimination                 `apply`       `obtain ⟨ha,hb⟩:=h`      `rcases h with ha | hb`      `rw [h]` or `rw [← h]`
(of `h`)                                  or  `h.left`              or `obtain (ha | hb) := h`  or `h.mp` or `h.mpr`
                                          and `h.right`

Not: is `P → False`
Equivalence `P ↔ Q` is a pair of implications
            `P → Q` (modus ponens) and `Q → P` (modus ponens reverse)

-/



variable (P Q R : Prop)

-- Prove these logical equivalences:

example : ((P ∧ Q) → R )↔ (P → Q → R) := sorry

example : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := sorry

example : (P → (Q ∨ R)) ↔ ((P ∧ ¬ Q) → R) := sorry

/- # Implication:
In `P → Q`,
`P` is the hypothesis,
`Q` is the conclusion,
`P` is sufficient for `Q` or
`Q` is necessary for `P`.

## Terminology:
`Q → P` is the converse,
`¬ P → ¬ Q` is the inverse,
`¬ Q → ¬ P` is the contrapositive.
-/

-- Practice all problems from prior lectures using the above table


/-
# Quantifiers: ∀ and ∃

## Existential quantifier: ∃
"There exists x, such that P(x)":
`∃ (x:α), (P x)` is type of __pairs__,
its terms is `(a, hpa)` with `a` a term of type `α` and `hpa` a proof of the proposition `P a`

Tactic:

`use [value]`
and
`obtain`
-/

example : ∃ n : ℕ , n * n = 16 := ⟨ 4,rfl⟩

example : ∃ n : ℕ , n * n = 2*n + 3 := by
use 3

/-
## Universal Quantifier: ∀
"For all x, we have P x"
`∀ x:α , P x` is a __function__
for every `x` of type `α` it produces a proof of the proposition `P x`

Tactics:  same as for a function
`intro` and `apply`
-/

example : ∀ n : ℕ, 0 ≤ n*n := sorry

-- here use linarith tactic at the very end to do simple arithmetic inequalities
example (f : ℝ → ℝ) (h : ∃ ε >0, ∀ x < ε , f x < 1) : ∃ ε , ∀ x < ε , f (2*x) < 1 := sorry
