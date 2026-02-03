import MIL.Common

/- # Lecture 6

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


/- `for every` is a **function**,
   `there exists` is a **pair**.


Proposition/Hypothesis     Universal Quantifier   Existential Quantifier
Formation                  `∀ x, P x`              `∃ x, P x`

Construction               `intro`                  `use a`

Elimination                `apply` or               `obtain ⟨a,ha⟩ := h`
                           `have hh := h a`
-/

-- To have some concrete examples, we shall play with Natural and Real numbers, even though we did not introduce then yet.
-- We are to introduce ℕ in the next lecture.


example : ∀ n : ℕ, 0 ≤ n*n := sorry

-- here use linarith tactic at the very end to do simple arithmetic inequalities
example (f : ℝ → ℝ) (h : ∃ ε >0, ∀ x < ε , f x < 1) : ∃ ε , ∀ x < ε , f (2*x) < 1 := sorry


-- Let us define even and odd numbers
def isEven (n : ℕ) := ∃ m, n = 2 * m
def isOdd (n : ℕ) := ∃ m, n = 2 * m + 1

example : ∀ n : ℕ, isEven (2*n) := sorry
example : ∀ n : ℕ, isOdd (2 * n + 1) := sorry
example : ∀ n : ℕ, isOdd (2 * n + 3) := sorry

example : ∀ n : ℕ, isEven n → isOdd (n+1) := sorry

example : ∀ n : ℕ, isOdd n → isEven (n+1) := sorry


example : ¬ ∀ n : ℕ, isOdd n := sorry

-- NOTE:proving  `¬ ∀ n : ℕ, isEven n` requires more tools.  To be revisited later.


-- might need `linarith` tactic here
example : ∀ x : ℝ, ∃ y : ℝ, x * y = x := sorry
example: ∃ y : ℝ, ∀ x : ℝ, x*y = x := sorry

theorem predExists : ∀ x : ℝ, ∃ y : ℝ, x = y + 1 := sorry
-- exchange the order of the two quantifiers in the last theorem,
-- then prove or disprove the resulting statement
-- you might need to use `linarith` again

-- Now let's prove that `theorem predExists` does NOT hold for ℕ
-- amazingly `linarith` again comes to a rescue.
example : ¬ ∀ x : ℕ, ∃ y : ℕ, x = y + 1 := sorry

-- try again, proving a statement over ℝ and its negation over ℕ :
example : ∀ x : ℝ, ∃ y, x = y + 5 := sorry

example : ¬ ∀ x : ℕ, ∃ y, x = y+5 := sorry

-- State and then prove or disprove the following statements:
-- "All integers are not odd" and "Not all integers are odd"

-- Again, completing the even analogue of this exercise requires more tools.
