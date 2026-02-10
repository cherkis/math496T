import MIL.Common


/- # Lecture 8: Using library of theorems. Dependent Types.
Handouts: 1. Logic table, 2. Ring&group properties
-/


/- ## Practicing theorem names: -/

#check add_comm  -- a + b = b + a
#check add_assoc
#check mul_zero
#check zero_mul

-- Guess the name of relevant theorems game:
example : n * 1 = n := sorry
example : 1 * n = n := sorry

#check mul_comm

example {n m k:ℕ} : n * (m + k) = n * m + n * k := sorry
example {n m k:ℕ} : (n + m) * k = n * k + m * k := sorry
example {n m k:ℕ} : n * (m * k) = (n * m) * k := sorry

/- ## Dependent Types
- Dependent pairs:       `(a:α , b:β a)`
  form the Σ-type, written as `Σ a:α, β a`

- Dependent functions:   `(a:α) → β a`
  form the Π-type, written as `Π a:α, β a`

-/

/- Examples:
`∃ x : α, p x` is notation for `Σ x : α, p x`
`∀ x : α, p x` is notation for `Π x : α, p x`
-/


-- ## In-class activity:
-- Practice MIL>CO2_Basic>S01_Calculating.lean
-- All of that CO2_Basic section is fun.
