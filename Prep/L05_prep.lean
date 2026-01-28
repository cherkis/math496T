import MIL.Common

/-
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
