/-

A collection of Tactics used in Math 496T, in sequence, with explanations

-/

/-
~~ intro ~~

Whenever a goal is of the form `⊢ P → Q`, the tactic
`intro hp` adds a hypothesis `hp : P` and changes the goal to `⊢ Q`.
(the name `hp` is arbitrarily chosen, any well-formed variable name will suffice)

Verbal Intuition:
`intro hp` may be read as "Let hp be a term of type P," or if P is a proposition,
you can read it as "Let hp be a proof of P."

-/
example {P : Prop} : P → P := by
  -- goal is `⊢ P → P` and `P : Prop` is the only hypothesis
  intro hp
  -- now we have a new hypothesis `hp : P` and the goal is `⊢ P`
  sorry -- This ends the proof without actually proving the statement.

/-
~~ exact ~~

If the goal is of the form `⊢ P` and there's a hypothesis `hp : P`,
the tactic `exact hp` will close out the goal and complete the proof.

Verbal Intuition:
`exact hp` may be read as "We have contructed hp, a term of type P,
so our proof is complete."

Now we can complete the example from above:
-/
example {P : Prop} : P → P := by
  -- goal is `⊢ P → P` and `P : Prop` is the only hypothesis
  intro hp
  -- now we have a new hypothesis `hp : P` and the goal is `⊢ P`
  exact hp
  -- our new tactic state says "No goals," so we are done.

/-
~~ contradiction ~~

For any goal, if there is a hypothesis `h : False`,  then
the tactic `contradiction` will close out the goal.

Verbal Intuition:
`contradiction` may be read as
"We have reached a contradiction following from our hypotheses,
so the proof is complete."

-/
example {P : Prop} : False → P := by
  intro h
  -- `h : False` is one of our hypotheses
  contradiction
  -- our new tactic state says "No goals," so we are done.

/-
~~ apply ~~

If the goal is of the form `⊢ Q` and there is a function/theorem `h : P → Q`,
the tactic `apply h` changes the goal to `⊢ P`.

Verbal Intuition:
`apply h` may be read as "We know by h that P implies Q, so to prove Q, we
can just prove P."

-/
example {P Q : Prop} (h : P → Q) (hp : P) : Q := by
  -- we have a hypothesis `h : P → Q` and a goal `⊢ Q`
  apply h
  -- Now our goal is `⊢ P`
  exact hp

/-
~~ dsimp ~~

`dsimp` unpacks the definitions of terms
-/
<<<<<<< HEAD

/-
~~ constructor ~~


-/

/-
~~ rintro ~~


-/

/-
~~ left ~~


-/

/-
~~ right ~~


-/

/-
~~ obtain ~~


-/

/-
~~ have ~~


-/

/-
~~ by_cases ~~


-/

/-
~~ rcases ~~


-/

/-
~~ cases ~~


-/

/-
~~ rfl ~~


-/

/-
~~ induction' ~~


-/
=======
>>>>>>> 8f12f1d (Creates Lean folder in Supplements and populates)
