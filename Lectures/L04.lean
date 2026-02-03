import MIL.Common

/- # Lecture 4

## Summary of Lecture 3
1. Negation and implication are functions.
2. `Prod` and `And` are pair types.
3. Tactics __exfalso__ and __contradiction__
2. Tactic __dsimp__, __constructor__, __rintro__
3. Use of `⟨ , ⟩`, `.left` and `.right` to extract parts of conjunction.


## Sum (or coproduct) or types and Or

### Sum:
-/

-- Formation rule
#check Sum -- Type → Type → Type
example (α β : Type) : Sum α β = (α ⊕ β) := rfl

-- Introduction rule
#check Sum.inl --   α → α ⊕ β
#check Sum.inr --   β → α ⊕ β

-- Elimination rule
#check Sum.elim -- Sum.elim (f : α → γ) (g : β → γ) : α ⊕ β → γ
/-
(f : α → γ)    (g : β → γ)
---------------------------  Sum.elim
α ⊕ β → γ
-/

-- ### Or:
#check Or -- Prop → Prop → Prop
#check Or.inl -- P → P ∨ Q
#check Or.inr -- Q → P ∨ Q
#check Or.elim -- Or.elim (h : a ∨ b) (left : a → c) (right : b → c) : c


-- ### Tactics:
-- __left__ and __right__
-- Pattern matching with __rintro__
-- __obtain__


variable (P Q R : Prop)


theorem elimination : (P ∨ Q) ∧ ¬ P → Q := by
rintro ⟨(hp | hq), np⟩  -- Pattern matching
.  exfalso
   apply np
   exact hp
.  exact hq


example : (P ∨ Q) ∧ ¬ P → (Q ∨ R) := by
intro h
obtain ⟨h1,h2⟩ := h
obtain (ha | hb) := h1
. contradiction
. left
  exact hb

-- To get used to the notation, try the following examples
example : (P ∨ Q) → (Q ∨ P) := sorry

example : (P ∧ R) → (Q ∨ P) := sorry


-- Equivalence as a pair:
-- `P ↔ Q` is really `P → Q` and `Q → P` and
-- for `h : P ↔ Q` we have `h.mp : P → Q` and `h.mpr : Q → P`

example : (P ∨ Q) ↔ (Q ∨ P) := sorry

example : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (R ∧ Q) := sorry

-- Let's explore proving the equivalence `P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R)`
--  first in human language, then in LEAN


/-
__Proof of P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)__
We need to prove both directions.

## (→) Left to Right: P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
Assume P ∨ (Q ∧ R). We must show both (P ∨ Q) and (P ∨ R).

. Case 1: P holds.

Then P ∨ Q holds (by left disjunct).
And P ∨ R holds (by left disjunct).
So (P ∨ Q) ∧ (P ∨ R) holds.

. Case 2: Q ∧ R holds.

Then Q holds, so P ∨ Q holds (by right disjunct).
And R holds, so P ∨ R holds (by right disjunct).
So (P ∨ Q) ∧ (P ∨ R) holds.

## (←) Right to Left: (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)
Assume (P ∨ Q) ∧ (P ∨ R). We must show P ∨ (Q ∧ R).

. Case 1: P holds.

Then P ∨ (Q ∧ R) holds immediately (by left disjunct).

. Case 2: P does not hold.

From P ∨ Q and ¬P, we conclude Q must hold.
From P ∨ R and ¬P, we conclude R must hold.
Therefore Q ∧ R holds.
So P ∨ (Q ∧ R) holds (by right disjunct).

## Both directions are proven, establishing the equivalence. Q.E.D.
-/


-- Now let's translate this proof into LEAN
example : P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R) := by
-- We need to prove both directions
constructor
-- (→) Left to Right: P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
-- Assume P ∨ (Q ∧ R). We must show both (P ∨ Q) and (P ∨ R).
. intro p_or_qr
  obtain hp | hqr := p_or_qr
-- Case 1: P holds.
-- Then P ∨ Q holds (by left disjunct).
  . have p_or_q : P ∨ Q := by left; exact hp
-- And P ∨ R holds (by left disjunct).
    have p_or_r : P ∨ R := by left; exact hp
-- So (P ∨ Q) ∧ (P ∨ R) holds.
    exact ⟨p_or_q, p_or_r⟩

-- Case 2: Q ∧ R holds.
  obtain ⟨hq,hr⟩ := hqr
-- Then Q holds, so P ∨ Q holds (by right disjunct).
  have p_or_q : P ∨ Q := by right; exact hq
-- And R holds, so P ∨ R holds (by right disjunct).
  have p_or_r : P ∨ R := by right; exact hr
-- So (P ∨ Q) ∧ (P ∨ R) holds.
  exact ⟨ p_or_q, p_or_r⟩

-- ## (←) Right to Left: (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)
-- Assume (P ∨ Q) ∧ (P ∨ R). We must show P ∨ (Q ∧ R).
. intro h
-- Case 1: P holds.  **Note, this proof is NOT constructive** **But it does NOT have to be**
  by_cases hp : P
-- Then P ∨ (Q ∧ R) holds immediately (by left disjunct).
  . left
    exact hp
-- Case 2: P does not hold.
-- From P ∨ Q and ¬P, we conclude Q must hold.
  have ⟨ hpq, hpr ⟩ := h
  have hq : Q := by
   obtain hp | hq := hpq
   . contradiction
   . exact hq
-- From P ∨ R and ¬P, we conclude R must hold.
  have hr : R := by
   obtain hp | hr := hpr
   . contradiction
   . exact hr
-- Therefore Q ∧ R holds.
  have hqr : Q ∧ R := by constructor; exact hq; exact hr
-- So P ∨ (Q ∧ R) holds (by right disjunct).
  right
  exact hqr
-- ## Both directions are proven, establishing the equivalence. Q.E.D.
done

-- Here is a stronger, constructive, proof.

example : P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R) := by
constructor
rintro (hp | ⟨hq, hr⟩)
. constructor
  left
  exact hp
  left
  exact hp
. constructor
  right
  exact hq
  right
  exact hr
rintro ⟨(hp | hq), (hpp | hr)⟩
left; exact hp
left; exact hp
left; exact hpp
right
constructor
exact hq
exact hr
done

-- Let's annotate it
example : P ∨ Q ∧ R ↔ (P ∨ Q) ∧ (P ∨ R) := by
-- We need to prove both directions
constructor
-- ## Proving forward direction: P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
rintro (hp | ⟨hq, hr⟩)
-- Assume P or Q ∧ R
-- First case: P holds
-- To prove (P ∨ Q) ∧ (P ∨ R), need to prove (P ∨ Q), then (P ∨ R)
. constructor
  -- proving P ∨ Q, by proving P
  left
  exact hp
  -- proving P ∨ R, by proving P
  left
  exact hp
-- Second case: Q and R hold
-- To prove (P ∨ Q) ∧ (P ∨ R), need to prove (P ∨ Q), then (P ∨ R)
. constructor
  -- We prove P or Q by proving Q
  right
  exact hq
  -- We prove P or R by proving R
  right
  exact hr
-- ## Proving reverse direction: (P ∨ Q) ∧ (P ∨ R) → P ∨ Q ∧ R
-- Suppose (P or Q) and (P or R) holds
rintro ⟨(hp | hq), (hpp | hr)⟩
-- then there are four cases
-- P holds and P holds:
left; exact hp -- We prove P ∨ (Q ∧ R) by proving P
-- P holds and R holds
left; exact hp -- We prove P ∨ (Q ∧ R) by proving P
-- Q holds and P holds
left; exact hpp -- We prove P ∨ (Q ∧ R) by proving P
-- Q holds and R holds
right  -- We prove P ∨ (Q ∧ R) by proving Q and R
constructor
-- first prove Q
exact hq
-- then prove R
exact hr
done

/-
Here is the same proof in Human language:
# Proof of P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)
We establish the equivalence by proving both implications.

## Forward Direction: P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
Assume P ∨ (Q ∧ R). We must show both (P ∨ Q) and (P ∨ R).

Case 1: If P holds, then both P ∨ Q and P ∨ R hold immediately, giving us the conjunction (P ∨ Q) ∧ (P ∨ R).

Case 2: If Q ∧ R holds, then Q holds (so P ∨ Q holds) and R holds (so P ∨ R holds), again giving us (P ∨ Q) ∧ (P ∨ R).

## Reverse Direction: (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)
Assume (P ∨ Q) ∧ (P ∨ R). We perform a case analysis on both disjunctions, yielding four cases:
(P and P), (P and R), (Q and R), (Q and R).

Cases 1-3: If P holds in either disjunction (which occurs in three of the four cases), then P ∨ (Q ∧ R) holds immediately.

Case 4: If Q holds (from P ∨ Q) and R holds (from P ∨ R), then Q ∧ R holds, so P ∨ (Q ∧ R) holds.

In all cases, we obtain P ∨ (Q ∧ R), completing the proof. ∎
-/


example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
rintro ⟨hp, hq | hr⟩
. left
  constructor
  exact hp
  exact hq
. right
  constructor
  exact hp
  exact hr
rintro (hpq | hpr)
constructor
exact hpq.left
left
exact hpq.right
constructor
exact hpr.left
right
exact hpr.right
done

-- in more detail
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
. intro h
  obtain ⟨hp, hqr⟩  := h
  obtain (hq | hr) := hqr
  . left
    constructor
    exact hp
    exact hq
  . right
    constructor
    exact hp
    exact hr
sorry

-- using more terms
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor
rintro ⟨hp, hq | hr⟩
. left
  exact ⟨hp,hq⟩
. right
  exact ⟨hp,hr⟩
rintro (⟨hp,hq⟩ | ⟨hp,hr⟩)
. exact ⟨hp,by left; exact hq⟩
. exact ⟨hp,by right; exact hr⟩
done

-- `by_cases`
example : (P ↔ Q) ↔ ((P ∧ Q) ∨ (¬ P ∧ ¬ Q)) := by
constructor
intro ⟨hpq, hqp⟩
by_cases h : P -- this is a CLASSICAL logic move
left
exact ⟨h, hpq h⟩
right
constructor
exact h
intro hq
apply h
apply hqp
exact hq

rintro (⟨hp,hq⟩ | ⟨hnp,hnq⟩)
constructor
. intro _
  exact hq
. intro _
  exact hp
constructor
. intro hp
  contradiction
. intro hq
  contradiction
done


-- Try proving these examples:
-- Feel free to use `by_cases` and `have`
example : ( P → Q ) ↔ (¬ P ∨ Q) := by
-- To prove if and only if we first prove
constructor
-- if (right implication)
. intro h
-- Suppose (P → Q), then we need to show ¬ P ∨ Q
-- consider two cases: Q is true or Q is not true.
  by_cases hh : Q
  -- if Q holds
  . right
  -- then the right side of the disnjunction holds
    apply hh
  -- if Q does not hold, then we are going to prove ¬ P
  left
  -- suppose the opposite: that P holds
  intro hp
  -- If Q holds then I have a contradiction
  apply hh
  -- and Q follows from P, and we assumed P, thus coming to a contradiction.
  apply h
  exact hp
  -- Therefore P does not hold.
. rintro (np | hq)
  . intro hp
    contradiction
  . intro hp1
    exact hq


example : ¬ ( P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
constructor
. rintro h
  constructor
  . intro hp
    apply h
    left
    exact hp
  . intro hq
    apply h
    right
    exact hq
. intro ⟨hp,hq⟩
  intro h
  rcases h with (h1 | h2)
  . contradiction
  . contradiction


example : ( P → Q) ↔ ( P ∧ ¬ Q) → (Q ∧ ¬ Q) := sorry


example : (¬ P ↔ Q) ↔ ((P → ¬ Q) ∧ (¬ Q → P)) := sorry









/-
Type theory can be traced back to Russell's paradox based on Cantor's theorem:
Thm: The function F : X → P(X) cannot be surjective.
( P(X) here is the power set of X.)

Proof:
Let A = { x ∈ X | x ∉ F(x)},
then A is not in the image of F,
since if A = F(a)
      then a ∈ F(a) <=> a ∈ A <=> a ∉ F(a)
      contradiction.
-/


theorem Cantor : ¬ ∃ F : X → Set X, Function.Surjective F := by
-- Assume F: X → Set X is surjective
intro ⟨F,hF⟩
-- define A
let A := { x : X | x ∉ F x}
-- surjectivity means
dsimp [Function.Surjective] at hF
-- so, let a be such that A = F(a)
let ⟨a,ha⟩ := hF A
-- then a in F(a) is equivalent to
--      a in A is equivalent to
--      a not in F(a)
have : a ∈ F a ↔ a ∉ F a := by
  nth_rw 1 [ha]
  rfl
-- contradiction
apply iff_not_self this
-- QED

/- NOTE: Only constructive logic used here. No LEM! -/

/-
Russell applies this theorem to X = collection of all sets,
and F = id.
Then A := { w | w ∉ w}, and A ∈ A <=> A ∉ A.
-/
