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
-- Pattern matching
-- __obtain__


variable (P Q R : Prop)


theorem elimination : (P ∨ Q) ∧ ¬ P → Q := by
rintro ⟨hp | hq, np⟩
contradiction
exact hq
done

example : (P ∨ Q) ∧ ¬ P → Q := by
intro h
obtain ⟨h1,h2⟩ := h
obtain (ha | hb) := h1
. contradiction
. exact hb

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
. exact ⟨hp,by left; apply hq⟩
. exact ⟨hp,by right; apply hr⟩
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

example : ( P → Q ) ↔ (¬ P ∨ Q) := by
constructor
intro hpq
by_cases h : P
right
apply hpq
exact h
left
exact h
rintro (np | hq) hp
contradiction
exact hq
done

example : ¬ ( P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
constructor
. intro h
  constructor
  intro hp
  apply h
  left
  exact hp
  intro hq
  apply h
  right
  exact hq
. rintro h (hp | hq)
  apply h.left
  exact hp
  apply h.right
  exact hq
  done
done


-- `by_cases` and `have`
example : ( P → Q) ↔ ( P ∧ ¬ Q) → (Q ∧ ¬ Q) := by
constructor
. rintro q_of_p ⟨hp,hnq⟩
  constructor
  apply q_of_p
  exact hp
  exact hnq
. intro h hp
  by_cases hq : Q
  . exact hq
  . have hqnq : Q ∧ ¬ Q := by apply h; constructor; exact hp; exact hq -- have
    exact hqnq.left
done

example : (¬ P ↔ Q) ↔ ((P → ¬ Q) ∧ (¬ Q → P)) := by
constructor
. intro h
  constructor
  . intro hp hq
    have hnp := h.mpr hq
    contradiction
  . intro hnq
    by_cases hp : P
    exact hp
    exfalso
    apply hnq
    apply h.mp
    exact hp
. intro ⟨ha,hb⟩
  constructor
  intro np
  by_cases hq : Q
  exact hq
  exfalso
  apply np
  apply hb
  exact hq
  intro hq hp
  apply ha hp
  exact hq
done









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
