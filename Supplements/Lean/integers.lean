import MIL.Common
-- ## Integers

/-
There are two constructors for integers, `Int.ofNat : Nat → Int` and
`Int.negSucc : Nat → Int`.
`ofNat` reflects that we can think of any natural number as an integer, but
these are not all the integers, so we need another constructor `negSucc` to
catch all the negative integers. To avoid double-counting 0, `negSucc n`
corresponds to `-(n+1)`.

-/

-- Lean uses inductive types again
inductive Int' : Type where
  | ofNat   : Nat → Int'
  | negSucc : Nat → Int'

def negThree : Int' := Int'.negSucc 2



-- # Addition

def Int'.subNatNat (m n : Nat) : Int' :=
  match (n - m : Nat) with
  | 0          => Int'.ofNat (m - n)  -- m ≥ n
  | Nat.succ k => Int'.negSucc k

def Int'.add : Int' → Int' → Int'
    -- m+n=m+n
  | Int'.ofNat m  , Int'.ofNat n   => Int'.ofNat (m + n)
    -- m + -(n + 1) = m - (n + 1)
  | Int'.ofNat m  , Int'.negSucc n => Int'.subNatNat m (Nat.succ n)
    -- -(m + 1) + n = n - (m + 1)
  | Int'.negSucc m, Int'.ofNat n   => Int'.subNatNat n (Nat.succ m)
    -- -(m + 1) + -(n + 1) = -(((m + n) + 1) + 1)
  | Int'.negSucc m, Int'.negSucc n => Int'.negSucc (Nat.succ (m + n))

-- # Subtraction

def Int'.negOfNat : Nat → Int'
  | 0      => Int'.ofNat 0
  | Nat.succ m => Int'.negSucc m

def Int'.neg : Int' → Int'
  | Int'.ofNat n   => Int'.negOfNat n
  | Int'.negSucc n => Int'.ofNat $ Nat.succ n

def Int'.sub : Int' → Int' → Int' :=
  fun a => fun b => Int'.add a $ Int'.neg b



-- # Nat cast to Int

/-
Now we have a conflict between two types of subtraction,
Nat.sub versus Int.sub. How should we resolve `3 - 5`?

Unless specified explicitly or by type inference, Lean
will interpret a string of digits a natural number.
So `3 - 5 : Nat` and the term equals `0 : Nat`.
How then do we specify if we DID mean to use Integer subtraction?

We can use type inference! Lean will parse `3` as a term of type `Nat`,
but if we demand that the symbol be considered another type,
Lean will try to accommodate. Namely, `(3 : Int)` is a term of
type `Int`. Although, if we try to force Lean to reinterpret a
symbol as a term of a different type, Lean will throw an error
in the event that no pre-declared means of type coercion exists.

The other method is to be completely explicit, so we could
write integer subtraction `3-5` as `Int.sub (Int.ofNat 3) (Int.ofNat 5)`
-/


#check 2
#check (2 : Int)
--#check (2 : List Nat)   --This throws an error
#eval 3 - 5
#eval (3 : Int) - 5
#eval Int.sub (Int.ofNat 3) (Int.ofNat 5)


example (n : Nat) : 0 - ((n : Int) - 2) = 2 - n := by
  rw [Int.zero_sub, Int.neg_sub]

#check Int.ofNat_inj

example (a b : Nat) (h : (a : Int) = (b : Int)) : a = b := by
  exact Int.ofNat_inj.mp h


-- # Order

inductive Int'.NonNeg : Int' → Prop where
  | mk {n : Nat} : NonNeg (Int'.ofNat n)

def Int'.le : Int' → Int' → Prop :=
  fun a => fun b => Int'.NonNeg (Int'.sub b a)

example : Int'.le (negThree) (Int'.ofNat 0) := by
  unfold Int'.le
  unfold negThree
  unfold Int'.sub
  unfold Int'.neg
  dsimp
  unfold Int'.add
  dsimp
  exact Int'.NonNeg.mk


-- # Nat in Bijection with Int
theorem even_or_odd : ∀ n : Nat, (∃ k, n = 2*k) ∨ (∃ k, n = 2*k + 1) := by
  intro n
  induction' n with n ih
  · left
    exists 0
  · rcases ih with (n_even | n_odd)
    · right
      obtain ⟨k, hk⟩ := n_even
      exists k
      rw [hk]
    · left
      obtain ⟨q, hq⟩ := n_odd
      exists q + 1
      rw [hq]
      omega

theorem zero_not_odd : ¬ (∃ k, 0 = 2*k + 1) := by
  push_neg
  intro k
  apply Nat.zero_ne_add_one

theorem not_even_and_odd : ∀ n : Nat, ¬((∃ k, n = 2*k) ∧ (∃ k, n = 2*k + 1)) := by
  intro n
  push_neg
  rintro ⟨k, hk⟩
  intro q
  rw [hk]
  intro h
  clear n hk
  rcases lt_or_ge q k with (qltk | kleq)
  · apply zero_not_odd
    exists k-(q+1)
    rw [Nat.mul_sub, ←Nat.sub_add_comm, Nat.mul_add, h, add_assoc, Nat.sub_self]
    apply Nat.mul_le_mul_left
    exact qltk
  · suffices : 2*q - 2 * k + 1 = 0
    · apply zero_not_odd
      exists q - k
    rw [←Nat.sub_add_comm, h, Nat.sub_self]
    apply Nat.mul_le_mul_left
    exact kleq

theorem eq_of_sum_eq : ∀ {n m : Nat}, n + n = m + m → n = m := by
  intro n m
  intro h
  apply le_antisymm
  · contrapose! h
    apply ne_of_gt
    exact add_lt_add h h
  · contrapose! h
    apply ne_of_lt
    apply add_lt_add h h

def zigzag : Int → Nat
  | Int.ofNat n => n+n
  | Int.negSucc n => n+n+1

theorem zigzag_inj : Function.Injective zigzag := by
  intro x
  match x with
  | Int.ofNat n =>
    intro y
    match y with
    | Int.ofNat m =>
      intro h
      dsimp [zigzag] at h
      congr
      exact eq_of_sum_eq h
    | Int.negSucc m =>
      intro h
      dsimp [zigzag] at h
      exfalso
      apply not_even_and_odd (n+n)
      constructor
      · exists n
        rw [two_mul]
      · exists m
        rw [h, two_mul]
  | Int.negSucc n =>
    intro y
    match y with
    | Int.ofNat m =>
      intro h
      dsimp [zigzag] at h
      exfalso
      apply not_even_and_odd (n+n+1)
      constructor
      · exists m
        rw [h, two_mul]
      · exists n
        rw [two_mul]
    | Int.negSucc m =>
      intro h
      dsimp [zigzag] at h
      congr
      let claim := add_right_cancel h
      exact eq_of_sum_eq claim

theorem zigzag_surj : Function.Surjective zigzag := by
  intro n
  let claim := even_or_odd n
  rcases claim with (⟨k, hk⟩|⟨k, hk⟩)
  · exists Int.ofNat k
    dsimp [zigzag]
    rw [hk, two_mul]
  · exists Int.negSucc k
    dsimp [zigzag]
    rw [hk, two_mul]
