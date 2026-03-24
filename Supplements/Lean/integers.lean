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


-- # Nat cast to Int


-- # Addition

def Int'.subNatNat (m n : Nat) : Int' :=
  match (n - m : Nat) with
  | 0          => Int'.ofNat (m - n)  -- m ≥ n
  | Nat.succ k => Int'.negSucc k

def Int'.add : Int' → Int' → Int'
  | Int'.ofNat m  , Int'.ofNat n   => Int'.ofNat (m + n)
  | Int'.ofNat m  , Int'.negSucc n => Int'.subNatNat m (Nat.succ n)
  | Int'.negSucc m, Int'.ofNat n   => Int'.subNatNat n (Nat.succ m)
  | Int'.negSucc m, Int'.negSucc n => Int'.negSucc (Nat.succ (m + n))

-- # Integer Division

-- # Order

inductive NonNeg : Int' → Prop where
  | mk {n : Nat} : NonNeg (Int'.ofNat n)





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
