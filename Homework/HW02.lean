-- import AutograderLib
import Mathlib.Tactic

/-! # Homework 2: Mathematical Induction
Playing with __addition__ on our natural numbers.
-/


-- Let us define our own natural numbers:
inductive myNat where
  | zero : myNat
  | succ : myNat → myNat

open myNat
-- with addition
def addLeft : myNat → myNat → myNat
  | zero, m => m
  | succ n, m => succ (addLeft n m)
-- here we bump most of the bucket we brought, and then drop the last pebble.
-- We already proved the following theorems in class.  You can use them.
theorem succ_addLeft (n m : myNat) : addLeft (succ n) m = succ (addLeft n m) := by
dsimp [addLeft]

theorem addLeft_succ (n m : myNat) : addLeft n (succ m) = succ (addLeft n m) := by
induction' n with n ih
. rfl
. dsimp [addLeft]
  rw [ih]


-- Now define a different addition:
def addLeft' : myNat → myNat → myNat
  | zero, m => m
  | succ n, m => addLeft' n (succ m)
-- where we first drop one pebble, then bump the rest of the bucket.

/- Prove that these two additions are the same.
   Advice: Write your proof on paper first, then translate it to Lean.
   You will need to use induction on n, and the theorems we proved above.
   Be careful with your quantifiers.
-/
theorem problem1 : ∀ n m : myNat, addLeft n m = addLeft' n m := by
  sorry


-- Above additions were inductive on the first argument.  Now define an addition that is inductive on the second argument:
def addRight : myNat → myNat → myNat
  | n, zero => n
  | n, succ m => addRight (succ n) m

-- Prove that it is equivalent to the previous two additions:
-- First change the order of quantifiers to make it easier to prove:
theorem problem2 : (∀ n m : myNat, addLeft n m = addRight n m) ↔ (∀ m n : myNat, addLeft n m = addRight n m) := by
  sorry

-- Recall some theorems we proved in class:
theorem zero_addLeft (n : myNat) : addLeft n zero = n := by
  induction' n with n ih
  · rfl
  . rw [addLeft]
    rw [ih]

theorem problem3 : ∀ m n : myNat, addLeft n m = addRight n m := by
  sorry
