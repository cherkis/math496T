import MIL.Common

-- # Lecture 9: Induction practice. Summation formulas.
-- New tactics: **congrArg, linarith, calc**

/- Some formulas:
∑_{k=1}^n k = n(n + 1)/2
∑_{k=1}^n k^2 = n(n + 1)(2n + 1)/6
∑_{k=1}^n k^3 = (n(n + 1)/2)^2 = (∑_{k=1}^n k)^2
∑_{k=1}^n (2k - 1) = n^2
∑_{k=1}^n (2k) = n(n + 1)
∑_{k=1}^n k(k + 1) = n(n + 1)(n + 2)/3
-/

open Nat

def SumTo :ℕ → ℕ
   | 0 => 0
   | succ n => (succ n) + SumTo n

-- Note: this corresponds to the conventional sum from 1 to n.
def SumToOfF (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | succ m => (f (succ m)) + SumToOfF m f


-- ∑_{k=1}^n k = n(n + 1)/2
theorem SumTo_formula (n : Nat) : 2 * (SumTo n) = n * (succ n) := by
  sorry

-- ∑_{k=1}^n k^2 = n(n + 1)(2n + 1)/6
theorem SumOfSquaresTo (n : Nat) : 6 * (SumToOfF n (fun x => x^2)) = n * (succ n) * (2 * n + 1) := by
  sorry

-- ∑_{k=1}^n k^3 = (n(n + 1)/2)^2 = (∑_{k=1}^n k)^2
theorem SumOfCubesTo (n : Nat) : 4 * (SumToOfF n (fun x => x^3)) = n^2 * (succ n)^2 := by
  sorry

-- HARD: Involves subtraction
-- ∑_{k=1}^n (2k - 1) = n^2
theorem oddSum (n : ℕ) : SumToOfF n (fun m => 2*m - 1) = n*n := by
  sorry


lemma sum_linear (n p : ℕ) (f : ℕ → ℕ) : SumToOfF n (fun m => p * f m) = p * SumToOfF n f := by
  sorry

lemma sumToOfId_eq_SumTo : SumToOfF n (fun m => m) = SumTo n := by
  sorry

-- ∑_{k=1}^n (2k) = n(n + 1)
example (n:ℕ) : SumToOfF n (fun m => 2*m) = n * (n+1) := by
  sorry




-- ∑_{k=1}^n k(k + 1) = n(n + 1)(n + 2)/3
example : 3 * SumToOfF n (fun m => m*(m+1)) = n * (n + 1) * (n + 2) := by
  sorry
