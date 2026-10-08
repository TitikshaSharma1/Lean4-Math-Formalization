import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

-- Project 2: Recursive Functions and Proof by Induction
-- Demonstrates structural induction and automated algebraic tactics (ring).

-- Define a recursive function for the sum of first n numbers
def sum_first_n : ℕ → ℕ
| 0 => 0
| n + 1 => sum_first_n n + (n + 1)

-- Prove that 2 * sum_first_n(n) = n * (n + 1)
theorem sum_first_n_formula (n : ℕ) : 2 * sum_first_n n = n * (n + 1) := by
  induction n with
  | zero => 
      -- Base case: n = 0
      rfl
  | succ d hd =>
      -- Inductive step: n = d + 1
      calc
        2 * sum_first_n (d + 1) = 2 * (sum_first_n d + (d + 1)) := by rfl
        _ = 2 * sum_first_n d + 2 * (d + 1) := by rw [Nat.mul_add]
        _ = d * (d + 1) + 2 * (d + 1) := by rw [hd]
        _ = (d + 2) * (d + 1) := by ring
        _ = (d + 1) * (d + 1 + 1) := by ring
