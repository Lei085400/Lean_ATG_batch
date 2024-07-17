import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Parity
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Order.WellFounded
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.NNReal
import Aesop
-- import Mathlib.Algebra.Group.Pi.Basic
-- set_option maxHeartbeats 0
set_option trace.aesop true
set_option trace.aesop.proof true
set_option maxHeartbeats 999999999999999999999999
open Nat Real Rat BigOperators


#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"



-- theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
--   have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
--    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
--   rw[choose_eq_choose_sub_add]
--   rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
--   have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
--   rw[choose_sub_eq_choose_sub_add, choose_succ_succ]

-- theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by lean_repl sorry
--  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
--   rw[add_comm]
--   simp [*, choose]
--   rw[Nat.sub_add_cancel h2]

-- theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
--   rw [choose_eq_factorial_div_factorial hk]
--   rw [choose_eq_factorial_div_factorial]
--   rw [Nat.sub_sub_self hk]
--   rw [mul_comm]
--   exact Nat.sub_le _ _

-- theorem choose_symm' {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by lean_repl sorry
--   rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
--     tsub_tsub_cancel_of_le hk, mul_comm]



-- theorem choose_eq_choose_sub_add(h1:1 ≤ n)(h2:1 ≤ k) :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by lean_repl sorry
--     rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]

-- theorem sum_neg_pow_mul_mul (t : ℕ → ℕ → ℕ → ℝ := fun m n k => (-1 : ℝ)^k * (choose n k : ℝ) * (m / (m+k))):
--     ∑ k in Ico 1 n, (-1 : ℝ)^k * ((choose (n-1) k + choose (n-1) (k-1)) : ℝ) * (m / (m+k)) = ∑ k in Ico 1 n, (((-1 : ℝ)^k * choose (n-1) k * (m / (m+k)) + (-1 : ℝ)^k * choose (n-1) (k-1) * (m / (m+k))) : ℝ):= by lean_repl sorry
--     -- congr 1
    -- ext1 k
    -- rw [mul_add]
    -- rw [add_mul]
  -- refine' sum_congr rfl fun y _ => _
  -- rw[mul_add]
  -- rw[add_mul]
--   -- apply sum_congr rfl
--   -- intro x hx
--   -- congr 2
--   -- rw [mul_add]
--   -- rw [add_mul]

-- theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by lean_repl sorry
--     rw[Nat.lt_iff_le_pred hn0]
--     intro a
--     exact a

-- theorem itd53 (hn :0 < n) :  ∑ k in range (n+1), (choose n k : ℝ) * (-1 : ℝ) ^ k / (k + 2) = 1 / ((n + 1) * (n + 2)) := by lean_repl sorry

--theorem itd53_ (hn :0 < n) :  ∑ k in range (n+1), (choose n k : ℝ) * (((-1 : ℝ) ^ (k+2)) / (k + 2)) = -(1 / (n + 2)) + 1 / (n+1) := by lean_repl sorry

-- theorem l₄ : 1/(k+1) - 1/(k+2) = 1/((k+1)*(k+2)) := by lean_repl sorry

-- theorem lt_eq_le_sub{y:ℕ}(hn0 : 0 < n) : y < n → y ≤ n - 1 := by lean_repl sorry

-- theorem Real_choose_eq_choose_add(h1:1 ≤ n)(h2:1 ≤ k) : (choose (n - 1 + 1) (k - 1 + 1) : ℝ) = (choose (n - 1 + 1 - 1) (k - 1 + 1) : ℝ)  + (choose (n - 1 + 1 - 1) (k - 1 + 1 - 1): ℝ) := by lean_repl sorry
--   -- rw[← Nat.sub_add_cancel h1, ← Nat.sub_add_cancel h2]
--   simp
--   rw[choose_succ_succ]
--   rw[add_comm]
--   simp

-- example (a b c : Nat) : a + b + c = a + c + b := by
--   rw [Nat.add_assoc]
--   rw [Nat.add_assoc]
--   rw [Nat.add_comm]
--   rw [Nat.add_assoc]
--   rw [Nat.add_comm b c]
--   rw [Nat.add_comm a (c+b)]


-- example(a b c:Nat):b + (c + a) = a + (c + b):=by
--   rw [← Nat.add_assoc]
--   rw [Nat.add_comm b c]
--   rw [Nat.add_comm a (c+b)]


theorem mathd_algebra_493
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 4 * Real.sqrt x + 1) :
  f (f 4) = 70 := by
  rw [h₀]
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← sub_eq_zero]
  rw [← sub_eq_zero]
  sorry

theorem mathd_algebra_493'
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 4 * Real.sqrt x + 1) :
  f 4 ^ 2 - 4 * Real.sqrt (f 4) + 1 - 70 - 0 - 0 - 0 = 0 := by
  rw [sub_eq_zero]
  rw [sub_eq_zero]
  rw [sub_eq_zero]
  rw [sub_eq_zero]
  rw[← h₀]
  rw[mathd_algebra_493 f h₀]
