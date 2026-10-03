import GraphicalAllocation.Process.DiscreteVariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Uniform bounds for genuine Markov variances and response energies -/
namespace GraphicalAllocation.Process.FiniteKernel
open scoped BigOperators
variable {S C : Type*} [Fintype C]
variable (K : FiniteKernel S C)

/-- A bounded test has one-step squared response at most four. -/
theorem responseEnergy_le_four {f : S → ℝ} (hf : ∀ x, |f x| ≤ 1) (x : S) :
    K.responseEnergy f x ≤ 4 := by
  have hd : ∀ c, (f (K.next x c) - f x) ^ 2 ≤ 4 := by
    intro c
    have hn := abs_le.mp (hf (K.next x c))
    have hx := abs_le.mp (hf x)
    nlinarith [sq_nonneg (f (K.next x c) - f x)]
  unfold responseEnergy
  calc
    _ ≤ ∑ c, K.weight x c * 4 := Finset.sum_le_sum
      (fun c hc => mul_le_mul_of_nonneg_left (hd c) (K.nonneg x c))
    _ = 4 := by rw [← Finset.sum_mul, K.total, one_mul]

theorem abs_responseEnergy_le_four {f : S → ℝ} (hf : ∀ x, |f x| ≤ 1) (x : S) :
    |K.responseEnergy f x| ≤ 4 := by
  rw [abs_of_nonneg (K.responseEnergy_nonneg f x)]
  exact K.responseEnergy_le_four hf x

theorem abs_variance_le_one {f : S → ℝ} (hf : ∀ x, |f x| ≤ 1) (x : S) :
    |K.variance f x| ≤ 1 := by
  rw [abs_of_nonneg (K.variance_nonneg f x)]
  exact K.variance_le_one hf x

end GraphicalAllocation.Process.FiniteKernel
