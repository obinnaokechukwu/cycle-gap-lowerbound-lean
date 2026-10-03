import GraphicalAllocation.Transport.MarkedTransport
import GraphicalAllocation.Process.DiscreteVariance

/-! # Jensen's inequality for the genuine finite-horizon expectation -/

namespace GraphicalAllocation.Process.FiniteKernel
open scoped BigOperators
variable {S C : Type*} [Fintype C]
variable (K : FiniteKernel S C)

/-- Positive-part square is convex under the actual Markov expectation. -/
theorem positivePart_sq_iterate_le (n : ℕ) (f : S → ℝ) (x : S) :
    max (K.iterate n f x) 0 ^ 2 ≤ K.iterate n (fun y => max (f y) 0 ^ 2) x := by
  have hu : 0 ≤ K.iterate n (fun y => max (f y) 0) x :=
    K.iterate_nonneg n (fun y => le_max_right _ _) x
  have hfu : K.iterate n f x ≤ K.iterate n (fun y => max (f y) 0) x :=
    K.iterate_mono n (fun y => le_max_left _ _) x
  have hmax : max (K.iterate n f x) 0 ≤ K.iterate n (fun y => max (f y) 0) x :=
    max_le hfu hu
  have hv := K.terminalVariance_nonneg n (fun y => max (f y) 0) x
  unfold terminalVariance at hv
  nlinarith [le_max_right (K.iterate n f x) 0]

/-- A pointwise inverse-volume energy bound survives arbitrary finite-horizon
Markov averaging, using the averaged response rather than averaged tails. -/
theorem iterate_energy_lower (n : ℕ) (f e : S → ℝ) {B : ℝ} (hB : 0 < B)
    (he : ∀ y, max (f y) 0 ^ 2 / B ≤ e y) (x : S) :
    max (K.iterate n f x) 0 ^ 2 / B ≤ K.iterate n e x := by
  have hmono := K.iterate_mono n he x
  have heq : K.iterate n (fun y => max (f y) 0 ^ 2 / B) x =
      K.iterate n (fun y => max (f y) 0 ^ 2) x / B := by
    simpa [div_eq_mul_inv, mul_comm] using
      congrFun (K.iterate_const_mul n B⁻¹ (fun y => max (f y) 0 ^ 2)) x
  rw [heq] at hmono
  exact (div_le_div_of_nonneg_right (K.positivePart_sq_iterate_le n f x) hB.le).trans hmono

end GraphicalAllocation.Process.FiniteKernel
