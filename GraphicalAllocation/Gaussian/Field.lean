import GraphicalAllocation.Spectral.GreenMatrix
import GraphicalAllocation.Spectral.Radius
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # The normalized finite-graph Gaussian free field

The sample space is the Euclidean space of vertex-indexed real vectors, and the
law is Mathlib's (possibly degenerate) multivariate Gaussian with covariance
`d • greenMatrix G hG`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace GraphicalAllocation.Gaussian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- The centered Gaussian free-field law with covariance `d L⁺`. -/
def freeField (d : ℝ) : Measure (EuclideanSpace ℝ V) :=
  multivariateGaussian 0 (d • Spectral.greenMatrix G hG)

instance freeField_isGaussian (d : ℝ) : IsGaussian (freeField G hG d) := by
  unfold freeField
  infer_instance

instance freeField_isProbabilityMeasure (d : ℝ) : IsProbabilityMeasure (freeField G hG d) :=
  inferInstance

theorem covariance_matrix_posSemidef {d : ℝ} (hd : 0 ≤ d) :
    (d • Spectral.greenMatrix G hG).PosSemidef :=
  (Spectral.greenMatrix_posSemidef G hG).smul hd

theorem freeField_covariance {d : ℝ} (hd : 0 ≤ d) (u v : V) :
    cov[fun x ↦ x u, fun x ↦ x v; freeField G hG d] =
      d * Spectral.greenMatrix G hG u v := by
  exact covariance_eval_multivariateGaussian (covariance_matrix_posSemidef G hG hd) u v

theorem freeField_variance {d : ℝ} (hd : 0 ≤ d) (v : V) :
    Var[fun x ↦ x v; freeField G hG d] =
      d * Spectral.greenDiagonal G hG v := by
  exact variance_eval_multivariateGaussian (covariance_matrix_posSemidef G hG hd) v

theorem freeField_coordinate_law {d : ℝ} (hd : 0 ≤ d) (v : V) :
    MeasurePreserving (fun x : EuclideanSpace ℝ V ↦ x v) (freeField G hG d)
      (gaussianReal 0 (d * Spectral.greenDiagonal G hG v).toNNReal) := by
  exact measurePreserving_eval_multivariateGaussian
    (covariance_matrix_posSemidef G hG hd)

theorem freeField_memLp_coord (d : ℝ) (v : V) :
    MemLp (fun x : EuclideanSpace ℝ V ↦ x v) 2 (freeField G hG d) :=
  IsGaussian.memLp_two_id.eval_piLp v

theorem freeField_integrable_coord (d : ℝ) (v : V) :
    Integrable (fun x : EuclideanSpace ℝ V ↦ x v) (freeField G hG d) :=
  IsGaussian.integrable_id.eval_piLp v

/-- The multivariate Gaussian is centered as a vector-valued expectation. -/
theorem freeField_meanVector (d : ℝ) :
    ∫ x : EuclideanSpace ℝ V, x ∂freeField G hG d = 0 := by
  exact integral_id_multivariateGaussian

theorem freeField_mean (d : ℝ) (v : V) :
    ∫ x : EuclideanSpace ℝ V, x v ∂freeField G hG d = 0 := by
  rw [← eval_integral_piLp (freeField_integrable_coord G hG d)]
  simp [freeField]

theorem freeField_sum_variance {d : ℝ} (hd : 0 ≤ d) :
    Var[fun x : EuclideanSpace ℝ V ↦ ∑ v, x v; freeField G hG d] = 0 := by
  rw [← covariance_self (by fun_prop)]
  rw [covariance_fun_sum_fun_sum (fun v ↦ freeField_memLp_coord G hG d v)
    (fun v ↦ freeField_memLp_coord G hG d v)]
  simp_rw [freeField_covariance G hG hd]
  simp only [← Finset.mul_sum, Spectral.greenMatrix_row_sum, mul_zero, Finset.sum_const_zero]

/-- The constant direction is zero almost surely, including degenerate cases. -/
theorem freeField_sum_zero {d : ℝ} (hd : 0 ≤ d) :
    ∀ᵐ x : EuclideanSpace ℝ V ∂freeField G hG d, ∑ v, x v = 0 := by
  have hm : MemLp (fun x : EuclideanSpace ℝ V ↦ ∑ v, x v) 2 (freeField G hG d) :=
    memLp_finsetSum _ (fun v _ ↦ freeField_memLp_coord G hG d v)
  have hmean : ∫ x : EuclideanSpace ℝ V, (∑ v, x v) ∂freeField G hG d = 0 := by
    rw [integral_finsetSum _ (fun v _ ↦ freeField_integrable_coord G hG d v)]
    simp [freeField_mean]
  simpa only [hmean] using
    ae_eq_integral_of_variance_eq_zero hm (freeField_sum_variance G hG hd)

end GraphicalAllocation.Gaussian
