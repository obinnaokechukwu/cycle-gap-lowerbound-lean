import GraphicalAllocation.Process.FiniteIntegrability
import GraphicalAllocation.Probability.PoissonMoments

/-!
# Upper bounds under exact Poissonization

Nonnegative expectations are decomposed into genuine event-count laws. A
polynomial tail budget is paid with the proved Poisson second moment, without
assuming a global bound on the state observable.
-/

namespace GraphicalAllocation.Process.FiniteKernel
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open GraphicalAllocation.Probability

variable {State Choice : Type*} [Fintype Choice]
variable [MeasurableSpace State] [MeasurableSingletonClass State]
variable (K : FiniteKernel State Choice)

/-- The exact Poisson-mixture identity for extended nonnegative expectations. -/
theorem lintegral_continuousLaw_ofReal (rate time : ℝ≥0) (x : State) (f : State → ℝ)
    (hf : ∀ y, 0 ≤ f y) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂(K.continuousLaw rate time x).toMeasure) =
      ∫⁻ k : ℕ, ENNReal.ofReal (K.iterate k f x) ∂poissonMeasure (rate * time) := by
  unfold continuousLaw
  rw [toMeasure_bind_sum, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, K.lintegral_eventLaw_ofReal _ _ _ hf]
  rw [lintegral_countable']
  apply tsum_congr
  intro k
  rw [Measure.toPMF_apply]
  exact mul_comm _ _

/-- A deterministic event-horizon bound with a one-ball tail growth estimate
converts into an explicit physical-time upper bound. -/
theorem poisson_upper_of_event_bound (rate time : ℝ≥0) (x : State) (f : State → ℝ)
    (hf : ∀ y, 0 ≤ f y) {B H : ℝ} (hB : 0 ≤ B) (hH : 0 < H)
    (hsmall : ∀ k : ℕ, (k : ℝ) ≤ H → K.iterate k f x ≤ B)
    (hall : ∀ k : ℕ, K.iterate k f x ≤ k) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂(K.continuousLaw rate time x).toMeasure) ≤
      ENNReal.ofReal (B + (((rate * time : ℝ≥0) : ℝ) ^ 2 + (rate * time : ℝ≥0)) / H) := by
  let r := rate * time
  have hdiv : Integrable (fun k : ℕ => (k : ℝ)^2 / H) (poissonMeasure r) :=
    (poisson_sq_integrable r).div_const H
  have hi : Integrable (fun k : ℕ => B + (k : ℝ)^2 / H) (poissonMeasure r) :=
    (integrable_const B).add hdiv
  have hn : ∀ k : ℕ, 0 ≤ B + (k : ℝ)^2 / H := fun k => add_nonneg hB (by positivity)
  have hbound (k : ℕ) : K.iterate k f x ≤ B + (k : ℝ)^2 / H := by
    by_cases hk : (k : ℝ) ≤ H
    · exact (hsmall k hk).trans (le_add_of_nonneg_right (by positivity))
    · have hk₀ : (0 : ℝ) ≤ k := by positivity
      have ht : (k : ℝ) ≤ (k : ℝ)^2 / H := by
        apply (le_div_iff₀ hH).mpr
        nlinarith [mul_nonneg hk₀ (by linarith : 0 ≤ (k : ℝ) - H)]
      exact (hall k).trans (ht.trans (le_add_of_nonneg_left hB))
  rw [K.lintegral_continuousLaw_ofReal rate time x f hf]
  calc
    _ ≤ ∫⁻ k : ℕ, ENNReal.ofReal (B + (k : ℝ)^2 / H) ∂poissonMeasure r :=
      lintegral_mono fun k => ENNReal.ofReal_le_ofReal (hbound k)
    _ = ENNReal.ofReal (∫ k : ℕ, B + (k : ℝ)^2 / H ∂poissonMeasure r) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)).symm
    _ = _ := by
      rw [integral_add (integrable_const B) hdiv, integral_div, poisson_sq_integral, integral_const]
      simp [r]

end GraphicalAllocation.Process.FiniteKernel
