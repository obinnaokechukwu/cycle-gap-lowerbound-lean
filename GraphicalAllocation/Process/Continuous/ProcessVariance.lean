import GraphicalAllocation.Process.Continuous.InitialLaw
import GraphicalAllocation.Process.SemigroupLaw
import Mathlib.Probability.Moments.Variance

/-!
# Response energy for the constructed stochastic law

This module closes the law-level bridge for the finite-horizon variance budget.
Both terminal variance and intermediate-state expectations refer to the actual
independent-Poisson-mixture process law, rather than an assumed semigroup law.
-/

noncomputable section

namespace GraphicalAllocation.Process.FiniteKernel

open MeasureTheory
open scoped BigOperators NNReal BoundedContinuousFunction

variable {State Choice : Type*} [Fintype Choice]
variable [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]
variable [TopologicalSpace State] [DiscreteTopology State] [OpensMeasurableSpace State]
variable (K : FiniteKernel State Choice)

/-- The analytic second-moment expression is Mathlib's variance under the
explicitly constructed terminal probability law. -/
theorem continuousVariance_eq_variance (μ : PMF State) (rate t : ℝ≥0)
    (f : State →ᵇ ℝ) :
    K.continuousVariance μ.toMeasure rate t f =
      ProbabilityTheory.variance f (K.continuousLawFrom μ rate t).toMeasure := by
  have hf : MemLp f 2 (K.continuousLawFrom μ rate t).toMeasure :=
    MemLp.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  rw [ProbabilityTheory.variance_eq_sub hf]
  have h2 := K.integral_continuousLawFrom_eq_semigroup μ rate t (f ^ 2)
  have h1 := K.integral_continuousLawFrom_eq_semigroup μ rate t f
  simpa only [continuousVariance, boundedExpectation_apply,
    BoundedContinuousFunction.coe_pow] using congrArg₂ (fun a b : ℝ => a - b ^ 2) h2.symm h1.symm

/-- At an admissible lag, the analytic energy is exactly expectation under the
actual intermediate-state law. -/
theorem lagResponseEnergy_eq_integral (μ : PMF State) (rate t : ℝ≥0)
    (f : State →ᵇ ℝ) {s : ℝ} (hs : s ≤ t) :
    K.lagResponseEnergy μ.toMeasure rate t f s =
      ∫ x, K.energy rate (K.semigroup rate s f) x
        ∂(K.continuousLawFrom μ rate (Real.toNNReal ((t : ℝ) - s))).toMeasure := by
  rw [K.integral_continuousLawFrom_eq_semigroup]
  simp only [Real.coe_toNNReal _ (sub_nonneg.mpr hs), lagResponseEnergy,
    boundedExpectation_apply]

/-- The finite-horizon response-energy lemma, expressed with the actual process
laws and the standard probability-theory variance. -/
theorem finiteHorizon_response_energy (μ : PMF State) (rate t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (f : State →ᵇ ℝ) :
    (∫ s in (0 : ℝ)..T, ∫ x,
      (rate : ℝ) * ∑ c, K.weight x c *
        (K.semigroup rate s f (K.next x c) - K.semigroup rate s f x) ^ 2
      ∂(K.continuousLawFrom μ rate (Real.toNNReal ((t : ℝ) - s))).toMeasure) ≤
      ProbabilityTheory.variance f (K.continuousLawFrom μ rate t).toMeasure := by
  rw [← K.continuousVariance_eq_variance]
  have h := K.integral_lagResponseEnergy_le_variance_of_le μ.toMeasure rate.coe_nonneg hT hTt f
  apply le_trans _ h
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s ≤ (t : ℝ) := by
    have hs' : s ∈ Set.Icc 0 T := by simpa only [Set.uIcc_of_le hT] using hs
    exact hs'.2.trans hTt
  simpa only [K.energy_apply] using (K.lagResponseEnergy_eq_integral μ rate t f hst).symm

end GraphicalAllocation.Process.FiniteKernel
