import GraphicalAllocation.Process.LawExpectation
import GraphicalAllocation.Process.Continuous.Semigroup

/-!
# Analytic semigroup equals the constructed process law

This bridge identifies the operator exponential with the genuine independent
Poisson event-count law. It also handles every initial distribution on the
countable state space.
-/

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators NNReal ENNReal BoundedContinuousFunction
open MeasureTheory

variable {State Choice : Type*} [Fintype Choice]
variable [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]
variable [TopologicalSpace State] [DiscreteTopology State]
variable (K : FiniteKernel State Choice)

theorem integral_continuousLaw_eq_semigroup (rate time : ℝ≥0) (x : State)
    (f : State →ᵇ ℝ) :
    ∫ y, f y ∂(K.continuousLaw rate time x).toMeasure = K.semigroup rate time f x := by
  rw [K.integral_continuousLaw rate time x f ‖f‖ (fun y => f.norm_coe_le_norm y)]
  have hi : Integrable (fun n => K.iterate n f x)
      (ProbabilityTheory.poissonMeasure (rate * time)) := by
    refine ⟨(measurable_of_countable _).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := ‖f‖) ?_⟩
    filter_upwards [] with n
    exact K.iterate_bounded n (fun y => f.norm_coe_le_norm y) x
  have hp := ProbabilityTheory.hasSum_integral_poissonMeasure hi
  have hs := K.semigroup_hasSum rate time f x
  have he : (fun n => ((Real.exp (-(rate * time : ℝ≥0)) *
      (rate * time : ℝ≥0) ^ n / (n.factorial : ℝ)) : ℝ) • K.iterate n f x) =
      (fun n => poissonWeight ((time : ℝ) * rate) n * K.iterate n f x) := by
    funext n
    simp only [NNReal.coe_mul, smul_eq_mul, poissonWeight, div_eq_mul_inv]
    rw [mul_comm (rate : ℝ) (time : ℝ)]
    ring
  rw [he] at hp
  exact hp.unique hs

/-- Poisson averaging of event-time expectations equals the analytic semigroup. -/
theorem integral_poisson_iterate_eq_semigroup (rate time : ℝ≥0) (x : State)
    (f : State →ᵇ ℝ) :
    (∫ n, K.iterate n f x ∂ProbabilityTheory.poissonMeasure (rate * time)) =
      K.semigroup rate time f x := by
  have h := K.integral_continuousLaw_eq_semigroup rate time x f
  rwa [K.integral_continuousLaw rate time x f ‖f‖ (fun y => f.norm_coe_le_norm y)] at h

/-- Arbitrary initial laws average the same semigroup. -/
theorem integral_continuousLawFrom_eq_semigroup (μ : PMF State) (rate time : ℝ≥0)
    (f : State →ᵇ ℝ) :
    ∫ y, f y ∂(K.continuousLawFrom μ rate time).toMeasure =
      ∫ x, K.semigroup rate time f x ∂μ.toMeasure := by
  unfold continuousLawFrom
  rw [integral_bind _ _ _
    (integrable_pmf_of_bounded _ f ‖f‖ (fun y => f.norm_coe_le_norm y))]
  rw [PMF.integral_eq_tsum μ _
    (integrable_pmf_of_bounded _ (K.semigroup rate time f) ‖f‖
      (fun x => K.semigroup_bounded rate.property time.property
        (fun y => f.norm_coe_le_norm y) x))]
  congr 1
  funext x
  rw [K.integral_continuousLaw_eq_semigroup]
  rfl

end GraphicalAllocation.Process.FiniteKernel
