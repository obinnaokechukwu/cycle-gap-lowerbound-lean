import GraphicalAllocation.Smoothed.CycleRule
import GraphicalAllocation.Applications.CycleContinuous

/-!
# The lower bound for the same smoothed cycle process

The six stages specialize the quantified lower theorem, fix the literal cyclic
edge type, identify its actual `cycleRule`, apply the saturated cycle theorem,
rewrite the deterministic initial law, and discharge the orientation by `rfl`.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed
open Process Rules Geometry Transport Applications MeasureTheory
open scoped NNReal ENNReal

lemma cycle_flat_gap_zero (n : ℕ) : gap (0 : Profile (Fin (n + 3))) = 0 :=
  (gap_eq_zero_iff _).mpr (fun _ _ => rfl)

/-- Zero physical time has zero events, also at the smallest cycle size. -/
lemma cycle_smoothed_law_zero (n : ℕ) :
    (cycleRule n).kernel.continuousLaw (n + 3) 0 0 = PMF.pure 0 := by
  have hp : (ProbabilityTheory.poissonMeasure 0).toPMF = PMF.pure 0 := by
    ext k
    cases k <;>
      simp [Measure.toPMF_apply, ProbabilityTheory.poissonMeasure_singleton,
        PMF.pure_apply]
  simp only [FiniteKernel.continuousLaw, mul_zero, hp, PMF.pure_bind,
    FiniteKernel.eventLaw_zero]

lemma cycle_smoothed_expectation_zero (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((cycleRule n).kernel.continuousLaw (n + 3) 0 0).toMeasure) = 0 := by
  rw [cycle_smoothed_law_zero, PMF.toMeasure_pure]
  simp [cycle_flat_gap_zero]

/-- The lower bound is for the very rule whose kernel is identified above. -/
theorem cycle_smoothed_lower_bound (n : ℕ) (time : ℝ≥0)
    (ht : (n + 3 : ℝ) ^ 2 ≤ time) :
    ENNReal.ofReal (cycleConstant * Real.sqrt (n + 3)) ≤
      ∫⁻ x, ENNReal.ofReal (gap x)
        ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ ((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure
        {x | cycleConstant * Real.sqrt (n + 3) ≤ gap x} := by
  simpa only [FiniteKernel.continuousLawFrom, PMF.pure_bind] using
    cycle_lower_bound_saturated n (cycleRule n) rfl (PMF.pure 0) time ht

end GraphicalAllocation.Smoothed
