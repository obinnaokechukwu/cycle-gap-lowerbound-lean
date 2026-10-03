import GraphicalAllocation.Smoothed.CycleUpper
import GraphicalAllocation.Smoothed.CycleLower

/-! # Corollary 8.3: the same smoothed rule nearly attains the cycle lower bound -/

noncomputable section
namespace GraphicalAllocation.Smoothed
open Process Rules Transport Applications MeasureTheory
open scoped NNReal ENNReal

/-- Both sides concern the same explicitly constructed rule, initial profile,
edge clocks, and probability law, for every cycle size at least three. -/
theorem cycle_smoothed_two_sided (n : ℕ) (time : ℝ≥0)
    (ht₀ : (n + 3 : ℝ) ^ 2 ≤ time) (ht₁ : (time : ℝ) ≤ (n + 3 : ℝ) ^ 4) :
    ENNReal.ofReal (cycleConstant * Real.sqrt (n + 3)) ≤
      (∫⁻ x, ENNReal.ofReal (gap x)
        ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ∧
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ≤
      ENNReal.ofReal (300 * Real.sqrt (n + 3) * Real.log (n + 3) + 2) :=
  ⟨(cycle_smoothed_lower_bound n time ht₀).1,
    cycle_smoothed_continuous_expectation_le n time ht₁⟩

/-- The displayed two-sided real expectation, with integrability already proved. -/
theorem cycle_smoothed_two_sided_integral (n : ℕ) (time : ℝ≥0)
    (ht₀ : (n + 3 : ℝ) ^ 2 ≤ time) (ht₁ : (time : ℝ) ≤ (n + 3 : ℝ) ^ 4) :
    cycleConstant * Real.sqrt (n + 3) ≤
      (∫ x, gap x ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ∧
    (∫ x, gap x ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ≤
      300 * Real.sqrt (n + 3) * Real.log (n + 3) + 2 := by
  refine ⟨?_, cycle_smoothed_continuous_integral_le n time ht₁⟩
  have h := (cycle_smoothed_lower_bound n time ht₀).1
  rw [← ofReal_integral_eq_lintegral_ofReal (cycle_smoothed_continuous_integrable n time ht₁)
    (ae_of_all _ gap_nonneg)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg gap_nonneg)).mp h

end GraphicalAllocation.Smoothed
