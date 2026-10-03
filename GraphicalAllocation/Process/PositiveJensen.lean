import GraphicalAllocation.Process.Continuous.InitialLaw

/-! # Positive-part Jensen inequality for bounded observables -/

namespace GraphicalAllocation.Process
open MeasureTheory
open scoped BoundedContinuousFunction

variable {State : Type*} [TopologicalSpace State] [DiscreteTopology State]
  [MeasurableSpace State] [OpensMeasurableSpace State]

noncomputable def positiveTest (f : State →ᵇ ℝ) : State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun x => max (f x) 0) ‖f‖ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self (f x)).trans (f.norm_coe_le_norm x)) (norm_nonneg _))

omit [MeasurableSpace State] [OpensMeasurableSpace State] in
@[simp] theorem positiveTest_apply (f : State →ᵇ ℝ) (x : State) : positiveTest f x = max (f x) 0 := rfl

/-- The expected squared positive part dominates the squared positive part of
expectation. Only boundedness of the test is used. -/
theorem boundedExpectation_pospart_sq (μ : Measure State) [IsProbabilityMeasure μ]
    (f : State →ᵇ ℝ) :
    max (boundedExpectation μ f) 0 ^ 2 ≤ boundedExpectation μ (positiveTest f ^ 2) := by
  have hs := boundedExpectation_sq μ (positiveTest f)
  have hn : 0 ≤ boundedExpectation μ (positiveTest f) :=
    boundedExpectation_nonneg μ (fun x => le_max_right (f x) 0)
  have hm : boundedExpectation μ f ≤ boundedExpectation μ (positiveTest f) :=
    boundedExpectation_mono μ (fun x => le_max_left (f x) 0)
  by_cases hf : boundedExpectation μ f ≤ 0
  · rw [max_eq_right hf, zero_pow (by decide : 2 ≠ 0)]
    exact boundedExpectation_nonneg μ (fun x => sq_nonneg _)
  · rw [max_eq_left (le_of_not_ge hf)]
    nlinarith

theorem integral_pospart_sq (μ : Measure State) [IsProbabilityMeasure μ]
    (f : State → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    max (∫ x, f x ∂μ) 0 ^ 2 ≤ ∫ x, max (f x) 0 ^ 2 ∂μ := by
  let f' : State →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf
  exact boundedExpectation_pospart_sq μ f'

end GraphicalAllocation.Process
