import GraphicalAllocation.Probability.BernsteinConditional
import GraphicalAllocation.Probability.BernsteinScalar

/-!
# Bounded-increment Bernstein inequality

This proves Lemma `lem:bernstein` in the revised paper, on an arbitrary probability
space. Neither a moment-generating-function inequality nor a tail inequality is
assumed: the scalar Taylor estimate is passed through conditional expectation and
iterated using the compensated exponential process.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GraphicalAllocation.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Bernstein control of the moment-generating function from bounded martingale
increments and a deterministic bound on the sum of conditional variances. -/
theorem bernstein_mgf_le {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ}
    {n : ℕ} {b σ χ : ℝ} (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hχb : χ * b < 3)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hmean : ∀ i < n, μ[ξ i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ, bernsteinVarianceSum μ ℱ ξ n ω ≤ σ) :
    mgf (bernsteinPartialSum ξ n) μ χ ≤
      Real.exp ((χ ^ 2 / (2 * (1 - χ * b / 3))) * σ) := by
  let c := χ ^ 2 / (2 * (1 - χ * b / 3))
  have hden : 0 < 2 * (1 - χ * b / 3) := by linarith
  have hc : 0 ≤ c := div_nonneg (sq_nonneg χ) hden.le
  have hcond : ∀ i < n, ∀ᵐ ω ∂μ,
      μ[fun ω ↦ Real.exp (χ * ξ i ω) | ℱ i] ω ≤
        Real.exp (c * μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω) := by
    intro i hi
    apply bernstein_condExp_exp_le (ℱ.le i)
      ((hmeas i hi).mono (ℱ.le (i + 1))).aestronglyMeasurable
      (hbound i hi) (hmean i hi) hχ
    exact (hbound i hi).mono (fun ω hω ↦ exp_mul_le_bernstein hb hχ hχb hω)
  have hcomp := bernstein_integral_compensated_le_one hχ hc hmeas hbound hcond
  have hcompint := bernstein_integrable_compensated hχ hc hmeas hbound
  have hsumint : Integrable (fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ n ω)) μ :=
    integrable_exp_mul_of_le χ (n * b) hχ
      ((bernsteinPartialSum_measurable hmeas).mono (ℱ.le n)).measurable.aemeasurable
      (bernsteinPartialSum_le hbound)
  calc
    mgf (bernsteinPartialSum ξ n) μ χ
        = ∫ ω, Real.exp (χ * bernsteinPartialSum ξ n ω) ∂μ := rfl
    _ ≤ ∫ ω, Real.exp (c * σ) * Real.exp (χ * bernsteinPartialSum ξ n ω -
        c * bernsteinVarianceSum μ ℱ ξ n ω) ∂μ := by
      apply integral_mono_ae hsumint (hcompint.const_mul _)
      filter_upwards [hvar] with ω hω
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (c * σ) * ∫ ω, Real.exp (χ * bernsteinPartialSum ξ n ω -
        c * bernsteinVarianceSum μ ℱ ξ n ω) ∂μ := integral_const_mul _ _
    _ ≤ Real.exp (c * σ) := by nlinarith [Real.exp_pos (c * σ)]

/-- One-sided bounded-increment Bernstein bound at a positive threshold. -/
theorem bernstein_measure_ge {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ}
    {n : ℕ} {b σ a : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ) (ha : 0 < a)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hmean : ∀ i < n, μ[ξ i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ, bernsteinVarianceSum μ ℱ ξ n ω ≤ σ) :
    μ.real {ω | a ≤ bernsteinPartialSum ξ n ω} ≤
      Real.exp (-(a ^ 2 / (2 * (σ + b * a / 3)))) := by
  let χ := a / (σ + b * a / 3)
  have hχ : 0 ≤ χ := (bernstein_parameter_pos ha hb hσ).le
  have hχb : χ * b < 3 := bernstein_parameter_mul_lt_three ha.le hb hσ
  have hmgf := bernstein_mgf_le hb hχ hχb hmeas hbound hmean hvar
  have hsumint : Integrable (fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ n ω)) μ :=
    integrable_exp_mul_of_le χ (n * b) hχ
      ((bernsteinPartialSum_measurable hmeas).mono (ℱ.le n)).measurable.aemeasurable
      (bernsteinPartialSum_le hbound)
  calc
    μ.real {ω | a ≤ bernsteinPartialSum ξ n ω}
        ≤ Real.exp (-χ * a) * mgf (bernsteinPartialSum ξ n) μ χ :=
      measure_ge_le_exp_mul_mgf a hχ hsumint
    _ ≤ Real.exp (-χ * a) * Real.exp ((χ ^ 2 / (2 * (1 - χ * b / 3))) * σ) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-(a ^ 2 / (2 * (σ + b * a / 3)))) := by
      rw [← Real.exp_add]
      congr 1
      exact bernstein_exponent_eq ha.le hb hσ

/-- Two-sided bounded-increment Bernstein bound at a positive threshold. -/
theorem bernstein_measure_abs_ge {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ}
    {n : ℕ} {b σ a : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ) (ha : 0 < a)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hmean : ∀ i < n, μ[ξ i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ, bernsteinVarianceSum μ ℱ ξ n ω ≤ σ) :
    μ.real {ω | a ≤ |bernsteinPartialSum ξ n ω|} ≤
      2 * Real.exp (-(a ^ 2 / (2 * (σ + b * a / 3)))) := by
  have hupper := bernstein_measure_ge hb hσ ha hmeas hbound hmean hvar
  have hnegmean : ∀ i < n, μ[(fun ω ↦ -ξ i ω) | ℱ i] =ᵐ[μ] 0 := by
    intro i hi
    exact (condExp_neg (ξ i) (ℱ i)).trans (by simpa using (hmean i hi).neg)
  have hnegvar : ∀ᵐ ω ∂μ,
      bernsteinVarianceSum μ ℱ (fun i ω ↦ -ξ i ω) n ω ≤ σ := by
    simpa only [bernsteinVarianceSum, neg_sq] using hvar
  have hlower := bernstein_measure_ge hb hσ ha (fun i hi ↦ (hmeas i hi).neg)
    (fun i hi ↦ by simpa only [Pi.neg_apply, abs_neg] using hbound i hi) hnegmean hnegvar
  have hevent : {ω | a ≤ |bernsteinPartialSum ξ n ω|} =
      {ω | a ≤ bernsteinPartialSum ξ n ω} ∪
        {ω | a ≤ bernsteinPartialSum (fun i ω ↦ -ξ i ω) n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, bernsteinPartialSum, Finset.sum_neg_distrib]
    rw [le_abs]
  change μ.real {ω | a ≤ bernsteinPartialSum (fun i ω ↦ -ξ i ω) n ω} ≤ _ at hlower
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

/-- Lemma 8.1: the literal bounded-increment Bernstein inequality, with almost-sure
increment and predictable-variance bounds and no restriction on the probability space. -/
theorem bounded_increment_bernstein {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ}
    {n : ℕ} {b σ s : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ) (hs : 0 < s)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hmean : ∀ i < n, μ[ξ i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n, μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω) ≤ σ) :
    μ.real {ω | Real.sqrt (2 * σ * s) + (2 * b / 3) * s ≤
      |∑ i ∈ Finset.range n, ξ i ω|} ≤ 2 * Real.exp (-s) := by
  have htail := bernstein_measure_abs_ge hb hσ (bernstein_threshold_pos hb hσ hs)
    hmeas hbound hmean hvar
  have hexponent := bernstein_threshold_exponent hb hσ hs
  dsimp only at hexponent
  rw [bernstein_exponent_eq (bernstein_threshold_pos hb hσ hs).le hb hσ] at hexponent
  exact htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num))

end GraphicalAllocation.Probability
