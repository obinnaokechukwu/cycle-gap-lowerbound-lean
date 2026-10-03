import GraphicalAllocation.Probability.Bernstein

/-!
# Predictable stopping and finite vector observables

These corollaries let the scalar Bernstein theorem be applied directly to finite
vector-valued martingale increments and a predictable stopping indicator.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GraphicalAllocation.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Multiplication by predictable zero-one indicators preserves the Bernstein
bound and can only decrease the predictable quadratic variation. -/
theorem bounded_increment_bernstein_indicator
    {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ} {n : ℕ} {b σ s : ℝ}
    (hb : 0 ≤ b) (hσ : 0 < σ) (hs : 0 < s)
    (hmeas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hmean : ∀ i < n, μ[ξ i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n, μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω) ≤ σ)
    (A : ℕ → Set Ω) (hA : ∀ i < n, MeasurableSet[ℱ i] (A i)) :
    μ.real {ω | Real.sqrt (2 * σ * s) + (2 * b / 3) * s ≤
      |∑ i ∈ Finset.range n, (A i).indicator (ξ i) ω|} ≤ 2 * Real.exp (-s) := by
  have hstopmeas : ∀ i < n,
      StronglyMeasurable[ℱ (i + 1)] ((A i).indicator (ξ i)) := by
    intro i hi
    exact (hmeas i hi).indicator ((ℱ.mono (Nat.le_succ i)) _ (hA i hi))
  have hstopbound : ∀ i < n, ∀ᵐ ω ∂μ, |(A i).indicator (ξ i) ω| ≤ b := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    by_cases hωA : ω ∈ A i
    · simpa [Set.indicator_of_mem hωA] using hω
    · simp [Set.indicator_of_notMem hωA, hb]
  have hstopmean : ∀ i < n, μ[(A i).indicator (ξ i) | ℱ i] =ᵐ[μ] 0 := by
    intro i hi
    have hint := bernstein_integrable_of_abs_le
      ((hmeas i hi).mono (ℱ.le (i + 1))).aestronglyMeasurable (hbound i hi)
    filter_upwards [condExp_indicator hint (hA i hi), hmean i hi] with ω hce hmean
    rw [hce]
    by_cases hωA : ω ∈ A i
    · simpa [Set.indicator_of_mem hωA] using hmean
    · simp [Set.indicator_of_notMem hωA]
  have hvarstep : ∀ i < n, ∀ᵐ ω ∂μ,
      μ[fun ω ↦ ((A i).indicator (ξ i) ω) ^ 2 | ℱ i] ω ≤
        μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω := by
    intro i hi
    apply condExp_mono
      (bernstein_integrable_sq
        ((hstopmeas i hi).mono (ℱ.le (i + 1))).aestronglyMeasurable (hstopbound i hi))
      (bernstein_integrable_sq
        ((hmeas i hi).mono (ℱ.le (i + 1))).aestronglyMeasurable (hbound i hi))
    exact Eventually.of_forall (fun ω ↦ by
      by_cases hωA : ω ∈ A i
      · simp [Set.indicator_of_mem hωA]
      · simp [Set.indicator_of_notMem hωA, sq_nonneg])
  have hstopvar : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n,
        μ[fun ω ↦ ((A i).indicator (ξ i) ω) ^ 2 | ℱ i] ω) ≤ σ := by
    filter_upwards [ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hvarstep i)), hvar]
      with ω hsteps hvar
    exact (Finset.sum_le_sum (fun i hi ↦ hsteps i (Finset.mem_range.mp hi))).trans hvar
  exact bounded_increment_bernstein hb hσ hs hstopmeas hstopbound hstopmean hstopvar

omit [IsProbabilityMeasure μ] in
/-- Conditional means commute with deterministic finite linear observations. -/
lemma bernstein_condExp_observable_eq_zero {ι : Type*} [Fintype ι]
    {m : MeasurableSpace Ω} {D : Ω → ι → ℝ} (g : ι → ℝ)
    (hint : ∀ v, Integrable (fun ω ↦ D ω v) μ)
    (hmean : ∀ v, μ[fun ω ↦ D ω v | m] =ᵐ[μ] 0) :
    μ[fun ω ↦ ∑ v, g v * D ω v | m] =ᵐ[μ] 0 := by
  classical
  have hterms : ∀ v, μ[fun ω ↦ g v * D ω v | m] =ᵐ[μ] 0 := by
    intro v
    filter_upwards [condExp_smul (g v) (fun ω ↦ D ω v) m (μ := μ), hmean v]
      with ω hce hzero
    change μ[fun ω ↦ g v * D ω v | m] ω = g v * μ[fun ω ↦ D ω v | m] ω at hce
    rw [hce, hzero]
    simp
  have hsum := condExp_finsetSum (s := Finset.univ)
    (fun v _ ↦ (hint v).const_mul (g v)) m
  have heq : (fun ω ↦ ∑ v, g v * D ω v) = ∑ v, (fun ω ↦ g v * D ω v) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [heq]
  refine hsum.trans ?_
  filter_upwards [ae_all_iff.mpr hterms] with ω hω
  simp only [Finset.sum_apply, hω, Pi.zero_apply, Finset.sum_const_zero]

/-- Bernstein for finite deterministic vector observations of adapted integrable
martingale differences, with an optional predictable stopping indicator. The
observable size and variance are the actual quantities needed by an application. -/
theorem bounded_increment_bernstein_vector_indicator
    {ι : Type*} [Fintype ι] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ι → ℝ} (g : ℕ → ι → ℝ) {n : ℕ} {b σ s : ℝ}
    (hb : 0 ≤ b) (hσ : 0 < σ) (hs : 0 < s)
    (hmeas : ∀ i < n, ∀ v, StronglyMeasurable[ℱ (i + 1)] (fun ω ↦ D i ω v))
    (hint : ∀ i < n, ∀ v, Integrable (fun ω ↦ D i ω v) μ)
    (hmean : ∀ i < n, ∀ v, μ[fun ω ↦ D i ω v | ℱ i] =ᵐ[μ] 0)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |∑ v, g i v * D i ω v| ≤ b)
    (hvar : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n,
        μ[fun ω ↦ (∑ v, g i v * D i ω v) ^ 2 | ℱ i] ω) ≤ σ)
    (A : ℕ → Set Ω) (hA : ∀ i < n, MeasurableSet[ℱ i] (A i)) :
    μ.real {ω | Real.sqrt (2 * σ * s) + (2 * b / 3) * s ≤
      |∑ i ∈ Finset.range n, (A i).indicator (fun ω ↦ ∑ v, g i v * D i ω v) ω|}
      ≤ 2 * Real.exp (-s) := by
  apply bounded_increment_bernstein_indicator hb hσ hs (A := A) (hA := hA)
  · intro i hi
    exact Finset.stronglyMeasurable_fun_sum _ (fun v _ ↦ (hmeas i hi v).const_mul (g i v))
  · exact hbound
  · intro i hi
    exact bernstein_condExp_observable_eq_zero (g i) (hint i hi) (hmean i hi)
  · exact hvar

end GraphicalAllocation.Probability
