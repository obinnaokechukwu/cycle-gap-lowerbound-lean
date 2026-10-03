import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The conditional-expectation part of bounded-increment Bernstein

The filtration lives on an arbitrary measurable probability space.  Increments at
index `i` are measurable at time `i + 1` and have conditional mean zero at time `i`.
All size and variance hypotheses are almost-everywhere statements.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GraphicalAllocation.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Bounded measurable real random variables are integrable on a finite measure. -/
lemma bernstein_integrable_of_abs_le [IsFiniteMeasure μ] {X : Ω → ℝ} {b : ℝ}
    (hX : AEStronglyMeasurable X μ) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable X μ := by
  exact (integrable_const b).mono' hX (by simpa only [Real.norm_eq_abs] using hb)

/-- A convenient integrability statement for a bounded squared increment. -/
lemma bernstein_integrable_sq [IsFiniteMeasure μ] {X : Ω → ℝ} {b : ℝ}
    (hX : AEStronglyMeasurable X μ) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω ↦ (X ω) ^ 2) μ := by
  apply bernstein_integrable_of_abs_le (hX.pow 2) (b := b ^ 2)
  filter_upwards [hb] with ω hω
  rw [abs_of_nonneg (sq_nonneg _)]
  change (X ω) ^ 2 ≤ b ^ 2
  nlinarith [abs_nonneg (X ω), sq_abs (X ω)]

/-- The sum of increments strictly before time `n`. -/
def bernsteinPartialSum (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, ξ i ω

/-- The predictable quadratic variation of the finite increment sequence. -/
noncomputable def bernsteinVarianceSum (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω

lemma bernsteinPartialSum_measurable {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ}
    {n : ℕ} (hξ : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i)) :
    StronglyMeasurable[ℱ n] (bernsteinPartialSum ξ n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact (hξ i (Finset.mem_range.mp hi)).mono (ℱ.mono (by simpa using hi))

lemma bernsteinVarianceSum_measurable (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
    (n : ℕ) : StronglyMeasurable[ℱ n] (bernsteinVarianceSum μ ℱ ξ n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_of_lt (Finset.mem_range.mp hi)))

lemma bernsteinPartialSum_le {ξ : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}
    (hξ : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b) :
    ∀ᵐ ω ∂μ, bernsteinPartialSum ξ n ω ≤ n * b := by
  induction n with
  | zero => simp [bernsteinPartialSum]
  | succ n ih =>
    filter_upwards [ih (fun i hi ↦ hξ i (Nat.lt_succ_of_lt hi)),
      hξ n (Nat.lt_succ_self n)] with ω hsum hlast
    dsimp [bernsteinPartialSum] at *
    rw [Finset.sum_range_succ]
    push_cast
    linarith [le_abs_self (ξ n ω)]

lemma bernsteinVarianceSum_nonneg (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
    (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ bernsteinVarianceSum μ ℱ ξ n ω := by
  have h : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω :=
    fun i ↦ condExp_nonneg (Eventually.of_forall (fun ω ↦ sq_nonneg (ξ i ω)))
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact Finset.sum_nonneg (fun i _ ↦ hω i)

/-- Integrability of the compensated exponential follows from bounded increments,
without any independent integrability hypothesis on the variance process. -/
lemma bernstein_integrable_compensated [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ} {b χ c : ℝ} {n : ℕ}
    (hχ : 0 ≤ χ) (hc : 0 ≤ c)
    (hξ : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hb : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b) :
    Integrable (fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ n ω -
      c * bernsteinVarianceSum μ ℱ ξ n ω)) μ := by
  apply (integrable_const (Real.exp (χ * (n * b)))).mono'
  · exact (Real.continuous_exp.comp_stronglyMeasurable
      (((bernsteinPartialSum_measurable hξ).const_mul χ).sub
        ((bernsteinVarianceSum_measurable ℱ ξ n).const_mul c))).mono (ℱ.le n)
        |>.aestronglyMeasurable
  · filter_upwards [bernsteinPartialSum_le hb, bernsteinVarianceSum_nonneg ℱ ξ n]
      with ω hsum hvar
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith

/-- The elementary quadratic exponential estimate passes through conditional
expectation, using the conditional mean-zero hypothesis. -/
lemma bernstein_condExp_exp_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {b χ c : ℝ}
    (hX : AEStronglyMeasurable[mΩ] X μ) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hmean : μ[X | m] =ᵐ[μ] 0) (hχ : 0 ≤ χ)
    (hquad : ∀ᵐ ω ∂μ, Real.exp (χ * X ω) ≤ 1 + χ * X ω + c * (X ω) ^ 2) :
    ∀ᵐ ω ∂μ, μ[fun ω ↦ Real.exp (χ * X ω) | m] ω ≤
      Real.exp (c * μ[fun ω ↦ (X ω) ^ 2 | m] ω) := by
  have hXint := bernstein_integrable_of_abs_le hX hb
  have hsqint := bernstein_integrable_sq hX hb
  have hexpint : Integrable (fun ω ↦ Real.exp (χ * X ω)) μ :=
    integrable_exp_mul_of_le χ b hχ hX.aemeasurable
      (hb.mono fun ω hω ↦ (le_abs_self _).trans hω)
  have hlinint := (integrable_const (1 : ℝ)).add (hXint.const_mul χ)
  have hpolyint := hlinint.add (hsqint.const_mul c)
  have hmono := condExp_mono (m := m) hexpint hpolyint hquad
  have hlin := condExp_add (integrable_const (1 : ℝ)) (hXint.const_mul χ) m
  have hpoly := condExp_add hlinint (hsqint.const_mul c) m
  have hχX := condExp_smul χ X m (μ := μ)
  have hcX := condExp_smul c (fun ω ↦ (X ω) ^ 2) m (μ := μ)
  filter_upwards [hmono, hlin, hpoly, hχX, hcX, hmean]
    with ω hmono hlin hpoly hχX hcX hmean
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul] at hlin hpoly hχX hcX
  rw [condExp_const hm] at hlin
  calc
    μ[fun ω ↦ Real.exp (χ * X ω) | m] ω
        ≤ μ[fun ω ↦ 1 + χ * X ω + c * (X ω) ^ 2 | m] ω := hmono
    _ = 1 + c * μ[fun ω ↦ (X ω) ^ 2 | m] ω := by
      rw [hpoly, hlin, hχX, hcX, hmean]
      simp
    _ ≤ Real.exp (c * μ[fun ω ↦ (X ω) ^ 2 | m] ω) := by
      simpa only [add_comm] using Real.add_one_le_exp (c * μ[fun ω ↦ (X ω) ^ 2 | m] ω)

/-- Iteration of the conditional exponential estimate. This is the compensated
exponential supermartingale argument, expressed as an expectation inequality. -/
lemma bernstein_integral_compensated_le_one [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → ℝ} {b χ c : ℝ} {n : ℕ}
    (hχ : 0 ≤ χ) (hc : 0 ≤ c)
    (hξ : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hb : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b)
    (hcond : ∀ i < n, ∀ᵐ ω ∂μ,
      μ[fun ω ↦ Real.exp (χ * ξ i ω) | ℱ i] ω ≤
        Real.exp (c * μ[fun ω ↦ (ξ i ω) ^ 2 | ℱ i] ω)) :
    (∫ ω, Real.exp (χ * bernsteinPartialSum ξ n ω -
      c * bernsteinVarianceSum μ ℱ ξ n ω) ∂μ) ≤ 1 := by
  induction n with
  | zero => simp [bernsteinPartialSum, bernsteinVarianceSum]
  | succ n ih =>
    have hξn : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (ξ i) :=
      fun i hi ↦ hξ i (Nat.lt_succ_of_lt hi)
    have hbn : ∀ i < n, ∀ᵐ ω ∂μ, |ξ i ω| ≤ b :=
      fun i hi ↦ hb i (Nat.lt_succ_of_lt hi)
    have hprev := bernstein_integrable_compensated hχ hc hξn hbn
    have hnext := bernstein_integrable_compensated hχ hc hξ hb
    let A : Ω → ℝ := fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ n ω -
      c * (bernsteinVarianceSum μ ℱ ξ n ω + μ[fun ω ↦ (ξ n ω) ^ 2 | ℱ n] ω))
    have hA : StronglyMeasurable[ℱ n] A := by
      exact Real.continuous_exp.comp_stronglyMeasurable
        (((bernsteinPartialSum_measurable hξn).const_mul χ).sub
          (((bernsteinVarianceSum_measurable ℱ ξ n).add
            stronglyMeasurable_condExp).const_mul c))
    have hfactor : (fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ (n + 1) ω -
        c * bernsteinVarianceSum μ ℱ ξ (n + 1) ω)) =
        A * (fun ω ↦ Real.exp (χ * ξ n ω)) := by
      funext ω
      simp only [bernsteinPartialSum, bernsteinVarianceSum, Finset.sum_range_succ,
        Pi.mul_apply, A, ← Real.exp_add]
      congr 1
      ring
    have hexpint : Integrable (fun ω ↦ Real.exp (χ * ξ n ω)) μ :=
      integrable_exp_mul_of_le χ b hχ
        ((hξ n (Nat.lt_succ_self n)).mono (ℱ.le (n + 1))).measurable.aemeasurable
        ((hb n (Nat.lt_succ_self n)).mono fun ω hω ↦ (le_abs_self _).trans hω)
    have hpull := condExp_mul_of_stronglyMeasurable_left hA
      (hfactor ▸ hnext) hexpint
    have hce : μ[fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ (n + 1) ω -
        c * bernsteinVarianceSum μ ℱ ξ (n + 1) ω) | ℱ n] ≤ᵐ[μ]
        (fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ n ω -
          c * bernsteinVarianceSum μ ℱ ξ n ω)) := by
      rw [hfactor]
      filter_upwards [hpull, hcond n (Nat.lt_succ_self n)] with ω hpull hcond
      change _ = A ω * _ at hpull
      rw [hpull]
      calc
        A ω * μ[fun ω ↦ Real.exp (χ * ξ n ω) | ℱ n] ω
            ≤ A ω * Real.exp (c * μ[fun ω ↦ (ξ n ω) ^ 2 | ℱ n] ω) :=
          mul_le_mul_of_nonneg_left hcond (Real.exp_nonneg _)
        _ = Real.exp (χ * bernsteinPartialSum ξ n ω -
            c * bernsteinVarianceSum μ ℱ ξ n ω) := by
          dsimp [A]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      (∫ ω, Real.exp (χ * bernsteinPartialSum ξ (n + 1) ω -
          c * bernsteinVarianceSum μ ℱ ξ (n + 1) ω) ∂μ)
          = ∫ ω, μ[fun ω ↦ Real.exp (χ * bernsteinPartialSum ξ (n + 1) ω -
            c * bernsteinVarianceSum μ ℱ ξ (n + 1) ω) | ℱ n] ω ∂μ :=
        (integral_condExp (ℱ.le n)).symm
      _ ≤ ∫ ω, Real.exp (χ * bernsteinPartialSum ξ n ω -
          c * bernsteinVarianceSum μ ℱ ξ n ω) ∂μ :=
        integral_mono_ae integrable_condExp hprev hce
      _ ≤ 1 := ih hξn hbn (fun i hi ↦ hcond i (Nat.lt_succ_of_lt hi))

end GraphicalAllocation.Probability
