import GraphicalAllocation.Diffusion.Poisson
import Mathlib.Probability.Moments.Variance

/-! # Poisson second moments and explicit lower-count probability -/

noncomputable section
namespace GraphicalAllocation.Probability
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open GraphicalAllocation.Diffusion

lemma poisson_factorial_second_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
      (n.factorial : ℝ) * ((n : ℝ) * (n - 1))) ((r : ℝ) ^ 2) := by
  have h := (poisson_first_moment_series r).mul_left (r : ℝ)
  have heq (n : ℕ) :
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) *
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) =
        (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * n) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  apply (hasSum_nat_add_iff' 1).mp
  convert h using 1
  · funext n
    simpa using heq n
  · simp [pow_two]

lemma poisson_second_moment_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
      (n.factorial : ℝ) * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + r) := by
  convert (poisson_factorial_second_series r).add (poisson_first_moment_series r) using 1
  funext n
  ring

lemma poisson_sq_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, abs_pow, Nat.abs_cast] using
    (poisson_second_moment_series r).summable

lemma poisson_sq_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_second_moment_series r).tsum_eq

lemma poisson_centered_sq_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ) - r) ^ 2) (poissonMeasure r) := by
  have h := ((poisson_sq_integrable r).sub
    ((poisson_natCast_integrable r).const_mul (2 * r))).add (integrable_const ((r : ℝ) ^ 2))
  convert h using 1
  funext n
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma poisson_centered_sq_integral (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r) ^ 2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ) - r) ^ 2) =
      fun n : ℕ => (n : ℝ) ^ 2 - (2 * r) * (n : ℝ) + (r : ℝ) ^ 2 := by funext n; ring
  have hm : Integrable (fun n : ℕ => (2 * (r : ℝ)) * (n : ℝ)) (poissonMeasure r) :=
    (poisson_natCast_integrable r).const_mul _
  have hs : Integrable (fun n : ℕ => (n : ℝ) ^ 2 - (2 * r) * (n : ℝ))
      (poissonMeasure r) := (poisson_sq_integrable r).sub hm
  rw [heq, integral_add hs (integrable_const _),
    integral_sub (poisson_sq_integrable r) hm,
    integral_const_mul, poisson_sq_integral, poisson_natCast_integral, integral_const]
  simp
  ring

/-- At least half the mean arrivals occur with probability at least 7/8 when the mean is 32. -/
theorem poisson_half_mean_probability {r : ℝ≥0} (hr : 32 ≤ (r : ℝ)) :
    (7 / 8 : ℝ) ≤ (poissonMeasure r).real {n : ℕ | (r : ℝ) / 2 ≤ n} := by
  have hr₀ : 0 < (r : ℝ) := by linarith
  have hc : 0 < (r : ℝ) ^ 2 / 4 := by positivity
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := poissonMeasure r) (ae_of_all _ (fun n : ℕ => sq_nonneg ((n : ℝ) - r)))
    (poisson_centered_sq_integrable r) ((r : ℝ) ^ 2 / 4)
  rw [poisson_centered_sq_integral] at hm
  have hsub : {n : ℕ | (n : ℝ) < (r : ℝ) / 2} ⊆
      {n : ℕ | (r : ℝ) ^ 2 / 4 ≤ ((n : ℝ) - r) ^ 2} := by
    intro n hn
    change (r : ℝ) ^ 2 / 4 ≤ ((n : ℝ) - r) ^ 2
    have hn₀ : (0 : ℝ) ≤ n := by positivity
    change (n : ℝ) < (r : ℝ) / 2 at hn
    nlinarith [sq_nonneg ((r : ℝ) / 2 - n)]
  have hb : (poissonMeasure r).real {n : ℕ | (n : ℝ) < (r : ℝ) / 2} ≤ 1 / 8 := by
    have hp := measureReal_mono (μ := poissonMeasure r) hsub
    have hbound := le_trans (mul_le_mul_of_nonneg_left hp hc.le) hm
    have hd : (poissonMeasure r).real {n : ℕ | (n : ℝ) < (r : ℝ) / 2} ≤
        (r : ℝ) / ((r : ℝ)^2 / 4) := (le_div_iff₀ hc).mpr (by
      rw [mul_comm]
      exact hbound)
    exact hd.trans ((div_le_iff₀ hc).mpr (by nlinarith [sq_nonneg ((r : ℝ) - 32)]))
  have heq : {n : ℕ | (r : ℝ) / 2 ≤ n} =
      {n : ℕ | (n : ℝ) < (r : ℝ) / 2}ᶜ := by ext n; simp
  rw [heq, probReal_compl_eq_one_sub ((Set.to_countable _).measurableSet)]
  linarith

end GraphicalAllocation.Probability
