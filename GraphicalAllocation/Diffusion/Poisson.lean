import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Exact Poissonization of affine event-count estimates

The first moment is proved from the Poisson series, so the conversion from h
updates to physical time is not an assumption about an abstract count law.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

lemma poisson_first_moment_series (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * n) (r : ℝ) := by
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have heq (n : ℕ) :
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) * (n + 1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hs : HasSum (fun n : ℕ =>
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) * (n + 1)) (r : ℝ) := by
    simpa only [heq, mul_one] using h
  apply (hasSum_nat_add_iff' 1).mp
  simpa using hs

/-- The event count has finite mean for every nonnegative time, including zero. -/
lemma poisson_natCast_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, Nat.abs_cast] using (poisson_first_moment_series r).summable

/-- The exact Poisson mean used to average event-time displacement bounds. -/
theorem poisson_natCast_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_first_moment_series r).tsum_eq

/-- An affine event bound averages to precisely the same affine function of
the Poisson mean. Nonnegative observables are automatically integrable. -/
theorem poisson_affine_bound (r : ℝ≥0) (f : ℕ → ℝ) (a b : ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hf : ∀ n, f n ≤ a * n + b) :
    Integrable f (poissonMeasure r) ∧ (∫ n, f n ∂poissonMeasure r) ≤ a * r + b := by
  have hg : Integrable (fun n : ℕ => a * n + b) (poissonMeasure r) :=
    ((poisson_natCast_integrable r).const_mul a).add (integrable_const b)
  have hi : Integrable f (poissonMeasure r) :=
    hg.mono_nonneg (measurable_of_countable f).aestronglyMeasurable
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf)
  refine ⟨hi, ?_⟩
  calc
    (∫ n, f n ∂poissonMeasure r) ≤ ∫ n : ℕ, a * n + b ∂poissonMeasure r :=
      integral_mono hi hg hf
    _ = a * r + b := by
      rw [integral_add ((poisson_natCast_integrable r).const_mul a) (integrable_const b),
        integral_const_mul, poisson_natCast_integral, integral_const]
      simp

/-- At physical time s with m independent rate-one edge clocks, an event bound
`a*h/m+b` becomes `a*s+b` without any approximation or de-Poissonization. -/
theorem poisson_event_to_physical (m : ℕ) (hm : 0 < m) (s : ℝ≥0)
    (f : ℕ → ℝ) (a b : ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n, f n ≤ a * n / m + b) :
    Integrable f (poissonMeasure ((m : ℝ≥0) * s)) ∧
      (∫ n, f n ∂poissonMeasure ((m : ℝ≥0) * s)) ≤ a * s + b := by
  have h := poisson_affine_bound ((m : ℝ≥0) * s) f (a / m) b hf0 (by
    intro n
    simpa only [div_mul_eq_mul_div] using hf n)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  convert h using 1
  push_cast
  field_simp

end GraphicalAllocation.Diffusion
