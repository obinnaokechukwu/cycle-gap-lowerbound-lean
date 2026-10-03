import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Scalar Bernstein estimates

The exponential bound follows by bounding the Taylor tail with a geometric series.
The reconstruction stages are: universal implication; real parameters and natural
Taylor indices; bounded absolute value and strict positive denominator; Taylor-tail
comparison; factorial and geometric-series estimates; casts and field arithmetic.
-/

namespace GraphicalAllocation.Probability

open scoped BigOperators

/-- The geometric majorant for the factorials in the quadratic Taylor tail. -/
private lemma factorial_geometric_bound (n : ℕ) :
    (2 : ℝ) * 3 ^ n ≤ (Nat.factorial (n + 2) : ℝ) := by
  exact_mod_cast (show 2 * 3 ^ n ≤ (n + 2).factorial by
    simpa [Nat.add_comm] using @Nat.factorial_mul_pow_le_factorial 2 n)

/-- A Taylor term after the linear term is dominated by a geometric term. -/
private lemma exp_tail_term_le {z r : ℝ} (hr : 0 ≤ r) (hz : |z| ≤ r) (n : ℕ) :
    z ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) ≤
      z ^ 2 / 2 * (r / 3) ^ n := by
  have hfact : 0 < (Nat.factorial (n + 2) : ℝ) := by positivity
  have hzpow : z ^ n ≤ r ^ n := calc
    z ^ n ≤ |z ^ n| := le_abs_self _
    _ = |z| ^ n := abs_pow _ _
    _ ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg z) hz _
  calc
    z ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) =
        z ^ 2 * z ^ n / (Nat.factorial (n + 2) : ℝ) := by ring
    _ ≤ z ^ 2 * r ^ n / (Nat.factorial (n + 2) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzpow (sq_nonneg z)) hfact.le
    _ ≤ z ^ 2 * r ^ n / (2 * 3 ^ n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (factorial_geometric_bound n)
    _ = z ^ 2 / 2 * (r / 3) ^ n := by rw [div_pow]; ring

/-- The bounded-argument Bernstein majorant for the exponential. -/
theorem exp_le_bernstein_quadratic {z r : ℝ} (hr : 0 ≤ r) (hr3 : r < 3)
    (hz : |z| ≤ r) :
    Real.exp z ≤ 1 + z + z ^ 2 / (2 * (1 - r / 3)) := by
  have hexp : HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have htail : HasSum (fun n : ℕ => z ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
      (Real.exp z - (1 + z)) := by
    simpa [Finset.sum_range_succ, Nat.factorial] using (hasSum_nat_add_iff' 2).2 hexp
  have hgeom := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ r / 3)
    (by linarith : r / 3 < 1)).mul_left (z ^ 2 / 2)
  have hle := hasSum_le (exp_tail_term_le hr hz) htail hgeom
  have heq : z ^ 2 / 2 * (1 - r / 3)⁻¹ = z ^ 2 / (2 * (1 - r / 3)) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [heq] at hle
  linarith

/-- Scalar input to the conditional bounded-increment Bernstein estimate. -/
theorem exp_mul_le_bernstein {b χ x : ℝ} (hb : 0 ≤ b) (hχ : 0 ≤ χ)
    (hχb : χ * b < 3) (hx : |x| ≤ b) :
    Real.exp (χ * x) ≤ 1 + χ * x +
      (χ ^ 2 / (2 * (1 - χ * b / 3))) * x ^ 2 := by
  have hz : |χ * x| ≤ χ * b := by
    rw [abs_mul, abs_of_nonneg hχ]
    exact mul_le_mul_of_nonneg_left hx hχ
  convert exp_le_bernstein_quadratic (mul_nonneg hχ hb) hχb hz using 1
  ring

/-- A finite centered distribution obeys the one-step Bernstein exponential bound. -/
theorem sum_mul_exp_le_exp_variance {ι : Type*} [Fintype ι]
    {p x : ι → ℝ} {b χ v : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hmean : ∑ i, p i * x i = 0)
    (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hχb : χ * b < 3)
    (hx : ∀ i, |x i| ≤ b) (hvar : ∑ i, p i * (x i) ^ 2 ≤ v) :
    ∑ i, p i * Real.exp (χ * x i) ≤
      Real.exp ((χ ^ 2 / (2 * (1 - χ * b / 3))) * v) := by
  let c : ℝ := χ ^ 2 / (2 * (1 - χ * b / 3))
  have hden : 0 < 1 - χ * b / 3 := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  change ∑ i, p i * Real.exp (χ * x i) ≤ Real.exp (c * v)
  calc
    ∑ i, p i * Real.exp (χ * x i) ≤
        ∑ i, (p i + χ * (p i * x i) + c * (p i * (x i) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      convert mul_le_mul_of_nonneg_left (exp_mul_le_bernstein hb hχ hχb (hx i)) (hp i)
        using 1
      dsimp [c]
      ring
    _ = 1 + c * (∑ i, p i * (x i) ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hpsum, hmean, mul_zero, add_zero]
    _ ≤ 1 + c * v := add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar hc)
    _ ≤ Real.exp (c * v) := by simpa [add_comm] using Real.add_one_le_exp (c * v)

/-- The usual positive Bernstein exponential parameter. -/
theorem bernstein_parameter_pos {a b σ : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hσ : 0 < σ) : 0 < a / (σ + b * a / 3) := by
  positivity

/-- The usual parameter lies within the domain of the Bernstein majorant. -/
theorem bernstein_parameter_mul_lt_three {a b σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hσ : 0 < σ) : (a / (σ + b * a / 3)) * b < 3 := by
  have hden : 0 < σ + b * a / 3 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith

/-- Substitution of the usual parameter into the exponential exponent. -/
theorem bernstein_exponent_eq {a b σ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hσ : 0 < σ) :
    -(a / (σ + b * a / 3)) * a +
      ((a / (σ + b * a / 3)) ^ 2 /
        (2 * (1 - (a / (σ + b * a / 3)) * b / 3))) * σ =
      -(a ^ 2 / (2 * (σ + b * a / 3))) := by
  have hden : 0 < σ + b * a / 3 := by positivity
  have hinner : 1 - (a / (σ + b * a / 3)) * b / 3 = σ / (σ + b * a / 3) := by
    field_simp [hden.ne']
    ring
  rw [hinner]
  field_simp [hden.ne', hσ.ne']
  ring

/-- The square-root plus linear Bernstein threshold is positive. -/
theorem bernstein_threshold_pos {b σ s : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ)
    (hs : 0 < s) : 0 < Real.sqrt (2 * σ * s) + (2 * b / 3) * s := by
  positivity

/-- The usual parameter turns the Bernstein threshold into exponent at most `-s`. -/
theorem bernstein_threshold_exponent {b σ s : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ)
    (hs : 0 < s) :
    let a := Real.sqrt (2 * σ * s) + (2 * b / 3) * s;
    let χ := a / (σ + b * a / 3);
    -χ * a + (χ ^ 2 / (2 * (1 - χ * b / 3))) * σ ≤ -s := by
  dsimp only
  rw [bernstein_exponent_eq (bernstein_threshold_pos hb hσ hs).le hb hσ]
  have hroot := Real.sq_sqrt (show 0 ≤ 2 * σ * s by positivity)
  have hden : 0 < 2 * (σ + b * (Real.sqrt (2 * σ * s) + (2 * b / 3) * s) / 3) := by
    positivity
  rw [neg_le_neg_iff, le_div_iff₀ hden]
  nlinarith [mul_nonneg (mul_nonneg hb hs.le) (Real.sqrt_nonneg (2 * σ * s))]

end GraphicalAllocation.Probability
