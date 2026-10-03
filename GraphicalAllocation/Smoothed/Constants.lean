import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Numerical parameters for polynomial-horizon smoothed allocation -/

noncomputable section
namespace GraphicalAllocation.Smoothed

/-- The concentration exponent prescribed by the paper. -/
def beta (ζ : ℝ) : ℝ := 2 * ζ + 2

/-- The fixed cutoff, chosen once for the desired polynomial horizon. -/
def cutoff (N d ζ : ℝ) : ℝ := (4 * d + 3) * beta ζ * Real.log N

lemma log_ge_one {N : ℝ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  exact (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hN)

lemma beta_ge_four {ζ : ℝ} (hζ : 1 ≤ ζ) : 4 ≤ beta ζ := by unfold beta; linarith

lemma scale_pos {N ζ : ℝ} (hN : 3 ≤ N) (hζ : 1 ≤ ζ) :
    0 < beta ζ * Real.log N := by
  have := log_ge_one hN
  have := beta_ge_four hζ
  positivity

lemma cutoff_ge_twelve {N d ζ : ℝ} (hN : 3 ≤ N) (hd : 0 ≤ d) (hζ : 1 ≤ ζ) :
    12 ≤ cutoff N d ζ := by
  have hlog := log_ge_one hN
  have hb := beta_ge_four hζ
  have hs : 4 ≤ beta ζ * Real.log N := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ beta ζ - 4) (by linarith : 0 ≤ Real.log N - 1)]
  unfold cutoff
  nlinarith [mul_nonneg hd (by linarith : 0 ≤ beta ζ * Real.log N - 4)]

lemma cutoff_pos {N d ζ : ℝ} (hN : 3 ≤ N) (hd : 0 ≤ d) (hζ : 1 ≤ ζ) :
    0 < cutoff N d ζ := lt_of_lt_of_le (by norm_num) (cutoff_ge_twelve hN hd hζ)

lemma exp_neg_scale {N ζ : ℝ} (hN : 0 < N) :
    Real.exp (-(beta ζ * Real.log N)) = N ^ (-beta ζ) := by
  rw [Real.rpow_def_of_pos hN]
  congr 1
  ring

/-- The graph smoothing step stays inside the positive-contraction range. -/
lemma stepsize_bound {N d m ζ : ℝ} (hN : 3 ≤ N) (hd : 0 < d) (hm : 0 < m)
    (hcount : N * d = 2 * m) (hζ : 1 ≤ ζ) :
    (1 / (2 * m * cutoff N d ζ)) * (2 * d) ≤ 1 := by
  have hθ := cutoff_ge_twelve hN hd.le hζ
  have hden : 0 < 2 * m * cutoff N d ζ := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hden]
  have hprod : 2 ≤ N * cutoff N d ζ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hprod hd.le
  nlinarith

/-- The edge Bernstein cutoff is strictly inside the chosen threshold. -/
lemma edge_bernstein_threshold_le {d s : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) :
    Real.sqrt (2 * (2 * d * ((4 * d + 3) * s)) * s) + (4 / 3) * s ≤
      (4 * d + 3) * s := by
  have hroot : Real.sqrt (2 * (2 * d * ((4 * d + 3) * s)) * s) ≤
      (4 * d + 3 / 2) * s := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg s]
  nlinarith

lemma vertex_bernstein_threshold {d s R : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (2 * (2 * d * ((4 * d + 3) * s) * R) * s) + (4 / 3) * s =
      s * (2 * Real.sqrt (d * (4 * d + 3) * R) + 4 / 3) := by
  rw [show 2 * (2 * d * ((4 * d + 3) * s) * R) * s =
      (2 * s) ^ 2 * (d * (4 * d + 3) * R) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * s)]
  ring

/-- The exceptional-event contribution to expected gap is at most two. -/
lemma exceptional_expectation_le_two {N m k ζ : ℝ} (hN : 3 ≤ N) (hm : 0 ≤ m)
    (hmN : m ≤ N ^ 2 / 2) (hk : 0 ≤ k) (hζ : 1 ≤ ζ) (hkN : k ≤ N ^ ζ) :
    k * (2 * k * m + 2 * N) * N ^ (-beta ζ) ≤ 2 := by
  have hN₀ : 0 < N := by linarith
  have ht : 0 < N ^ ζ := Real.rpow_pos_of_pos hN₀ _
  have htN : N ≤ N ^ ζ := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) hζ
  have hb : N ^ beta ζ = (N ^ ζ) ^ 2 * N ^ 2 := by
    rw [beta, Real.rpow_add hN₀, mul_comm 2 ζ, Real.rpow_mul hN₀.le]
    simp only [Real.rpow_two]
  rw [Real.rpow_neg hN₀.le, hb, ← div_eq_mul_inv]
  have hden : 0 < (N ^ ζ) ^ 2 * N ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hbound : k * (2 * k * m + 2 * N) ≤
      (N ^ ζ) * (2 * (N ^ ζ) * (N ^ 2 / 2) + 2 * N) := by
    gcongr
  have hprod : 2 ≤ (N ^ ζ) * N := by nlinarith
  nlinarith [mul_nonneg (by positivity : 0 ≤ (N ^ ζ) * N)
    (by linarith : 0 ≤ (N ^ ζ) * N - 2)]

end GraphicalAllocation.Smoothed
