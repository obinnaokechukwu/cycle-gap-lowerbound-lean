import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Gamma

open MeasureTheory Set Real
open scoped NNReal

namespace GraphicalAllocation.Gaussian

-- Stages 0–2: the scalar variance is nonnegative; the integral is Bochner's real integral.
theorem integrable_abs_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x|) (ProbabilityTheory.gaussianReal μ v) := by
  have h := ProbabilityTheory.memLp_id_gaussianReal (μ := μ) (v := v) 1
  simpa only [Real.norm_eq_abs, id_eq] using (memLp_one_iff_integrable.mp h).norm

-- Stages 3–5: integrate on the positive half-line and use symmetry.
private theorem integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| * exp (-b * x ^ 2)) = b⁻¹ := by
  have hi : Integrable (fun x : ℝ => |x| * exp (-b * x ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).norm
  have hhalf : (∫ x : ℝ in Ioi 0, |x| * exp (-b * x ^ 2)) = b⁻¹ / 2 := by
    calc
      _ = ∫ x : ℝ in Ioi 0, x ^ (1 : ℝ) * exp (-b * x ^ (2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [abs_of_pos (show 0 < x from hx), Real.rpow_one, Real.rpow_two]
      _ = b⁻¹ / 2 := by
        have h := integral_rpow_mul_exp_neg_mul_rpow
          (p := 2) (q := 1) (b := b) (by norm_num) (by norm_num) hb
        norm_num [Real.rpow_neg_one, Real.Gamma_one] at h
        simpa [div_eq_mul_inv] using h
  have heq : (∫ x : ℝ in Iic 0, |x| * exp (-b * x ^ 2)) =
      ∫ x : ℝ in Ioi 0, |x| * exp (-b * x ^ 2) := by
    calc
      _ = ∫ x : ℝ in Ioi 0, |-x| * exp (-b * (-x) ^ 2) := by
        simpa only [neg_zero] using
          (integral_comp_neg_Ioi 0 (fun x : ℝ => |x| * exp (-b * x ^ 2))).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        dsimp only
        rw [abs_neg, neg_sq]
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hi, compl_Ioi, heq, hhalf]
  ring

theorem integral_abs_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂ProbabilityTheory.gaussianReal 0 v) =
      Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, smul_eq_mul]
  have hf : (fun x : ℝ => (√(2 * π * (v : ℝ)))⁻¹ * exp (-x ^ 2 / (2 * v)) * |x|) =
      (fun x : ℝ => (√(2 * π * (v : ℝ)))⁻¹ * (|x| * exp (-(2 * (v : ℝ))⁻¹ * x ^ 2))) := by
    ext x
    have he : -x ^ 2 / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * x ^ 2 := by ring
    rw [he]
    ring
  rw [hf, integral_const_mul, integral_abs_mul_exp_neg_mul_sq (by positivity), inv_inv]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) * π),
    Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_div (by norm_num : 0 ≤ (2 : ℝ))]
  have hs2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have hsv := Real.sq_sqrt hvpos.le
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hspine : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsvne : Real.sqrt (v : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hvpos)
  field_simp
  nlinarith

end GraphicalAllocation.Gaussian
