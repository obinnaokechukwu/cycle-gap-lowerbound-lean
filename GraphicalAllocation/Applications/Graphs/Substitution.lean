import GraphicalAllocation.Applications.Graphs.Integrals
import GraphicalAllocation.Applications.Graphs.Radii
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The lag-to-radius change of variables, with its exact coefficient -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs
open MeasureTheory Set Geometry

/-- The substitution r=κ√(s+1) contributes the factor 2/κ². -/
theorem sqrt_radius_substitution {K κ T : ℝ} (hK : 0 < K) (hκ : 0 < κ) (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..T, 1 / (κ * Real.sqrt (s + 1) * min K (κ * Real.sqrt (s + 1)))) =
      (2 / κ ^ 2) * ∫ r in κ..(κ * Real.sqrt (T + 1)), 1 / min K r := by
  let f : ℝ → ℝ := fun s => κ * Real.sqrt (s + 1)
  let f' : ℝ → ℝ := fun s => κ / (2 * Real.sqrt (s + 1))
  have hspos : ∀ s ∈ uIcc 0 T, 0 < s + 1 := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    linarith [hs.1]
  have hderiv : ∀ s ∈ uIcc 0 T, HasDerivAt f (f' s) s := by
    intro s hs
    have h := (((hasDerivAt_id s).add_const 1).sqrt (ne_of_gt (hspos s hs))).const_mul κ
    simpa [f, f', div_eq_mul_inv, mul_assoc] using h
  have hcont : ContinuousOn f' (uIcc 0 T) := by
    apply continuousOn_const.div
      (continuous_const.mul ((continuous_id.add continuous_const).sqrt)).continuousOn
    intro s hs
    exact ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (hspos s hs)))
  have hg : ContinuousOn (fun r : ℝ => 1 / min K r) (f '' uIcc 0 T) := by
    apply continuousOn_const.div (continuous_const.min continuous_id).continuousOn
    rintro r ⟨s, hs, rfl⟩
    exact ne_of_gt (lt_min hK (mul_pos hκ (Real.sqrt_pos.2 (hspos s hs))))
  have hsubst := intervalIntegral.integral_comp_mul_deriv' hderiv hcont hg
  have hzero : f 0 = κ := by simp [f]
  rw [hzero] at hsubst
  rw [← hsubst, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsqrt : Real.sqrt (s + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hspos s hs))
  dsimp [f, f']
  field_simp

/-- The exact transformed endpoint is L/16 at the chosen horizon. -/
theorem torus_radius_substitution {K κ L : ℝ} (hK : 0 < K) (hκ : 0 < κ)
    (hL : 16 * κ ≤ L) :
    (∫ s in (0:ℝ)..torusHorizon κ L,
      1 / (κ * Real.sqrt (s + 1) * min K (κ * Real.sqrt (s + 1)))) =
      (2 / κ ^ 2) * ∫ r in κ..(L / 16), 1 / min K r := by
  rw [sqrt_radius_substitution hK hκ (torusHorizon_nonneg hκ hL),
    torusHorizon_sqrt hκ (by linarith)]

/-- The coefficient in (7.7): m/N=2 and the volume comparison contributes 1/25. -/
theorem torus_volume_integral {K κ L : ℝ} (hK : 0 < K) (hκ : 0 < κ)
    (hL : 16 * κ ≤ L) :
    2 * (∫ s in (0:ℝ)..torusHorizon κ L,
      1 / (25 * (κ * Real.sqrt (s + 1)) * min K (κ * Real.sqrt (s + 1)))) =
      (4 / (25 * κ ^ 2)) * ∫ r in κ..(L / 16), 1 / min K r := by
  have hfun : (fun s : ℝ =>
      1 / (25 * (κ * Real.sqrt (s + 1)) * min K (κ * Real.sqrt (s + 1)))) =
      fun s => (1 / 25 : ℝ) *
        (1 / (κ * Real.sqrt (s + 1) * min K (κ * Real.sqrt (s + 1)))) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_const_mul, torus_radius_substitution hK hκ hL]
  ring

/-- The integrated comparison produces the affine lower bound in the torus
scale Z. This is an unconditional analytic inequality. -/
theorem torus_volume_integral_lower {K κ L : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L)
    (hκ : 1 ≤ κ) (hL : 16 * κ ≤ L) :
    (L / K + Real.log K) / (100 * κ ^ 2) - 4 * (1 + κ) / (25 * κ ^ 2) ≤
      2 * (∫ s in (0:ℝ)..torusHorizon κ L,
        1 / (25 * (κ * Real.sqrt (s + 1)) * min K (κ * Real.sqrt (s + 1)))) := by
  rw [torus_volume_integral (one_pos.trans_le hK) (one_pos.trans_le hκ) hL]
  have h := mul_le_mul_of_nonneg_left (reciprocalMin_truncated hK hKL hκ hL)
    (show 0 ≤ 4 / (25 * κ ^ 2) by positivity)
  convert h using 1
  ring

end GraphicalAllocation.Applications.Graphs
