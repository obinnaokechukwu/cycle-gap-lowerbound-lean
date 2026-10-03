import GraphicalAllocation.Gaussian.AbsoluteMoment
import GraphicalAllocation.Smoothed.Constants
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Numerical comparison with the normalized Gaussian range

The scalar estimate in (8.2) is first rewritten using the Gaussian absolute
moment.  The lower bound `d * R ≥ 1/3` then absorbs the additive constants.
-/

noncomputable section

namespace GraphicalAllocation.Gaussian

open Real

/-- An explicit coefficient for the `O_ζ(√d log N)` Gaussian-range comparison. -/
def gaussianRangeComparisonConstant (ζ : ℝ) : ℝ := 24 * Smoothed.beta ζ + 6

lemma gaussianRangeComparisonConstant_eq (ζ : ℝ) :
    gaussianRangeComparisonConstant ζ = 48 * ζ + 54 := by
  unfold gaussianRangeComparisonConstant Smoothed.beta
  ring

/-- Exact substitution in the displayed bound of the Gaussian free field remark. -/
theorem gaussianRange_substitution {B d N ζ R M : ℝ}
    (hd : 1 ≤ d) (hN : 3 ≤ N) (hζ : 1 ≤ ζ) (_hR : 0 ≤ R)
    (hM : sqrt (2 / π) * sqrt (d * R) ≤ M)
    (hB : B ≤ 2 * Smoothed.beta ζ * log N *
      (2 * sqrt (d * (4 * d + 3) * R) + 4 / 3) + 2) :
    B ≤ 2 * Smoothed.beta ζ * log N *
      (2 * sqrt (π * (4 * d + 3) / 2) * M + 4 / 3) + 2 := by
  have hd0 : 0 ≤ d := by linarith
  have hlog : 0 ≤ log N := le_trans (by norm_num) (Smoothed.log_ge_one hN)
  have hb : 0 ≤ Smoothed.beta ζ := le_trans (by norm_num) (Smoothed.beta_ge_four hζ)
  have hroot : sqrt (d * (4 * d + 3) * R) ≤ sqrt (π * (4 * d + 3) / 2) * M := by
    calc
      _ = sqrt (π * (4 * d + 3) / 2) * (sqrt (2 / π) * sqrt (d * R)) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / π),
          ← Real.sqrt_mul (by positivity : 0 ≤ π * (4 * d + 3) / 2)]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (sqrt_nonneg _)
  apply hB.trans
  have hscale : 0 ≤ 2 * Smoothed.beta ζ * log N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot hscale]

/-- The resistance lower bound forces a uniform positive Gaussian range. -/
lemma gaussianRange_one_third_le {d R M : ℝ}
    (hres : 1 / 3 ≤ d * R) (hM : sqrt (2 / π) * sqrt (d * R) ≤ M) :
    1 / 3 ≤ M := by
  have ha : (2 / 3 : ℝ) ≤ sqrt (2 / π) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_lt_four]
  have hb : (1 / 2 : ℝ) ≤ sqrt (d * R) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hab := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (sqrt_nonneg _)
  nlinarith

/-- Absorb every additive term into an explicit multiple of `√d log N M`. -/
theorem gaussianRange_absorption {B d N ζ R M : ℝ}
    (hd : 1 ≤ d) (hN : 3 ≤ N) (hζ : 1 ≤ ζ) (hR : 0 ≤ R)
    (hM : sqrt (2 / π) * sqrt (d * R) ≤ M) (hres : 1 / 3 ≤ d * R)
    (hB : B ≤ 2 * Smoothed.beta ζ * log N *
      (2 * sqrt (d * (4 * d + 3) * R) + 4 / 3) + 2) :
    B ≤ gaussianRangeComparisonConstant ζ * sqrt d * log N * M := by
  have hdisplay := gaussianRange_substitution hd hN hζ hR hM hB
  have hd0 : 0 ≤ d := by linarith
  have hlog := Smoothed.log_ge_one hN
  have hlog0 : 0 ≤ log N := by linarith
  have hb := Smoothed.beta_ge_four hζ
  have hb0 : 0 ≤ Smoothed.beta ζ := by linarith
  have hMlower := gaussianRange_one_third_le hres hM
  have hM0 : 0 ≤ M := by linarith
  have hsd : 1 ≤ sqrt d := by
    apply Real.le_sqrt_of_sq_le
    simpa using hd
  have hroot : sqrt (π * (4 * d + 3) / 2) ≤ 4 * sqrt d := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le
        (by linarith : 0 ≤ 4 * d + 3)
      nlinarith [Real.sq_sqrt hd0]
  let D : ℝ := sqrt d * log N * M
  have hDlog : log N ≤ 3 * D := by
    have hsm := mul_le_mul_of_nonneg_right hsd hM0
    have hq : 1 ≤ 3 * (sqrt d * M) := by nlinarith
    have h := mul_le_mul_of_nonneg_right hq hlog0
    dsimp [D]
    nlinarith
  have hDone : 1 ≤ 3 * D := hlog.trans hDlog
  have hmain :
      4 * Smoothed.beta ζ * log N * sqrt (π * (4 * d + 3) / 2) * M ≤
        16 * Smoothed.beta ζ * D := by
    have h := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 4 * Smoothed.beta ζ * log N * M by positivity)
    dsimp [D]
    nlinarith
  have hconstant := mul_le_mul_of_nonneg_left hDlog hb0
  have hbound : B ≤ (24 * Smoothed.beta ζ + 6) * D := by
    nlinarith
  simpa only [gaussianRangeComparisonConstant, D, mul_assoc] using hbound

end GraphicalAllocation.Gaussian
