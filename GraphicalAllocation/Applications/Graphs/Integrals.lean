import GraphicalAllocation.Geometry.TorusIntegral
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-! # Rescaling and truncating the rectangular-torus scale integral
The reciprocal integrand and its exact primitive are established in geometry.
This module verifies that restricting the usable radii loses only a bounded
initial contribution and a fixed scale factor.
-/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs
open MeasureTheory Set Geometry

/-- The initial part of the capped reciprocal integral costs at most its length. -/
theorem reciprocalMin_integral_le_length {K b : ℝ} (hK : 1 ≤ K) (hb : 1 ≤ b) :
    (∫ r in 1..b, 1 / min K r) ≤ b - 1 := by
  have hKp : 0 < K := lt_of_lt_of_le one_pos hK
  calc
    _ ≤ ∫ _r in (1:ℝ)..b, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on hb
        (reciprocalMin_intervalIntegrable hKp one_pos (one_pos.trans_le hb))
        intervalIntegrable_const
      intro r hr
      exact reciprocalMin_le_one hK hr.1
    _ = b - 1 := by simp

/-- Monotonicity under dilation by sixteen, including the removed initial
interval. The large-radius integral retains one sixteenth of the full scale. -/
theorem reciprocalMin_rescaling {K L : ℝ} (hK : 1 ≤ K) (hL : 16 ≤ L) :
    (∫ r in (1:ℝ)..L, 1 / min K r) / 16 - 15 / 16 ≤
      ∫ r in (1:ℝ)..(L / 16), 1 / min K r := by
  have hKp : 0 < K := one_pos.trans_le hK
  have hLp : 0 < L := by linarith
  have hL16 : 1 ≤ L / 16 := by linarith
  have hscale : (∫ r in (16:ℝ)..L, 1 / min K r) =
      16 * ∫ r in (1:ℝ)..(L / 16), 1 / min K (16 * r) := by
    simpa [show 16 * (L / 16) = L by ring] using (intervalIntegral.mul_integral_comp_mul_left (f := fun r : ℝ => 1 / min K r)
      (a := 1) (b := L / 16) 16).symm
  have hmono : (∫ r in (1:ℝ)..(L / 16), 1 / min K (16 * r)) ≤
      ∫ r in (1:ℝ)..(L / 16), 1 / min K r := by
    apply intervalIntegral.integral_mono_on hL16
    · apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div (continuous_const.min (continuous_const.mul continuous_id)).continuousOn
      intro r hr
      rw [uIcc_of_le hL16] at hr
      exact ne_of_gt (lt_min hKp (show 0 < 16 * r by nlinarith [hr.1]))
    · exact reciprocalMin_intervalIntegrable hKp one_pos (by positivity)
    · intro r hr
      exact reciprocalMin_antitone hKp
        (show 0 < r by linarith [hr.1])
        (show 0 < 16 * r by nlinarith [hr.1]) (by nlinarith [hr.1])
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (reciprocalMin_intervalIntegrable hKp one_pos (by norm_num : (0:ℝ) < 16))
    (reciprocalMin_intervalIntegrable hKp (by norm_num : (0:ℝ) < 16) hLp)
  have hinitial := reciprocalMin_integral_le_length hK (by norm_num : (1:ℝ) ≤ 16)
  rw [hscale] at hadd
  nlinarith

/-- The precise truncation inequality used in the torus proof; the proof gives
an extra unit of slack beyond the displayed estimate. -/
theorem reciprocalMin_truncated {K L κ : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L)
    (hκ : 1 ≤ κ) (hL : 16 * κ ≤ L) :
    (L / K + Real.log K) / 16 - 1 - κ ≤
      ∫ r in κ..(L / 16), 1 / min K r := by
  have hKp : 0 < K := one_pos.trans_le hK
  have hκp : 0 < κ := one_pos.trans_le hκ
  have hLp : 0 < L := by nlinarith
  have hscale := reciprocalMin_rescaling hK (by nlinarith : (16:ℝ) ≤ L)
  rw [reciprocalMin_integral hK hKL] at hscale
  have hinitial := reciprocalMin_integral_le_length hK hκ
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (reciprocalMin_intervalIntegrable hKp one_pos hκp)
    (reciprocalMin_intervalIntegrable hKp hκp (by positivity : 0 < L / 16))
  linarith

end GraphicalAllocation.Applications.Graphs
