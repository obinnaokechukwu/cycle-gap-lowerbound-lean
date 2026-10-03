import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-!
# The rectangular-torus reciprocal-volume integral

The exact logarithmic-plus-linear integral is proved as an ordinary Lebesgue
interval integral. Positivity makes the integrand continuous on every compact
interval in use, discharging rather than assuming its integrability.
-/

namespace GraphicalAllocation.Geometry

open MeasureTheory

/-- Integrability of the reciprocal of a capped radius on positive intervals. -/
theorem reciprocalMin_intervalIntegrable {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun r : ℝ => 1 / min K r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuous_const.min continuous_id).continuousOn
  intro r hr
  exact ne_of_gt (lt_min hK ((lt_min ha hb).trans_le hr.1))

/-- The exact integral used for rectangular tori: logarithmic until radius K,
then linear after the short coordinate has saturated. -/
theorem reciprocalMin_integral {K L : ℝ} (hK : 1 ≤ K) (hL : K ≤ L) :
    (∫ r in (1:ℝ)..L, 1 / min K r) = L / K + Real.log K - 1 := by
  have hK₀ : 0 < K := lt_of_lt_of_le one_pos hK
  have hL₀ : 0 < L := hK₀.trans_le hL
  have hleft : (∫ r in (1:ℝ)..K, 1 / min K r) = Real.log K := by
    calc
      _ = ∫ r in (1:ℝ)..K, 1 / r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [Set.uIcc_of_le hK] at hr
        dsimp
        rw [min_eq_right hr.2]
      _ = Real.log K := by rw [integral_one_div_of_pos one_pos hK₀]; simp
  have hright : (∫ r in K..L, 1 / min K r) = L / K - 1 := by
    calc
      _ = ∫ r in K..L, 1 / K := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [Set.uIcc_of_le hL] at hr
        dsimp
        rw [min_eq_left hr.1]
      _ = L / K - 1 := by rw [intervalIntegral.integral_const]; simp; field_simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (reciprocalMin_intervalIntegrable hK₀ one_pos hK₀)
    (reciprocalMin_intervalIntegrable hK₀ hK₀ hL₀), hleft, hright]
  ring

/-- The volume integrand is nonincreasing on the positive half-line. -/
theorem reciprocalMin_antitone {K : ℝ} (hK : 0 < K) :
    AntitoneOn (fun r : ℝ => 1 / min K r) (Set.Ioi 0) := by
  intro a ha b hb hab
  exact one_div_le_one_div_of_le (lt_min hK ha) (min_le_min_left K hab)

/-- On radii at least one, this integrand is at most one. -/
theorem reciprocalMin_le_one {K r : ℝ} (hK : 1 ≤ K) (hr : 1 ≤ r) :
    1 / min K r ≤ 1 := by
  exact (div_le_one (lt_of_lt_of_le one_pos (le_min hK hr))).mpr (le_min hK hr)

end GraphicalAllocation.Geometry
