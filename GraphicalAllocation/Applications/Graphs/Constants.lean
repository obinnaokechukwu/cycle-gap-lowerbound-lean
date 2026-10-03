import GraphicalAllocation.Applications.Graphs.Radii
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # The constants and small-scale alternatives in Section 7 -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs

/-- The fixed radius coefficient for two-dimensional tori. -/
def torusKappa : ℝ := 4 * Real.pi * Real.sqrt 21

/-- The advertised universal two-dimensional constant. -/
def torusConstant : ℝ := 1 / (1280 * Real.pi * Real.sqrt 42)

lemma torusKappa_pos : 0 < torusKappa := by unfold torusKappa; positivity

lemma one_le_torusKappa : 1 ≤ torusKappa := by
  have hs : 1 ≤ Real.sqrt 21 := by norm_num
  unfold torusKappa
  nlinarith [Real.pi_gt_three]

lemma torusKappa_sq : torusKappa ^ 2 = 16 * (21 * Real.pi ^ 2) := by
  unfold torusKappa
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

lemma torusConstant_pos : 0 < torusConstant := by unfold torusConstant; positivity

/-- Exact conversion of the square-root coefficient after the affine integral estimate. -/
lemma torusConstant_eq : torusConstant = 1 / (320 * Real.sqrt 2 * torusKappa) := by
  have hs : Real.sqrt 42 = Real.sqrt 2 * Real.sqrt 21 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold torusConstant torusKappa
  rw [hs]
  ring

lemma torusConstant_sq : torusConstant ^ 2 = 1 / (204800 * torusKappa ^ 2) := by
  rw [torusConstant_eq, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

/-- The bounded-Z regime needs only the rational 1/3 phase estimate. -/
theorem torus_small_scale {Z : ℝ} (_hZ : 0 ≤ Z) (hZupper : Z ≤ 32 * (1 + torusKappa)) :
    torusConstant * Real.sqrt Z ≤ 1 / 3 := by
  have hκ := one_le_torusKappa
  have hs2 : 1 ≤ Real.sqrt 2 := by norm_num
  have hsZ : Real.sqrt Z ≤ 10 * torusKappa := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (torusKappa - 1)]
  rw [torusConstant_eq]
  have hden : 0 < 320 * Real.sqrt 2 * torusKappa := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hs2 (show 0 ≤ torusKappa by positivity)]

/-- If the long side does not reach the radius construction, its scale belongs
to the same bounded-Z regime, without a separate probabilistic argument. -/
theorem torus_short_side_scale {K L : ℝ} (hK : 3 ≤ K) (hKL : K ≤ L)
    (hL : L < 16 * torusKappa) :
    L / K + Real.log K ≤ 32 * (1 + torusKappa) := by
  have hKp : 0 < K := by linarith
  have hLpos : 0 ≤ L := by linarith
  have hdiv : L / K ≤ L / 3 := by gcongr
  have hlog : Real.log K ≤ K - 1 := Real.log_le_sub_one_of_pos hKp
  have hκ := one_le_torusKappa
  linarith

/-- The large-Z regime absorbs the affine error term exactly. -/
theorem torus_affine_large {Z : ℝ} (hZ : 32 * (1 + torusKappa) ≤ Z) :
    Z / (200 * torusKappa ^ 2) ≤
      Z / (100 * torusKappa ^ 2) - 4 * (1 + torusKappa) / (25 * torusKappa ^ 2) := by
  have hκ := torusKappa_pos
  apply (le_sub_iff_add_le).mpr
  calc
    _ = (Z + 32 * (1 + torusKappa)) / (200 * torusKappa ^ 2) := by ring
    _ ≤ (2 * Z) / (200 * torusKappa ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = Z / (100 * torusKappa ^ 2) := by ring

/-- The final threshold is bounded by the generic sqrt(I)/32 lower scale. -/
theorem torus_scale_comparison {Z I : ℝ} (hZ : 0 ≤ Z)
    (hI : Z / (200 * torusKappa ^ 2) ≤ I) :
    torusConstant * Real.sqrt Z ≤ Real.sqrt I / 32 := by
  have hκ := torusKappa_pos
  have hInonneg : 0 ≤ I := (by positivity : 0 ≤ Z / (200 * torusKappa ^ 2)).trans hI
  apply (sq_le_sq₀ (mul_nonneg torusConstant_pos.le (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [mul_pow, torusConstant_sq, Real.sq_sqrt hZ, div_pow, Real.sq_sqrt hInonneg]
  have h := div_le_div_of_nonneg_right hI (by norm_num : (0:ℝ) ≤ 1024)
  convert h using 1 <;> ring

lemma torus_horizon_le_square {L : ℝ} (hL : 0 ≤ L) :
    torusHorizon torusKappa L ≤ L ^ 2 := by
  have hκ := one_le_torusKappa
  have hdiv : L / (16 * torusKappa) ≤ L := div_le_self hL (by linarith)
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ L / (16 * torusKappa)) hL).mpr hdiv
  unfold torusHorizon
  linarith

end GraphicalAllocation.Applications.Graphs
