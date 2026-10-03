import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! # Measurable protected radii and explicit horizon bounds -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs
open MeasureTheory Set

/-- The radius used at response lag s; integer rounding is upward. -/
def torusRadius (κ s : ℝ) : ℝ := ⌈κ * Real.sqrt (s + 1)⌉₊

lemma measurable_torusRadius (κ : ℝ) : Measurable (torusRadius κ) := by
  unfold torusRadius
  fun_prop

lemma torusRadius_ge (κ s : ℝ) : κ * Real.sqrt (s + 1) ≤ torusRadius κ s :=
  Nat.le_ceil _

lemma torusRadius_lt {κ s : ℝ} (hκ : 0 ≤ κ) :
    torusRadius κ s < κ * Real.sqrt (s + 1) + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg hκ (Real.sqrt_nonneg _))

lemma torusRadius_pos {κ s : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s) :
    0 < torusRadius κ s :=
  (mul_pos hκ (Real.sqrt_pos.2 (by linarith))).trans_le (torusRadius_ge _ _)

lemma torusRadius_volume_factor {κ s : ℝ} (hκ : 1 ≤ κ) (hs : 0 ≤ s) :
    2 * torusRadius κ s + 1 ≤ 5 * (κ * Real.sqrt (s + 1)) := by
  have hsqrt : 1 ≤ Real.sqrt (s + 1) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hr : 1 ≤ κ * Real.sqrt (s + 1) := by nlinarith
  have hceil := torusRadius_lt (show 0 ≤ κ by linarith) (s := s)
  linarith

/-- The finite horizon for which the long-coordinate shift remains separated. -/
def torusHorizon (κ L : ℝ) : ℝ := (L / (16 * κ)) ^ 2 - 1

lemma torusHorizon_nonneg {κ L : ℝ} (hκ : 0 < κ) (hL : 16 * κ ≤ L) :
    0 ≤ torusHorizon κ L := by
  have h : 1 ≤ L / (16 * κ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  unfold torusHorizon
  nlinarith

lemma torusHorizon_sqrt {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) :
    κ * Real.sqrt (torusHorizon κ L + 1) = L / 16 := by
  unfold torusHorizon
  rw [sub_add_cancel, Real.sqrt_sq (by positivity : 0 ≤ L / (16 * κ))]
  field_simp

lemma torusRadius_le_eighth {κ L s : ℝ} (hκ : 1 ≤ κ) (hL : 16 * κ ≤ L)
    (_hs : 0 ≤ s) (hsT : s ≤ torusHorizon κ L) :
    torusRadius κ s ≤ L / 8 := by
  have hκp : 0 < κ := one_pos.trans_le hκ
  have hLp : 0 ≤ L := by nlinarith
  have hbase : κ * Real.sqrt (s + 1) ≤ L / 16 := by
    rw [← torusHorizon_sqrt hκp hLp]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hκp.le
  have hceil := torusRadius_lt hκp.le (s := s)
  have hL16 : 16 ≤ L := by nlinarith
  linarith

/-- Squared-displacement Markov estimates stay below 1/16 with κ=4√C. -/
lemma torusRadius_tail_bound {C κ s : ℝ} (_hC : 0 ≤ C) (hκ : 0 < κ)
    (hκsq : κ ^ 2 = 16 * C) (hs : 0 ≤ s) :
    C * (s + 1) / torusRadius κ s ^ 2 ≤ 1 / 16 := by
  have hR := torusRadius_pos hκ hs
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  have hsq := (sq_le_sq₀ (mul_nonneg hκ.le (Real.sqrt_nonneg _)) hR.le).mpr
    (torusRadius_ge κ s)
  rw [mul_pow, Real.sq_sqrt (by linarith), hκsq] at hsq
  nlinarith

/-- Saturating the short side commutes with a fivefold volume enlargement up
to the same factor; this prevents losing an extra factor of five. -/
lemma capped_volume_scaling {K r a : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (har : a ≤ 5 * r) :
    a * min K a ≤ 25 * r * min K r := by
  have hmin : min K a ≤ 5 * min K r := by
    by_cases hKr : K ≤ r
    · rw [min_eq_left hKr]
      exact (min_le_left K a).trans (by linarith)
    · rw [min_eq_right (le_of_not_ge hKr)]
      exact (min_le_right K a).trans har
  calc
    a * min K a ≤ (5 * r) * (5 * min K r) :=
      mul_le_mul har hmin (le_min hK ha) (by positivity)
    _ = 25 * r * min K r := by ring

/-- The integer ceiling costs at most the displayed factor 25. -/
lemma torusRadius_volume_bound {K κ s : ℝ} (hK : 0 ≤ K) (hκ : 1 ≤ κ) (hs : 0 ≤ s) :
    (2 * torusRadius κ s + 1) * min K (2 * torusRadius κ s + 1) ≤
      25 * (κ * Real.sqrt (s + 1)) * min K (κ * Real.sqrt (s + 1)) := by
  apply capped_volume_scaling hK (by positivity)
  · have := torusRadius_pos (one_pos.trans_le hκ) hs
    positivity
  · exact torusRadius_volume_factor hκ hs

end GraphicalAllocation.Applications.Graphs
