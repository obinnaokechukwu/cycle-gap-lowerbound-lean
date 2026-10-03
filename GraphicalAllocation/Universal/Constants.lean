import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Explicit logarithmic-window constants

This module proves the floor, logarithm, and regular-graph size estimates used
by Proposition 7.8. In particular the numerical assumptions are retained as
published, rather than replaced by assumptions about untouched probabilities.
-/

noncomputable section
namespace GraphicalAllocation.Universal

/-- The prescribed number of arrivals in the final window. -/
def logWindow (N : ℕ) : ℕ := ⌊(N : ℝ) / 16 * Real.log N⌋₊

/-- The window's deterministic increase in average load. -/
def windowAverage (N : ℕ) : ℝ := (logWindow N : ℝ) / N

lemma log_ge_one {N : ℝ} (hN : 1000 ≤ N) : 1 ≤ Real.log N := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < N)).mpr
  exact Real.exp_one_lt_three.le.trans (by linarith)

lemma windowAverage_bounds (N : ℕ) (hN : (1000 : ℝ) ≤ N) :
    Real.log N / 32 ≤ windowAverage N ∧ windowAverage N ≤ Real.log N / 16 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog := log_ge_one hN
  have hfloor : (logWindow N : ℝ) ≤ (N : ℝ) / 16 * Real.log N :=
    Nat.floor_le (by positivity)
  have hfloor' : (N : ℝ) / 16 * Real.log N - 1 < (logWindow N : ℝ) :=
    Nat.sub_one_lt_floor _
  have hprod : 32 ≤ (N : ℝ) * Real.log N := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hN0.le]
  unfold windowAverage
  constructor
  · apply (le_div_iff₀ hN0).mpr
    nlinarith
  · apply (div_le_iff₀ hN0).mpr
    nlinarith

lemma windowAverage_pos (N : ℕ) (hN : (1000 : ℝ) ≤ N) : 0 < windowAverage N := by
  have := (windowAverage_bounds N hN).1
  have := log_ge_one hN
  linarith

/-- Elementary logarithmic estimate, including both endpoints of the interval. -/
lemma log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hy : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  have hfrac : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    apply (mul_le_mul_iff_left₀ hy).mp
    have hc : (1 - (1 - x)⁻¹) * (1 - x) = -x := by field_simp; ring
    rw [hc]
    nlinarith
  exact hfrac.trans hlog

/-- The untouched probability is bounded below directly from the window size. -/
lemma untouched_probability_lower (N : ℕ) (hN : (1000 : ℝ) ≤ N) :
    Real.exp (-(Real.log N) / 4) ≤
      (1 - 2 / (N : ℝ)) ^ logWindow N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 ≤ 2 / (N : ℝ) := by positivity
  have hx' : 2 / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hN0).mpr
    linarith
  have hb : 0 < 1 - 2 / (N : ℝ) := by linarith
  have hlog := log_one_sub_lower hx hx'
  have hτ := (windowAverage_bounds N hN).2
  have hexp : -(Real.log N) / 4 ≤ (logWindow N : ℝ) * Real.log (1 - 2 / (N : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (logWindow N))
    have hm' : -4 * ((logWindow N : ℝ) / N) ≤
        (logWindow N : ℝ) * Real.log (1 - 2 / (N : ℝ)) := by
      convert hm using 1
      ring
    unfold windowAverage at hτ
    linarith
  calc
    _ ≤ Real.exp ((logWindow N : ℝ) * Real.log (1 - 2 / (N : ℝ))) := Real.exp_le_exp.mpr hexp
    _ = (1 - 2 / (N : ℝ)) ^ logWindow N := by rw [Real.exp_nat_mul, Real.exp_log hb]

/-- Rewriting the paper's `4/3` size condition in the form used by the mean bound. -/
lemma size_condition_three_quarters {N D : ℝ} (hD : 0 ≤ D)
    (hsize : D ^ (4 / 3 : ℝ) ≤ N) : D ≤ N ^ (3 / 4 : ℝ) := by
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hD _) hsize (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [← Real.rpow_mul hD] at hp
  norm_num at hp
  exact hp

/-- An independent set of the greedy size has at least one expected untouched
vertex under exactly the published graph-size assumption. -/
lemma untouched_mean_ge_one (N I Δ : ℕ) (hN : (1000 : ℝ) ≤ N)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ N)
    (hI : (N : ℝ) ≤ 9 * ((Δ : ℝ) + 1) * I) :
    1 ≤ (I : ℝ) * (1 - 2 / (N : ℝ)) ^ logWindow N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hD : (0 : ℝ) < 9 * ((Δ : ℝ) + 1) := by positivity
  have hthree := size_condition_three_quarters hD.le hsize
  have hpow := untouched_probability_lower N hN
  have hid : (9 * ((Δ : ℝ) + 1)) ≤ (N : ℝ) * Real.exp (-(Real.log N) / 4) := by
    calc
      _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) := hthree
      _ = (N : ℝ) * Real.exp (-(Real.log N) / 4) := by
        rw [Real.rpow_def_of_pos hN0, ← Real.exp_log hN0, ← Real.exp_add]
        congr 1
        simp only [Real.log_exp]
        ring
  have hmul := mul_le_mul_of_nonneg_right hI (Real.exp_pos (-(Real.log N) / 4)).le
  have hIexp : 1 ≤ (I : ℝ) * Real.exp (-(Real.log N) / 4) := by nlinarith
  exact hIexp.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg I))

/-- The universal size threshold for a degree-four graph is below 1000. -/
lemma degree_four_size : (9 * ((4 : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ 1000 := by
  have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 45)
    (by norm_num : (45 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have he : (64 : ℝ) ^ (4 / 3 : ℝ) = 256 := by
    rw [show (64 : ℝ) = (4 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  norm_num only [show (9 * ((4 : ℝ) + 1)) = 45 by norm_num]
  rw [he] at hp
  linarith

end GraphicalAllocation.Universal
