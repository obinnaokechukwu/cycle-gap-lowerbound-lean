import GraphicalAllocation.Geometry.CycleMetric
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# First Fourier coordinate and the edge-normalized circle

The coordinate is Mathlib's standard additive character on `ZMod n`, composed
with its canonical ring equivalence from `Fin n`. The metric in every bound is
the genuine shortest-path metric established in `CycleMetric`.
-/

noncomputable section
namespace GraphicalAllocation.Geometry

open SimpleGraph
open scoped Fin.CommRing

/-- The first Fourier coordinate of a cyclic vertex. -/
def cycleFourier (n : ℕ) (u : Fin (n + 3)) : ℂ :=
  ZMod.toCircle (ZMod.finEquiv (n + 3) u)

@[simp] theorem norm_cycleFourier (n : ℕ) (u : Fin (n + 3)) :
    ‖cycleFourier n u‖ = 1 := Circle.norm_coe _

/-- Translation by a signed lift acts by the standard complex character. -/
theorem cycleFourier_add_int (n : ℕ) (u : Fin (n + 3)) (k : ℤ) :
    cycleFourier n (u + (k : Fin (n + 3))) =
      cycleFourier n u * Complex.exp (2 * Real.pi * Complex.I * k / (n + 3)) := by
  simp only [cycleFourier, map_add, map_intCast, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [ZMod.toCircle_intCast]
  push_cast
  rfl

/-- The chord is computed from the unique balanced integer lift. -/
theorem cycleFourier_chord_lift (n : ℕ) (u v : Fin (n + 3)) :
    ‖cycleFourier n v - cycleFourier n u‖ =
      2 * |Real.sin (Real.pi * cycleLift n u v / (n + 3))| := by
  have hv : v = u + (cycleLift n u v : Fin (n + 3)) := by rw [cycleLift_cast]; abel
  conv_lhs => rw [hv, cycleFourier_add_int]
  rw [← mul_sub_one, norm_mul, norm_cycleFourier, one_mul]
  have he : (2 * Real.pi * Complex.I * (cycleLift n u v : ℂ) / (n + 3)) =
      Complex.I * ((2 * Real.pi * (cycleLift n u v : ℝ) / (n + 3) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have ha : (2 * Real.pi * (cycleLift n u v : ℝ) / (n + 3)) / 2 =
      Real.pi * cycleLift n u v / (n + 3) := by ring
  rw [ha, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]

/-- The balanced lift lies in the half-circle interval. -/
theorem cycleLift_abs_le_half (n : ℕ) (u v : Fin (n + 3)) :
    |(cycleLift n u v : ℝ)| ≤ ((n + 3 : ℕ) : ℝ) / 2 := by
  have h := (ZMod.finEquiv (n + 3) (v - u)).valMinAbs_mem_Ioc
  change -(n + 3 : ℤ) < cycleLift n u v * 2 ∧ cycleLift n u v * 2 ≤ (n + 3 : ℤ) at h
  have hl : -((n + 3 : ℕ) : ℝ) < (cycleLift n u v : ℝ) * 2 := by exact_mod_cast h.1
  have hu : (cycleLift n u v : ℝ) * 2 ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast h.2
  rw [abs_le]
  constructor <;> linarith 

/-- Jordan's inequality gives the paper's sharp linear chord lower bound. -/
theorem cycleFourier_chord_lower (n : ℕ) (u v : Fin (n + 3)) :
    4 * ((cycleGraph (n + 3)).dist u v : ℝ) / (n + 3) ≤
      ‖cycleFourier n v - cycleFourier n u‖ := by
  have hn : (0:ℝ) < n + 3 := by positivity
  have ha := cycleLift_abs_le_half n u v
  push_cast at ha
  have harg : |Real.pi * (cycleLift n u v : ℝ) / (n + 3)| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn] at hs
  rw [cycleFourier_chord_lift, cycle_dist_eq_lift]
  have hk : ((cycleLift n u v).natAbs : ℝ) = |(cycleLift n u v : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hk]
  have he : 2 / Real.pi * (Real.pi * |(cycleLift n u v : ℝ)| / (n + 3)) =
      2 * |(cycleLift n u v : ℝ)| / (n + 3) := by field_simp
  rw [he] at hs
  convert mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2) using 1
  ring

/-- Exact Fourier chord in terms of the canonical graph distance. -/
theorem cycleFourier_chord (n : ℕ) (u v : Fin (n + 3)) :
    ‖cycleFourier n v - cycleFourier n u‖ =
      2 * Real.sin (Real.pi * ((cycleGraph (n + 3)).dist u v : ℝ) / (n + 3)) := by
  have hn : (0:ℝ) < n + 3 := by positivity
  have ha := cycleLift_abs_le_half n u v
  push_cast at ha
  have harg : |Real.pi * (cycleLift n u v : ℝ) / (n + 3)| ≤ Real.pi := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    nlinarith [Real.pi_pos]
  rw [cycleFourier_chord_lift, Real.abs_sin_eq_sin_abs_of_abs_le_pi harg,
    abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hn, cycle_dist_eq_lift,
    Nat.cast_natAbs, Int.cast_abs]

/-- Adjacent Fourier coordinates have chord length `2 sin(π/n)`. -/
theorem cycleFourier_edge (n : ℕ) {u v : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj u v) :
    ‖cycleFourier n v - cycleFourier n u‖ = 2 * Real.sin (Real.pi / (n + 3)) := by
  rw [cycleFourier_chord, dist_eq_one_iff_adj.mpr h]
  simp

/-- The normalizing edge chord is strictly positive. -/
theorem cycle_sin_pos (n : ℕ) : 0 < Real.sin (Real.pi / (n + 3)) := by
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < n + 3)).mpr
  nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]

/-- The paper's edge-normalized circle embedding. -/
def cycleEmbedding (n : ℕ) (u : Fin (n + 3)) : ℂ :=
  (2 * Real.sin (Real.pi / (n + 3)))⁻¹ • cycleFourier n u

/-- Chords of the normalized embedding. -/
theorem cycleEmbedding_chord (n : ℕ) (u v : Fin (n + 3)) :
    ‖cycleEmbedding n v - cycleEmbedding n u‖ =
      ‖cycleFourier n v - cycleFourier n u‖ / (2 * Real.sin (Real.pi / (n + 3))) := by
  rw [cycleEmbedding, cycleEmbedding, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (mul_pos (by norm_num) (cycle_sin_pos n))]
  ring

/-- Every actual graph edge is mapped to a unit Hilbert chord. -/
theorem cycleEmbedding_edge (n : ℕ) {u v : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj u v) :
    ‖cycleEmbedding n v - cycleEmbedding n u‖ = 1 := by
  rw [cycleEmbedding_chord, cycleFourier_edge n h, div_self]
  exact ne_of_gt (mul_pos (by norm_num) (cycle_sin_pos n))

/-- Distortion at most `π/2` for the actual cycle metric. -/
theorem cycleEmbedding_distortion (n : ℕ) (u v : Fin (n + 3)) :
    ((cycleGraph (n + 3)).dist u v : ℝ) ≤
      Real.pi / 2 * ‖cycleEmbedding n v - cycleEmbedding n u‖ := by
  have hn : (0:ℝ) < n + 3 := by positivity
  have hd : (0:ℝ) ≤ (cycleGraph (n + 3)).dist u v := by positivity
  have hs := Real.sin_le (div_nonneg Real.pi_pos.le hn.le)
  have hc := cycleFourier_chord_lower n u v
  have hsc : Real.sin (Real.pi / (n + 3)) * (n + 3) ≤ Real.pi :=
    (le_div_iff₀ hn).mp hs
  have hcc : 4 * ((cycleGraph (n + 3)).dist u v : ℝ) ≤
      ‖cycleFourier n v - cycleFourier n u‖ * (n + 3) := (div_le_iff₀ hn).mp hc
  have hmain : ((cycleGraph (n + 3)).dist u v : ℝ) *
      (2 * Real.sin (Real.pi / (n + 3))) ≤
        Real.pi / 2 * ‖cycleFourier n v - cycleFourier n u‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hsc (show (0:ℝ) ≤ 2 * ((cycleGraph (n + 3)).dist u v : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hcc (Real.pi_pos.le)
    have h₃ : (n + 3) *
        (((cycleGraph (n + 3)).dist u v : ℝ) * (2 * Real.sin (Real.pi / (n + 3)))) ≤
        (n + 3) * (Real.pi / 2 * ‖cycleFourier n v - cycleFourier n u‖) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hn).mp h₃
  rw [cycleEmbedding_chord, ← mul_div_assoc]
  exact (le_div_iff₀ (mul_pos (by norm_num) (cycle_sin_pos n))).mpr hmain

end GraphicalAllocation.Geometry
