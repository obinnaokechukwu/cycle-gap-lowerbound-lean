import GraphicalAllocation.Applications.Graphs.SingleScale
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # The cylinder radius, horizon, and advertised constant -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs

/-- The explicit degree-dependent cylinder constant. -/
def cylinderConstant (Δ : ℝ) : ℝ := 1 / (2048 * Real.pi * Real.sqrt (Δ * (Δ + 1)))

lemma cylinder_radius_bounds {L : ℕ} (hL : 120 ≤ L) :
    (L : ℝ) / 7 ≤ (L / 6 : ℕ) ∧
    4 * Real.pi ≤ (L / 6 : ℕ) ∧
    2 * (L / 6 : ℕ) + 1 ≤ (L : ℝ) / 2 ∧
    2 * (L / 6) ≤ L / 2 := by
  have h₁ : L ≤ 7 * (L / 6) := by omega
  have h₂ : 20 ≤ L / 6 := by omega
  have h₃ : 2 * (2 * (L / 6) + 1) ≤ L := by omega
  have h₁r : (L : ℝ) ≤ 7 * (L / 6 : ℕ) := by exact_mod_cast h₁
  have h₂r : (20 : ℝ) ≤ (L / 6 : ℕ) := by exact_mod_cast h₂
  have h₃r : 2 * (2 * (L / 6 : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast h₃
  refine ⟨by linarith, by linarith [Real.pi_lt_four], by linarith, ?_⟩
  omega

lemma cylinder_small_scale {L w Δ : ℝ} (hL : 0 ≤ L) (hLupper : L < 120)
    (hw : 1 ≤ w) (hΔ : 2 ≤ Δ) :
    cylinderConstant Δ * Real.sqrt (L / w) ≤ 1 / 3 := by
  have hδ : 1 ≤ Δ * (Δ + 1) := by nlinarith
  have hsδ : 1 ≤ Real.sqrt (Δ * (Δ + 1)) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hδ)
  have hratio : L / w ≤ L := (div_le_self hL hw)
  have hsL : Real.sqrt (L / w) ≤ 12 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  unfold cylinderConstant
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 2048 * Real.pi * Real.sqrt (Δ * (Δ + 1)))).mpr
  nlinarith [Real.pi_gt_three]

lemma cylinder_horizon_le_square {L R Δ : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hRL : R ≤ L) (hΔ : 2 ≤ Δ) :
    embeddingHorizon (Real.pi / 2) (Δ * (Δ + 1)) R ≤ L ^ 2 := by
  have hδ : 6 ≤ Δ * (Δ + 1) := by nlinarith
  have hden : 1 ≤ 64 * (Real.pi / 2) ^ 2 * (Δ * (Δ + 1)) := by
    have hp : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith
  unfold embeddingHorizon
  exact (div_le_self (sq_nonneg R) hden).trans ((sq_le_sq₀ hR hL).mpr hRL)

/-- The single-scale bound dominates the advertised cylinder constant, with
room to spare; all arguments are numerical or geometric size quantities. -/
lemma cylinder_scale_comparison {L w Δ R B a : ℝ} (hL : 0 < L) (hw : 0 < w)
    (hΔ : 2 ≤ Δ) (hR : L / 7 ≤ R) (hB : 0 < B) (hBcap : B ≤ w * L / 2)
    (ha : 1 ≤ a) :
    cylinderConstant Δ * Real.sqrt (L / w) ≤
      Real.sqrt (a * embeddingHorizon (Real.pi / 2) (Δ * (Δ + 1)) R / (4 * B)) / 16 := by
  have hδ : 0 < Δ * (Δ + 1) := by nlinarith
  have hRp : 0 < R := (div_pos hL (by norm_num)).trans_le hR
  have h₁ : 0 ≤ a * embeddingHorizon (Real.pi / 2) (Δ * (Δ + 1)) R / (4 * B) := by
    unfold embeddingHorizon
    positivity
  apply (sq_le_sq₀ (by unfold cylinderConstant; positivity) (by positivity)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt h₁, Real.sq_sqrt (by positivity : 0 ≤ L / w)]
  unfold cylinderConstant embeddingHorizon
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hδ.le]
  have hRsq : L ^ 2 ≤ 49 * R ^ 2 := by nlinarith
  have hmul : 2 * B * L ≤ w * L ^ 2 := by nlinarith
  have haR : R ^ 2 ≤ a * R ^ 2 := le_mul_of_one_le_left (sq_nonneg R) ha
  field_simp
  nlinarith

end GraphicalAllocation.Applications.Graphs
