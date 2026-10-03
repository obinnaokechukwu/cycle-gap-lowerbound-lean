import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Checked numerical parameters for the cycle applications

This file contains no probabilistic assumptions. All floors, time horizons and
constants used in the continuous and exact-event-count cycle applications are
proved here over the real and natural numbers.
-/

namespace GraphicalAllocation.Applications
noncomputable section

lemma pi_one_le : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
lemma pi_sq_one_le : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [pi_one_le]
lemma pi_sq_lt_sixteen : Real.pi ^ 2 < 16 := by
  nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- The paper's `min(√n,t^(1/4))`, expressed using iterated square roots. -/
def cycleScale (n t : ℝ) : ℝ := Real.sqrt (min n (Real.sqrt t))

/-- The continuous lower-bound constant, without hidden asymptotic choices. -/
def cycleConstant : ℝ := 1 / (1024 * Real.pi * Real.sqrt 3)

/-- The exact-count lower-bound constant. -/
def discreteCycleConstant : ℝ := 1 / (16384 * Real.pi * Real.sqrt 3)

lemma cycleConstant_pos : 0 < cycleConstant := by unfold cycleConstant; positivity
lemma discreteCycleConstant_pos : 0 < discreteCycleConstant := by
  unfold discreteCycleConstant; positivity

lemma sqrt_three_one_le : (1 : ℝ) ≤ Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]

lemma continuous_min_comparison {n t : ℝ} (_hn : 0 ≤ n) :
    min n (Real.sqrt t) ≤ 2 * min (n / 2) (Real.sqrt t) := by
  rw [min_def (n / 2)]
  split_ifs with h
  · linarith [min_le_left n (Real.sqrt t)]
  · linarith [min_le_right n (Real.sqrt t), Real.sqrt_nonneg t]

lemma continuous_floor_parameters {n t : ℝ} (hn : 0 ≤ n)
    (r : ℕ) (hr : r = ⌊min (n / 2) (Real.sqrt t)⌋₊) :
    (r : ℝ) ≤ n / 2 ∧ (r : ℝ) ≤ Real.sqrt t ∧
      (24 ≤ r → min n (Real.sqrt t) ≤ 3 * r) ∧
      (r < 24 → min n (Real.sqrt t) < 48) := by
  have hy : 0 ≤ min (n / 2) (Real.sqrt t) := le_min (by positivity) (Real.sqrt_nonneg t)
  have hlo : (r : ℝ) ≤ min (n / 2) (Real.sqrt t) := hr ▸ Nat.floor_le hy
  have hhi : min (n / 2) (Real.sqrt t) < (r : ℝ) + 1 := by
    simpa only [hr] using Nat.lt_floor_add_one (min (n / 2) (Real.sqrt t))
  refine ⟨hlo.trans (min_le_left _ _), hlo.trans (min_le_right _ _), ?_, ?_⟩
  · intro hlarge
    have hlarge' : (24 : ℝ) ≤ r := by exact_mod_cast hlarge
    linarith [continuous_min_comparison (t := t) hn]
  · intro hsmall
    have hsmall' : (r : ℝ) ≤ 23 := by exact_mod_cast (show r ≤ 23 by omega)
    linarith [continuous_min_comparison (t := t) hn]

lemma continuous_radius_parameters {r : ℕ} (hr : 24 ≤ r) :
    8 ≤ r / 3 ∧ r ≤ 4 * (r / 3) ∧ 2 * (r / 3) + 1 ≤ r ∧
      3 * (r / 3) ≤ r := by omega

lemma continuous_time_parameter {t : ℝ} (ht : 0 ≤ t) {r R : ℕ}
    (hr : (r : ℝ) ≤ Real.sqrt t) (hR : R ≤ r) :
    (R : ℝ) ^ 2 / (64 * Real.pi ^ 2) ≤ t := by
  have hRR : (R : ℝ) ≤ Real.sqrt t := (by exact_mod_cast hR : (R : ℝ) ≤ r).trans hr
  have hs : (R : ℝ) ^ 2 ≤ t := by
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t, (Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi ^ 2)).mpr
  nlinarith [pi_sq_one_le]

lemma continuous_tail_parameter {R : ℝ} (hR : 8 ≤ R) {s : ℝ}
    (hs : s ≤ R ^ 2 / (64 * Real.pi ^ 2)) :
    (2 * Real.pi ^ 2 * s + 2) / R ^ 2 ≤ 1 / 16 := by
  have hRp : 0 < R ^ 2 := by positivity
  have hs' := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi ^ 2)).mp hs
  apply (div_le_iff₀ hRp).mpr
  nlinarith

lemma continuous_quantile_arithmetic {r R M : ℝ}
    (hr : 0 ≤ r) (hR : 8 ≤ R) (hrR : r ≤ 4 * R)
    (hvol : 2 * R + 1 ≤ r) (hM : 0 ≤ M)
    (htransport : R ^ 2 / (64 * Real.pi ^ 2) / (4 * (2 * R + 1)) ≤ M ^ 2) :
    Real.sqrt r / (64 * Real.pi) ≤ M := by
  have hden : 0 < 64 * Real.pi ^ 2 * (4 * (2 * R + 1)) := by positivity
  have hbase : R ^ 2 ≤ M ^ 2 * (64 * Real.pi ^ 2 * (4 * (2 * R + 1))) := by
    apply (div_le_iff₀ hden).mp
    simpa only [div_div] using htransport
  have hrpos : 0 < r := by linarith
  have hsquare : r ≤ 4096 * Real.pi ^ 2 * M ^ 2 := by
    have hRR : r ^ 2 ≤ 16 * R ^ 2 := by nlinarith
    have hMM : 0 ≤ M ^ 2 * (64 * Real.pi ^ 2) := by positivity
    have hbound : M ^ 2 * (64 * Real.pi ^ 2 * (4 * (2 * R + 1))) ≤
        M ^ 2 * (64 * Real.pi ^ 2 * (4 * r)) := by nlinarith
    have hp : r * r ≤ (4096 * Real.pi ^ 2 * M ^ 2) * r := by nlinarith
    exact (mul_le_mul_iff_of_pos_right hrpos).mp hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi)).mpr
  have hp : 0 ≤ M * (64 * Real.pi) := by positivity
  have hsq : (Real.sqrt r) ^ 2 ≤ (M * (64 * Real.pi)) ^ 2 := by
    nlinarith [Real.sq_sqrt hr]
  exact (sq_le_sq₀ (Real.sqrt_nonneg r) hp).mp hsq

lemma continuous_scale_comparison {n t r : ℝ} (hn : 0 ≤ n)
    (hr : min n (Real.sqrt t) ≤ 3 * r) :
    cycleConstant * cycleScale n t ≤ (Real.sqrt r / (64 * Real.pi)) / 16 := by
  have hr0 : 0 ≤ r := by linarith [le_min hn (Real.sqrt_nonneg t)]
  have hs := Real.sq_sqrt (le_min hn (Real.sqrt_nonneg t))
  have hsr := Real.sq_sqrt hr0
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsbound : Real.sqrt (min n (Real.sqrt t)) ≤ Real.sqrt r * Real.sqrt 3 := by
    have hprod : 0 ≤ Real.sqrt r * Real.sqrt 3 := by positivity
    nlinarith [Real.sqrt_nonneg (min n (Real.sqrt t))]
  unfold cycleConstant cycleScale
  have hp : 0 < Real.pi := Real.pi_pos
  have h3p : 0 < Real.sqrt (3 : ℝ) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi)).mpr
  field_simp
  nlinarith

lemma continuous_small_scale {n t : ℝ} (hn : 0 ≤ n)
    (hsmall : min n (Real.sqrt t) < 48) :
    cycleConstant * cycleScale n t ≤ 1 / 3 := by
  have hs : Real.sqrt (min n (Real.sqrt t)) < 8 := by
    nlinarith [Real.sq_sqrt (le_min hn (Real.sqrt_nonneg t)),
      Real.sqrt_nonneg (min n (Real.sqrt t))]
  unfold cycleConstant cycleScale
  have hden : 0 < 1024 * Real.pi * Real.sqrt (3 : ℝ) := by positivity
  have hdenlo : (24 : ℝ) ≤ 1024 * Real.pi * Real.sqrt 3 := by
    nlinarith [pi_one_le, sqrt_three_one_le]
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hden).mpr
  linarith


lemma discrete_min_comparison {n t : ℝ} (_hn : 0 ≤ n) :
    min n (Real.sqrt t) ≤ 512 * min (n / 512) (Real.sqrt t) := by
  rw [min_def (n / 512)]
  split_ifs with h
  · linarith [min_le_left n (Real.sqrt t)]
  · linarith [min_le_right n (Real.sqrt t), Real.sqrt_nonneg t]

lemma discrete_floor_parameters {n t : ℝ} (hn : 0 ≤ n)
    (R : ℕ) (hR : R = ⌊min (n / 512) (Real.sqrt t)⌋₊) :
    (R : ℝ) ≤ n / 512 ∧ (R : ℝ) ≤ Real.sqrt t ∧
      (8 ≤ R → min n (Real.sqrt t) ≤ 1024 * R) ∧
      (R < 8 → min n (Real.sqrt t) < 4096) := by
  have hy : 0 ≤ min (n / 512) (Real.sqrt t) := le_min (by positivity) (Real.sqrt_nonneg t)
  have hlo : (R : ℝ) ≤ min (n / 512) (Real.sqrt t) := hR ▸ Nat.floor_le hy
  have hhi : min (n / 512) (Real.sqrt t) < (R : ℝ) + 1 := by
    simpa only [hR] using Nat.lt_floor_add_one (min (n / 512) (Real.sqrt t))
  refine ⟨hlo.trans (min_le_left _ _), hlo.trans (min_le_right _ _), ?_, ?_⟩
  · intro hlarge
    have hlarge' : (8 : ℝ) ≤ R := by exact_mod_cast hlarge
    linarith [discrete_min_comparison (t := t) hn]
  · intro hsmall
    have hsmall' : (R : ℝ) ≤ 7 := by exact_mod_cast (show R ≤ 7 by omega)
    linarith [discrete_min_comparison (t := t) hn]

lemma discrete_radius_parameters {n R : ℝ} (hR : 8 ≤ R) (hnR : R ≤ n / 512) :
    4096 ≤ n ∧ 2 * R + 1 ≤ n / 128 ∧ 2 * R + 1 ≤ 3 * R := by
  constructor
  · linarith
  constructor <;> linarith

lemma discrete_horizon_argument {n R : ℝ} (hR : 8 ≤ R) (hnR : R ≤ n / 512) :
    2 ≤ n * R ^ 2 / (64 * Real.pi ^ 2) := by
  have hn : 4096 ≤ n := (discrete_radius_parameters hR hnR).1
  have hR2 : (64 : ℝ) ≤ R ^ 2 := by nlinarith
  have hprod : 4096 * 64 ≤ n * R ^ 2 := mul_le_mul hn hR2 (by norm_num) (by linarith)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi ^ 2)).mpr
  nlinarith [pi_sq_lt_sixteen]

lemma floor_half_of_two_le {a : ℝ} (ha : 2 ≤ a) : a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one a
  linarith

lemma discrete_horizon_parameters {n : ℝ} (hn : 0 < n) {k R : ℕ}
    (hR : 8 ≤ R) (hnR : (R : ℝ) ≤ n / 512)
    (hkR : (R : ℝ) ≤ Real.sqrt (k / n)) :
    let H := ⌊n * (R : ℝ) ^ 2 / (64 * Real.pi ^ 2)⌋₊
    1 ≤ H ∧ H ≤ k ∧
      n * (R : ℝ) ^ 2 / (128 * Real.pi ^ 2) ≤ (H : ℝ) := by
  let a := n * (R : ℝ) ^ 2 / (64 * Real.pi ^ 2)
  have hR' : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have ha : 2 ≤ a := discrete_horizon_argument hR' hnR
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hhalf : a / 2 ≤ (⌊a⌋₊ : ℝ) := floor_half_of_two_le ha
  have hfirst : 1 ≤ ⌊a⌋₊ := by
    exact_mod_cast (show (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) by linarith)
  have hR2 : (R : ℝ) ^ 2 ≤ (k : ℝ) / n := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) / n by positivity),
      Real.sqrt_nonneg ((k : ℝ) / n), (Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hR2' : n * (R : ℝ) ^ 2 ≤ k := by
    have hh := (le_div_iff₀ hn).mp hR2
    nlinarith
  have hak : a ≤ k := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi ^ 2)).mpr
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [pi_sq_one_le]
  have hlast : n * (R : ℝ) ^ 2 / (128 * Real.pi ^ 2) ≤ (⌊a⌋₊ : ℝ) := by
    convert hhalf using 1
    dsimp [a]
    ring
  refine ⟨hfirst, ?_, hlast⟩
  have hnat : ⌊a⌋₊ ≤ k := by exact_mod_cast hfloor.trans hak
  exact hnat

lemma discrete_tail_parameter {n R h : ℝ} (hn : 0 < n) (hR : 8 ≤ R)
    (hh : h ≤ n * R ^ 2 / (64 * Real.pi ^ 2)) :
    (2 * Real.pi ^ 2 * h / n + 2) / R ^ 2 ≤ 1 / 16 := by
  have hh' := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * Real.pi ^ 2)).mp hh
  have hinner : 2 * Real.pi ^ 2 * h / n ≤ R ^ 2 / 32 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)).mpr
  nlinarith

lemma discrete_quantile_arithmetic {n R H M ell : ℝ}
    (hn : 0 < n) (hR : 8 ≤ R) (hM : 0 ≤ M)
    (hell : 0 ≤ ell) (hellR : ell ≤ 1024 * R)
    (hH : n * R ^ 2 / (128 * Real.pi ^ 2) ≤ H)
    (htransport : H / (8 * n * (2 * R + 1)) ≤ M ^ 2) :
    Real.sqrt ell / (1024 * Real.pi * Real.sqrt 3) ≤ M := by
  have hH' : n * R ^ 2 ≤ H * (128 * Real.pi ^ 2) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 128 * Real.pi ^ 2)).mp hH
  have hT : H ≤ M ^ 2 * (8 * n * (2 * R + 1)) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n * (2 * R + 1))).mp htransport
  have hV : 2 * R + 1 ≤ 3 * R := by linarith
  have hp : 0 ≤ M ^ 2 * (8 * n) := by positivity
  have hT' : H ≤ M ^ 2 * (8 * n * (3 * R)) := by nlinarith
  have hTpi : H * (128 * Real.pi ^ 2) ≤
      (M ^ 2 * (8 * n * (3 * R))) * (128 * Real.pi ^ 2) :=
    mul_le_mul_of_nonneg_right hT' (by positivity)
  have hmain : R ≤ 3072 * Real.pi ^ 2 * M ^ 2 := by
    have hmult : R * (n * R) ≤ (3072 * Real.pi ^ 2 * M ^ 2) * (n * R) := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < n * R)).mp hmult
  have hsquare : ell ≤ (1024 * Real.pi * Real.sqrt 3) ^ 2 * M ^ 2 := by
    have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1024 * Real.pi * Real.sqrt 3)).mpr
  have hnonneg : 0 ≤ M * (1024 * Real.pi * Real.sqrt 3) := by positivity
  have hs : (Real.sqrt ell) ^ 2 ≤ (M * (1024 * Real.pi * Real.sqrt 3)) ^ 2 := by
    nlinarith [Real.sq_sqrt hell]
  exact (sq_le_sq₀ (Real.sqrt_nonneg ell) hnonneg).mp hs

lemma discrete_scale_identity (n t : ℝ) :
    discreteCycleConstant * cycleScale n t =
      (Real.sqrt (min n (Real.sqrt t)) / (1024 * Real.pi * Real.sqrt 3)) / 16 := by
  unfold discreteCycleConstant cycleScale
  ring

lemma discrete_small_scale {n t : ℝ} (hn : 0 ≤ n)
    (hsmall : min n (Real.sqrt t) < 4096) :
    discreteCycleConstant * cycleScale n t ≤ 1 / 3 := by
  have hs : Real.sqrt (min n (Real.sqrt t)) < 64 := by
    nlinarith [Real.sq_sqrt (le_min hn (Real.sqrt_nonneg t)),
      Real.sqrt_nonneg (min n (Real.sqrt t))]
  unfold discreteCycleConstant cycleScale
  have hden : 0 < 16384 * Real.pi * Real.sqrt (3 : ℝ) := by positivity
  have hdenlo : (192 : ℝ) ≤ 16384 * Real.pi * Real.sqrt 3 := by
    nlinarith [pi_one_le, sqrt_three_one_le]
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hden).mpr
  linarith

/-- Agreement with the exponent notation in both introductory theorem statements. -/
lemma cycleScale_eq_min (n t : ℝ) (ht : 0 ≤ t) :
    cycleScale n t = min (Real.sqrt n) (t ^ (1 / 4 : ℝ)) := by
  have hs : Real.sqrt (Real.sqrt t) = t ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
    norm_num
  unfold cycleScale
  rw [← hs]
  exact Real.sqrt_monotone.map_min


lemma cycleScale_saturated {n t : ℝ} (_hn : 0 ≤ n) (ht : n ^ 2 ≤ t) :
    cycleScale n t = Real.sqrt n := by
  have ht0 : 0 ≤ t := (sq_nonneg n).trans ht
  have hs : n ≤ Real.sqrt t := by
    nlinarith [Real.sq_sqrt ht0, Real.sqrt_nonneg t]
  simp [cycleScale, min_eq_left hs]

lemma discrete_cycleScale_saturated {n k : ℝ} (hn : 0 < n) (hk : n ^ 3 ≤ k) :
    cycleScale n (k / n) = Real.sqrt n := by
  apply cycleScale_saturated hn.le
  apply (le_div_iff₀ hn).mpr
  nlinarith

end
end GraphicalAllocation.Applications
