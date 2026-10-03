import GraphicalAllocation.Smoothed.Constants
import GraphicalAllocation.Spectral.Cycle

/-!
# Exact constants in the smoothed cycle corollary

The reconstruction stages are: (0) universal numerical inequalities; (1) real
cycle size and time; (2) the paper's cutoff, square root, and Poisson moment;
(3) bound the square root, then absorb the additive terms; (4) ordered-ring
inequalities; (5) casts and normalization. No process law is postulated here.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed

lemma cycle_cutoff (N : ℝ) : cutoff N 2 10 = 242 * Real.log N := by
  norm_num [cutoff, beta]

lemma cycle_cutoff_pos {N : ℝ} (hN : 3 ≤ N) : 0 < 242 * Real.log N := by
  rw [← cycle_cutoff]
  exact cutoff_pos hN (by norm_num) (by norm_num)

lemma cycle_event_horizon (n k : ℕ) (hk : k ≤ (n + 3) ^ 10) :
    (k : ℝ) ≤ (n + 3 : ℝ) ^ (10 : ℝ) := by
  rw [Real.rpow_ofNat]
  exact_mod_cast hk

/-- The numerical estimate absorbs the exceptional contribution of two. -/
lemma cycle_bound_le {N R : ℝ} (hN : 3 ≤ N) (hR : R ≤ N / 4) :
    2 * beta 10 * Real.log N * (2 * Real.sqrt (2 * (4 * 2 + 3) * R) + 4 / 3) + 2 ≤
      300 * Real.sqrt N * Real.log N := by
  have hlog := log_ge_one hN
  have hsqrt : 1 ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hroot : Real.sqrt (2 * (4 * 2 + 3) * R) ≤ (5 / 2) * Real.sqrt N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (show 0 ≤ N by linarith)]
  have hlog₀ : 0 ≤ Real.log N := by linarith
  have hprod : 1 ≤ Real.sqrt N * Real.log N := by nlinarith
  have hrootMul := mul_le_mul_of_nonneg_left hroot hlog₀
  have hlogMul := mul_le_mul_of_nonneg_right hsqrt hlog₀
  norm_num [beta] at *
  nlinarith

/-- Physical mean at most the fifth power of the cycle size. -/
lemma cycle_poisson_mean_le {N t : ℝ} (hN : 0 ≤ N) (ht : t ≤ N ^ 4) :
    N * t ≤ N ^ 5 := by
  calc
    N * t ≤ N * N ^ 4 := mul_le_mul_of_nonneg_left ht hN
    _ = N ^ 5 := by ring

/-- The second moment beyond the event horizon costs at most two. -/
lemma cycle_poisson_remainder_le_two {N μ : ℝ} (hN : 3 ≤ N) (hμ : 0 ≤ μ)
    (hμN : μ ≤ N ^ 5) : (μ ^ 2 + μ) / N ^ 10 ≤ 2 := by
  have hN₀ : 0 < N := by linarith
  have hpow : 1 ≤ N ^ 5 := one_le_pow₀ (by linarith : 1 ≤ N)
  have hsq : μ ^ 2 ≤ (N ^ 5) ^ 2 := pow_le_pow_left₀ hμ hμN 2
  rw [div_le_iff₀ (by positivity : 0 < N ^ 10)]
  have hp : (N ^ 5) ^ 2 = N ^ 10 := by ring
  nlinarith [sq_nonneg (N ^ 5 - 1)]

end GraphicalAllocation.Smoothed
