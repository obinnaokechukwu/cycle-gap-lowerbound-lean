import GraphicalAllocation.Applications.Graphs.Setup
import GraphicalAllocation.Applications.Graphs.Substitution
import GraphicalAllocation.Applications.Graphs.Embedding

/-! # Analytic volume and displacement interfaces for actual rectangular tori -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs
open MeasureTheory Set

/-- The continuous volume upper bound after integer-radius rounding. -/
def torusVolume (K κ s : ℝ) : ℝ :=
  25 * (κ * Real.sqrt (s + 1)) * min K (κ * Real.sqrt (s + 1))

lemma torusVolume_pos {K κ s : ℝ} (hK : 0 < K) (hκ : 0 < κ) (hs : 0 ≤ s) :
    0 < torusVolume K κ s := by
  have hr : 0 < κ * Real.sqrt (s + 1) := mul_pos hκ (Real.sqrt_pos.2 (by linarith))
  unfold torusVolume
  exact mul_pos (mul_pos (by norm_num) hr) (lt_min hK hr)

lemma continuous_torusVolume (K κ : ℝ) : Continuous (torusVolume K κ) := by
  unfold torusVolume
  fun_prop

lemma torusVolume_reciprocal_integrable {K κ T : ℝ} (hK : 0 < K) (hκ : 0 < κ)
    (hT : 0 ≤ T) : IntervalIntegrable (fun s => 1 / torusVolume K κ s) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuous_torusVolume K κ).continuousOn
  intro s hs
  rw [uIcc_of_le hT] at hs
  exact ne_of_gt (torusVolume_pos hK hκ hs.1)

/-- The degree-four Hilbert bound lies below 21π²(s+1). -/
lemma torus_diffusion_budget {s : ℝ} (hs : 0 ≤ s) :
    (Real.pi / Real.sqrt 2) ^ 2 * (2 * 1 ^ 2 * (4 : ℝ) * (4 + 1) * s + 2 * 1 ^ 2) ≤
      (21 * Real.pi ^ 2) * (s + 1) := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [sq_nonneg Real.pi]

lemma torus_scale_nonneg {K L : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L) :
    0 ≤ L / K + Real.log K := by
  have hKp : 0 < K := one_pos.trans_le hK
  exact add_nonneg (div_nonneg (hKp.trans_le hKL).le hKp.le) (Real.log_nonneg hK)

end GraphicalAllocation.Applications.Graphs
