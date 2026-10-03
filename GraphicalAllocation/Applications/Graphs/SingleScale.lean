import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # The general embedding horizon and single-scale constants -/

noncomputable section
namespace GraphicalAllocation.Applications.Graphs

/-- The positive-distortion hypothesis is essential for this horizon. -/
def embeddingHorizon (D δ R : ℝ) : ℝ := R ^ 2 / (64 * D ^ 2 * δ)

lemma embeddingHorizon_pos {D δ R : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hR : 0 < R) :
    0 < embeddingHorizon D δ R := by unfold embeddingHorizon; positivity

/-- At the selected horizon the displacement envelope is uniformly at most 1/16. -/
theorem embedding_horizon_tail {D δ R s : ℝ} (hD : 0 < D) (hδ : 0 < δ)
    (hR : 8 * D ≤ R) (hs : s ≤ embeddingHorizon D δ R) :
    D ^ 2 * (2 * δ * s + 2) / R ^ 2 ≤ 1 / 16 := by
  have hRp : 0 < R := by linarith
  have hs' : s * (64 * D ^ 2 * δ) ≤ R ^ 2 :=
    (le_div_iff₀ (by positivity)).mp hs
  apply (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
  have hRsq : (8 * D) ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (by positivity) hRp.le).mpr hR
  nlinarith

/-- Literal square-root simplification giving equation (7.4). -/
theorem embedding_scale_identity {D δ R m N B : ℝ} (hD : 0 < D) (hδ : 0 < δ)
    (hR : 0 ≤ R) (hm : 0 ≤ m) (hN : 0 < N) (hB : 0 < B) :
    Real.sqrt (m / N * embeddingHorizon D δ R / (4 * B)) / 16 =
      R / (256 * D * Real.sqrt δ) * Real.sqrt (m / (N * B)) := by
  have h₁ : 0 ≤ m / N * embeddingHorizon D δ R / (4 * B) := by
    unfold embeddingHorizon
    positivity
  have h₂ : 0 ≤ m / (N * B) := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt h₁, mul_pow, div_pow, mul_pow, mul_pow,
    Real.sq_sqrt hδ.le, Real.sq_sqrt h₂]
  unfold embeddingHorizon
  field_simp
  ring

end GraphicalAllocation.Applications.Graphs
