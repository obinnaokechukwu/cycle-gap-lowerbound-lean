import GraphicalAllocation.Projections.CellBridge

/-!
# Conditional variance and support-localized projection energy

These estimates supply the exact radius-squared constant in Section 7.
Cell averages are explicit finite weighted averages, and inactive local cells
are singletons, so their energy is zero.
-/

noncomputable section

open scoped BigOperators Matrix

namespace GraphicalAllocation.Projections

variable {A B E : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq A] in
/-- Expansion around an arbitrary center of a normalized weighted measure. -/
theorem weighted_distance_identity (w : A → ℝ) (hw : ∑ a, w a = 1)
    (f : A → E) (c : E) :
    (∑ a, w a * ‖f a - c‖ ^ 2) =
      (∑ a, w a * ‖f a‖ ^ 2) -
      2 * inner ℝ (∑ a, w a • f a) c + ‖c‖ ^ 2 := by
  have hc : (∑ a, w a * (2 * inner ℝ (f a) c)) =
      2 * inner ℝ (∑ a, w a • f a) c := by
    simp only [sum_inner, real_inner_smul_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hc, ← Finset.sum_mul, hw, one_mul]

omit [DecidableEq A] in
/-- The weighted barycenter minimizes the mean squared distance. -/
theorem weighted_variance_le_center (w : A → ℝ) (hw : ∑ a, w a = 1)
    (f : A → E) (c : E) :
    (∑ a, w a * ‖f a - ∑ b, w b • f b‖ ^ 2) ≤
      ∑ a, w a * ‖f a - c‖ ^ 2 := by
  rw [weighted_distance_identity w hw f _, weighted_distance_identity w hw f c,
    real_inner_self_eq_norm_sq]
  have h := norm_sub_sq_real (∑ a, w a • f a) c
  have hn := sq_nonneg ‖(∑ a, w a • f a) - c‖
  linarith

omit [DecidableEq A] in
/-- A conditional selection cell lying in a radius-`r` ball has variance at
most `r²`; this is the exact constant used by Lemma 7.1. -/
theorem cell_variance_le_radius {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (f : A → E) (a : A) (c : E) (r : ℝ)
    (hball : ∀ b, p b = p a → ‖f b - c‖ ≤ r) :
    (∑ b, Palm.cellKernel μ p a b *
      ‖f b - vectorAverage (Palm.cellKernel μ p) f a‖ ^ 2) ≤ r ^ 2 := by
  have hcenter := weighted_variance_le_center (Palm.cellKernel μ p a)
    (Palm.cellKernel_row_sum hμ p a) f c
  apply hcenter.trans
  calc
    (∑ b, Palm.cellKernel μ p a b * ‖f b - c‖ ^ 2) ≤
        ∑ b, Palm.cellKernel μ p a b * r ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : p b = p a
      · have hr := hball b hb
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hr)).2 hr)
          (Palm.cellKernel_nonneg (fun a => (hμ a).le) p a b)
      · simp [Palm.cellKernel, hb]
    _ = r ^ 2 := by rw [← Finset.sum_mul, Palm.cellKernel_row_sum hμ, one_mul]

omit [DecidableEq A] in
/-- A cell's vector average is constant on that cell. -/
theorem vectorAverage_same_cell (μ : A → ℝ) (p : A → B) (f : A → E)
    {a b : A} (hab : p a = p b) :
    vectorAverage (Palm.cellKernel μ p) f a = vectorAverage (Palm.cellKernel μ p) f b := by
  unfold vectorAverage
  simp_rw [Palm.cellKernel_same_cell μ p hab]

omit [DecidableEq A] in
/-- Global projection energy is the weighted average of within-cell variances. -/
theorem cell_residual_eq_average_variance {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (f : A → E) :
    (∑ b, μ b * ‖f b - vectorAverage (Palm.cellKernel μ p) f b‖ ^ 2) =
      ∑ a, μ a * ∑ b, Palm.cellKernel μ p a b *
        ‖f b - vectorAverage (Palm.cellKernel μ p) f a‖ ^ 2 := by
  symm
  calc
    _ = ∑ a, ∑ b, μ a * Palm.cellKernel μ p a b *
        ‖f b - vectorAverage (Palm.cellKernel μ p) f b‖ ^ 2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : p a = p b
      · rw [vectorAverage_same_cell μ p f hb]
        ring
      · have hb' := Ne.symm hb
        simp [Palm.cellKernel, hb']
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, Palm.cellKernel_stationary hμ]

/-- Only marks in active selection cells contribute. Inactive cells are exact
singletons, while each active cell contributes at most its mass times `r²`. -/
theorem local_projection_energy_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (S : Finset B) (f : A → E) (c : B → E) (r : ℝ)
    (hball : ∀ a, p a ∈ S → ‖f a - c (p a)‖ ≤ r) :
    (∑ a, μ a * ‖f a - vectorAverage (Palm.cellKernel μ (Palm.localKey p S)) f a‖ ^ 2) ≤
      (∑ a, if p a ∈ S then μ a else 0) * r ^ 2 := by
  rw [cell_residual_eq_average_variance hμ]
  calc
    _ ≤ ∑ a, μ a * (if p a ∈ S then r ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hμ a).le
      by_cases ha : p a ∈ S
      · simp only [ha, ↓reduceIte]
        simp only [vectorAverage, Palm.cellKernel_localKey_active μ p S ha]
        exact cell_variance_le_radius hμ p f a (c (p a)) r (fun b hb => by
          simpa [hb] using hball b (hb ▸ ha))
      · simp [vectorAverage, Palm.cellKernel_localKey_inactive hμ p S ha, ha]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring

/-- Local cell resampling has diffusive Hilbert displacement when the affected
mass and cell radii have uniform bounds. -/
theorem local_chain_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → B) (S : ℕ → Finset B) (f : A → E)
    (c : ℕ → B → E) (r M : ℝ)
    (hball : ∀ j a, p j a ∈ S j → ‖f a - c j (p j a)‖ ≤ r)
    (hmass : ∀ j, (∑ a, if p j a ∈ S j then μ a else 0) ≤ M) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ
      (fun j => Palm.cellKernel μ (Palm.localKey (p j) (S j))) n a b *
      ‖f b - f a‖ ^ 2) ≤ 4 * (n : ℝ) * M * r ^ 2 := by
  have hc := cell_hilbert_chain_displacement_le hμ
    (fun j => Palm.localKey (p j) (S j)) f n
  apply hc.trans
  calc
    _ ≤ 4 * ∑ j ∈ Finset.range n, M * r ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j _
      exact (local_projection_energy_le hμ (p j) (S j) f (c j) r (hball j)).trans
        (mul_le_mul_of_nonneg_right (hmass j) (sq_nonneg r))
    _ = _ := by simp; ring

end GraphicalAllocation.Projections
