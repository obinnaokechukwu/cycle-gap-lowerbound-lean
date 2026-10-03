import GraphicalAllocation.Projections.CellVariance

/-!
# Endpoint displacement from localized projection chains

This is the finite-event Hilbert-displacement estimate underlying Section 7.
The only geometric inputs are the cell radius, the affected mass, and the
endpoint-to-mark errors, all stated explicitly.
-/

noncomputable section

open scoped BigOperators

namespace GraphicalAllocation.Projections

variable {A B E : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq A] [InnerProductSpace ℝ E] in
/-- Integrate the endpoint-to-midpoint error against a genuine finite joint law. -/
theorem weighted_endpoint_midpoint_le (w : A → A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hmass : ∑ a, ∑ b, w a b = 1)
    (u v f : A → E) (η : ℝ)
    (hu : ∀ a, ‖u a - f a‖ ≤ η / 2) (hv : ∀ b, ‖v b - f b‖ ≤ η / 2) :
    (∑ a, ∑ b, w a b * ‖v b - u a‖ ^ 2) ≤
      2 * (∑ a, ∑ b, w a b * ‖f b - f a‖ ^ 2) + 2 * η ^ 2 := by
  calc
    _ ≤ ∑ a, ∑ b, w a b * (2 * ‖f b - f a‖ ^ 2 + 2 * η ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (endpoint_midpoint_square_le (v b) (u a) (f b) (f a) η (hv b) (hu a)) (hw a b)
    _ = (∑ a, ∑ b, (2 * (w a b * ‖f b - f a‖ ^ 2) + w a b * (2 * η ^ 2))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 2 * (∑ a, ∑ b, w a b * ‖f b - f a‖ ^ 2) +
        (∑ a, ∑ b, w a b) * (2 * η ^ 2) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by rw [hmass, one_mul]

/-- Finite-event version of Lemma 7.1 from explicitly localized cell kernels.
Taking `M = Δ(Δ+1)/m` gives its stated constant after `n` events. -/
theorem local_endpoint_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (hμmass : ∑ a, μ a = 1) (p : ℕ → A → B) (S : ℕ → Finset B)
    (f u v : A → E) (c : ℕ → B → E) (η M : ℝ)
    (hball : ∀ j a, p j a ∈ S j → ‖f a - c j (p j a)‖ ≤ η / 2)
    (hmass : ∀ j, (∑ a, if p j a ∈ S j then μ a else 0) ≤ M)
    (hu : ∀ a, ‖u a - f a‖ ≤ η / 2) (hv : ∀ b, ‖v b - f b‖ ≤ η / 2)
    (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ
      (fun j => Palm.cellKernel μ (Palm.localKey (p j) (S j))) n a b *
      ‖v b - u a‖ ^ 2) ≤ 2 * η ^ 2 * M * (n : ℝ) + 2 * η ^ 2 := by
  have hprob := cell_endpointJoint_probability hμ hμmass
    (fun j => Palm.localKey (p j) (S j)) n
  have he := weighted_endpoint_midpoint_le _ hprob.1 hprob.2 u v f η hu hv
  have hd := local_chain_displacement_le hμ p S f c (η / 2) M hball hmass n
  calc
    _ ≤ 2 * (∑ a, ∑ b, endpointJoint μ
        (fun j => Palm.cellKernel μ (Palm.localKey (p j) (S j))) n a b *
        ‖f b - f a‖ ^ 2) + 2 * η ^ 2 := he
    _ ≤ 2 * (4 * (n : ℝ) * M * (η / 2) ^ 2) + 2 * η ^ 2 := by linarith
    _ = _ := by ring

end GraphicalAllocation.Projections
