import GraphicalAllocation.Projections.HilbertChain
import GraphicalAllocation.Palm.FiniteKernel

/-!
# Actual cell-resampling chains satisfy the projection bound

This instantiates the Hilbert-space result with the cell kernel constructed
from atom weights and partitions. Reversibility and idempotence are proved by
the finite Palm kernel module, rather than assumed as conclusions.
-/

noncomputable section

open scoped BigOperators Matrix

namespace GraphicalAllocation.Projections

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

/-- Equation (4.2) for the explicitly constructed finite selection-cell chain. -/
theorem cell_chain_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → B) (f : A → ℝ) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ (fun j => Palm.cellKernel μ (p j)) n a b *
      (f b - f a) ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a * (f a - Palm.cellAverage μ (p j) f a) ^ 2 := by
  exact stationary_chain_displacement_le hμ (fun j => Palm.cellKernel μ (p j))
    (fun j => Palm.cellKernel_row_sum hμ (p j))
    (fun j => Palm.cellKernel_detailed_balance μ (p j))
    (fun j => Matrix.ext fun a b => Palm.cellKernel_idempotent hμ (p j) a b) f n

/-- Normalized positive atom weights and cell resampling give a genuine
nonnegative, total-mass-one endpoint joint distribution. -/
theorem cell_endpointJoint_probability {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (hmass : ∑ a, μ a = 1) (p : ℕ → A → B) (n : ℕ) :
    (∀ a b, 0 ≤ endpointJoint μ (fun j => Palm.cellKernel μ (p j)) n a b) ∧
    (∑ a, ∑ b, endpointJoint μ (fun j => Palm.cellKernel μ (p j)) n a b) = 1 := by
  constructor
  · intro a b
    exact mul_nonneg (hμ a).le (forwardProduct_nonneg _
      (fun j => Palm.cellKernel_nonneg (fun a => (hμ a).le) (p j)) n a b)
  · simp only [endpointJoint, ← Finset.mul_sum,
      forwardProduct_row_sum _ (fun j => Palm.cellKernel_row_sum hμ (p j)), mul_one]
    exact hmass

/-- The Hilbert-valued statement for actual selection-cell resampling, with no
finite-dimensionality requirement on the target. Complex Hilbert spaces carry
the canonical underlying real inner-product-space instance as well. -/
theorem cell_hilbert_chain_displacement_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → B) (f : A → E) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ (fun j => Palm.cellKernel μ (p j)) n a b *
      ‖f b - f a‖ ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a *
        ‖f a - vectorAverage (Palm.cellKernel μ (p j)) f a‖ ^ 2 := by
  exact hilbert_chain_displacement_le hμ (fun j => Palm.cellKernel μ (p j))
    (fun j => Palm.cellKernel_row_sum hμ (p j))
    (fun j => Palm.cellKernel_detailed_balance μ (p j))
    (fun j => Matrix.ext fun a b => Palm.cellKernel_idempotent hμ (p j) a b) f n

end GraphicalAllocation.Projections
