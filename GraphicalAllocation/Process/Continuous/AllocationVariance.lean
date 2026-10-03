import GraphicalAllocation.Process.Continuous.ProcessVariance
import GraphicalAllocation.Process.Allocation

/-!
# Finite-horizon variance budget for endpoint-local allocation

This specializes the constructed-law theorem to the actual rule-derived vertex
rates. In particular, the coefficient of each squared response is exactly
`AllocationRule.rate`, with no assumed diffusion or variance bound.
-/

noncomputable section

namespace GraphicalAllocation.Process.AllocationRule

open GraphicalAllocation.Rules MeasureTheory
open scoped BigOperators NNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E]
variable (A : AllocationRule V E)

/-- Cancellation of the total rate against the event-selection normalization. -/
theorem rate_mul_kernel_energy (g : Profile V → ℝ) (x : Profile V) :
    (Fintype.card E : ℝ) * ∑ v, A.kernel.weight x v *
      (g (A.kernel.next x v) - g x) ^ 2 =
    ∑ v, A.rate x v * (g (raise x v) - g x) ^ 2 := by
  have hm : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := E)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [kernel_weight, kernel_next]
  field_simp

variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]

/-- The analytic carré du champ equals the paper's vertex-rate energy. -/
theorem energy_eq_sum_rates (f : Profile V →ᵇ ℝ) (x : Profile V) :
    A.kernel.energy (Fintype.card E) f x =
      ∑ v, A.rate x v * (f (raise x v) - f x) ^ 2 := by
  rw [A.kernel.energy_apply, A.rate_mul_kernel_energy]

variable [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
variable [OpensMeasurableSpace (Profile V)]

/-- Section 5, finite-horizon response energy, for the actual allocation process
from any independent initial law. The theorem is stronger than the source in
not requiring translation invariance of the bounded test. -/
theorem finiteHorizon_response_energy (μ : PMF (Profile V)) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (f : Profile V →ᵇ ℝ) :
    (∫ s in (0 : ℝ)..T, ∫ x,
      ∑ v, A.rate x v *
        (A.kernel.semigroup (Fintype.card E) s f (raise x v) -
          A.kernel.semigroup (Fintype.card E) s f x) ^ 2
      ∂(A.kernel.continuousLawFrom μ (Fintype.card E)
        (Real.toNNReal ((t : ℝ) - s))).toMeasure) ≤
      ProbabilityTheory.variance f
        (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure := by
  have h := A.kernel.finiteHorizon_response_energy μ (Fintype.card E) t hT hTt f
  simpa only [NNReal.coe_natCast, A.rate_mul_kernel_energy] using h

end GraphicalAllocation.Process.AllocationRule
