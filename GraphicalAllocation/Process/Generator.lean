import GraphicalAllocation.Process.Allocation
import GraphicalAllocation.Process.Continuous.Kernel

/-!
# The rate-one-per-edge generator

The Poissonized transition law has exactly the sum of the individual edge
allocation generators. This identifies its physical-time normalization directly
without depending on a separate realization of clock sample paths.
-/

namespace GraphicalAllocation.Process.AllocationRule
open Rules
open scoped BigOperators BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E]
variable (A : AllocationRule V E)

/-- Rate times the one-event mean increment equals the allocation-rate generator. -/
theorem allocation_generator_identity (f : Profile V → ℝ) (x : Profile V) :
    (Fintype.card E : ℝ) * (A.kernel.step f x - f x) =
      ∑ v, A.rate x v * (f (raise x v) - f x) := by
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
  have he : A.kernel.step f x = (∑ v, A.rate x v * f (raise x v)) / Fintype.card E := by
    simp only [FiniteKernel.step, kernel_weight, kernel_next, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, A.sum_rate]
  field_simp

/-- The same generator is the sum of rate-one oriented-edge contributions. -/
theorem allocation_generator_by_edges (f : Profile V → ℝ) (x : Profile V) :
    (Fintype.card E : ℝ) * (A.kernel.step f x - f x) =
      ∑ e, (A.edgeProbability x e * (f (raise x (A.tail e)) - f x) +
        (1 - A.edgeProbability x e) * (f (raise x (A.head e)) - f x)) := by
  rw [A.allocation_generator_identity]
  unfold rate
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [edgeRate, add_mul, ite_mul, Finset.sum_add_distrib]

variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]

/-- The analytic generator has the paper's literal vertex-rate formula. -/
theorem generator_eq_rate_sum (f : Profile V →ᵇ ℝ) (x : Profile V) :
    A.kernel.generator (Fintype.card E) f x =
      ∑ v, A.rate x v * (f (raise x v) - f x) :=
  A.allocation_generator_identity f x

end GraphicalAllocation.Process.AllocationRule
