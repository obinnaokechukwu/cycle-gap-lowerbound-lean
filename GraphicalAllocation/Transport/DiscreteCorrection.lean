import GraphicalAllocation.Transport.Counting
import GraphicalAllocation.Process.Allocation
import GraphicalAllocation.Process.DiscreteVariance

/-!
# The repaired discrete variance-correction lemma

Both statements below concern the actual endpoint-local allocation kernel. The
mean-increment bound is first proved at lag zero and then transported by the
Markov operator's commutation identity. Thus this proof does not require a Palm
intertwining theorem. Positivity of `M` is explicit, as required by erratum E1.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E]
variable (A : AllocationRule V E)

/-- The paper's unnormalized carré-du-champ response energy. -/
def rateEnergy (f : Profile V → ℝ) (x : Profile V) : ℝ :=
  ∑ v, A.rate x v * finiteDifference f x v ^ 2

theorem kernel_responseEnergy_eq (f : Profile V → ℝ) (x : Profile V) :
    A.kernel.responseEnergy f x = rateEnergy A f x / Fintype.card E := by
  simp [FiniteKernel.responseEnergy, rateEnergy, finiteDifference, Finset.sum_div,
    div_mul_eq_mul_div]

/-- Equation (6.3) for the actual graph allocation kernel, for any test. -/
theorem discrete_variance_correction (h : ℕ) (f : Profile V → ℝ) (x : Profile V) :
    A.kernel.step (fun y => A.kernel.iterate h f y ^ 2) x -
      A.kernel.iterate (h + 1) f x ^ 2 =
    rateEnergy A (A.kernel.iterate h f) x / Fintype.card E -
      (A.kernel.step (A.kernel.iterate h f) x - A.kernel.iterate h f x) ^ 2 := by
  rw [← kernel_responseEnergy_eq]
  exact A.kernel.variance_eq_responseEnergy (A.kernel.iterate h f) x

/-- Direct generator identity from the derived next-allocation rate distribution. -/
theorem kernel_increment_eq (f : Profile V → ℝ) (x : Profile V) :
    A.kernel.step f x - f x =
      (∑ v, A.rate x v * finiteDifference f x v) / Fintype.card E := by
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
  simp only [finiteDifference, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    A.sum_rate, sub_div]
  simp [FiniteKernel.step, Finset.sum_div, div_mul_eq_mul_div, hm]

/-- Lag-zero estimate, using only the two endpoint rates. -/
theorem clipped_mean_increment (i j : V) (hij : i ≠ j) {M Δ : ℝ}
    (hM : 0 < M) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (x : Profile V) :
    |A.kernel.step (clippedContrast i j M) x - clippedContrast i j M x| ≤
      2 * Δ / ((Fintype.card E : ℝ) * M) := by
  have hm : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  rw [kernel_increment_eq, abs_div, abs_of_pos hm]
  have h := weighted_clipped_increment_abs_le i j hij hM x (A.rate x)
    (A.rate_nonneg x) (fun v => (A.rate_le_degree x v).trans (hΔ v))
  calc
    _ ≤ (2 * Δ / M) / Fintype.card E := div_le_div_of_nonneg_right h hm.le
    _ = 2 * Δ / ((Fintype.card E : ℝ) * M) := by ring

/-- Equation (6.4), at every exact event lag. The hypothesis `M > 0` repairs
its omission from the source statement. -/
theorem clipped_iterate_mean_increment (i j : V) (hij : i ≠ j) {M Δ : ℝ}
    (hM : 0 < M) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (h : ℕ) (x : Profile V) :
    |A.kernel.step (A.kernel.iterate h (clippedContrast i j M)) x -
      A.kernel.iterate h (clippedContrast i j M) x| ≤
      2 * Δ / ((Fintype.card E : ℝ) * M) := by
  exact A.kernel.iterate_increment_bounded h (clippedContrast i j M)
    (2 * Δ / ((Fintype.card E : ℝ) * M))
    (clipped_mean_increment A i j hij hM hΔ) x

end GraphicalAllocation.Transport
