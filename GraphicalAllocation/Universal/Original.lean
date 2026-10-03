import GraphicalAllocation.Universal.Laws

/-!
# The original endpoint-local rule is an instance of the universal strategy model

The equality of the finite transition operators is proved by summing over the
edge and endpoint coin. It implies equality of the actual event-count and
Poissonized laws, rather than assuming a bridge between the two models.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace GraphicalAllocation.Universal

open scoped BigOperators NNReal ENNReal
open Process Rules Transport Geometry MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
variable (A : AllocationRule V G.edgeSet)
variable (hA : A.toOrientedGraph = canonicalOrientation G)

/-- Forgetting monotonicity gives an admissible universal endpoint strategy. -/
def allocationStrategy : EndpointStrategy G (Profile V) where
  load := id
  probability := A.edgeProbability
  probability_nonneg := A.edgeProbability_nonneg
  probability_le_one := A.edgeProbability_le_one
  next x c := raise x (if c.2 then A.tail c.1 else A.head c.1)
  next_load x e b := by
    change raise x (if b then A.tail e else A.head e) = _
    rw [show A.tail = (canonicalOrientation G).tail from congrArg OrientedGraph.tail hA,
      show A.head = (canonicalOrientation G).head from congrArg OrientedGraph.head hA]
    rfl

omit [Nonempty V] in
/-- Summing the explicit edge/coin update gives precisely the original rate kernel. -/
theorem allocationStrategy_step (f : Profile V → ℝ) (x : Profile V) :
    (allocationStrategy G A hA).kernel.step f x = A.kernel.step f x := by
  unfold FiniteKernel.step
  simp only [EndpointStrategy.kernel, allocationStrategy, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, AllocationRule.kernel_weight,
    AllocationRule.kernel_next]
  unfold AllocationRule.rate
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [AllocationRule.edgeRate, add_div, add_mul, ite_div, ite_mul,
    Finset.sum_add_distrib]

omit [Nonempty V] in
/-- All finite-time expectations agree for arbitrary tests, with no integrability premise. -/
theorem allocationStrategy_iterate (k : ℕ) (f : Profile V → ℝ) :
    (allocationStrategy G A hA).kernel.iterate k f = A.kernel.iterate k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [FiniteKernel.iterate_succ, FiniteKernel.iterate_succ, ih]
    funext x
    exact allocationStrategy_step G A hA _ x

omit [Nonempty V] in
/-- The strategy instantiation has exactly the original event-count law. -/
theorem allocationStrategy_eventLaw (k : ℕ) (x : Profile V) :
    (allocationStrategy G A hA).kernel.eventLaw k x = A.kernel.eventLaw k x := by
  apply PMF.ext
  intro y
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton]
  change ((allocationStrategy G A hA).kernel.eventLaw k x).toOuterMeasure {z | z = y} =
    (A.kernel.eventLaw k x).toOuterMeasure {z | z = y}
  rw [eventLaw_outerProbability, eventLaw_outerProbability, allocationStrategy_iterate]

omit [Nonempty V] in
/-- Initial mixtures preserve the exact event law. -/
theorem allocationStrategy_eventLawFrom (μ : PMF (Profile V)) (k : ℕ) :
    (allocationStrategy G A hA).kernel.eventLawFrom μ k = A.kernel.eventLawFrom μ k := by
  unfold FiniteKernel.eventLawFrom
  congr 1
  funext x
  exact allocationStrategy_eventLaw G A hA k x

omit [Nonempty V] in
/-- The same equality holds after Poissonization and every initial distribution. -/
theorem allocationStrategy_continuousLawFrom (μ : PMF (Profile V)) (rate t : ℝ≥0) :
    (allocationStrategy G A hA).kernel.continuousLawFrom μ rate t =
      A.kernel.continuousLawFrom μ rate t := by
  unfold FiniteKernel.continuousLawFrom FiniteKernel.continuousLaw
  congr 1
  funext x
  congr 1
  funext k
  exact allocationStrategy_eventLaw G A hA k x

include hA in
/-- The universal logarithmic lower bound for the paper's original actual law. -/
theorem allocation_discrete_probability (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (μ : PMF (Profile V)) (k : ℕ) (hk : logWindow (Fintype.card V) ≤ k) :
    (1 / 2 : ℝ≥0∞) ≤ (A.kernel.eventLawFrom μ k).toMeasure
      {y | Real.log (Fintype.card V) / 64 ≤ gap y} := by
  have h := (allocationStrategy G A hA).discrete_probability Δ hΔ hN hsize μ k hk
  rw [allocationStrategy_eventLawFrom] at h
  simpa only [allocationStrategy, id_eq, PMF.toMeasure_apply_eq_toOuterMeasure] using h

include hA in
/-- Proposition 7.8 in physical time for the actual endpoint-local process. -/
theorem allocation_continuous_probability (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (μ : PMF (Profile V)) (t : ℝ≥0)
    (ht : Real.log (Fintype.card V) / (4 * Δ) ≤ t) :
    (7 / 16 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (Fintype.card G.edgeSet) t).toMeasure
      {y | Real.log (Fintype.card V) / 64 ≤ gap y} := by
  have h := (allocationStrategy G A hA).continuous_probability Δ hΔ hN hsize μ t ht
  rw [allocationStrategy_continuousLawFrom] at h
  simpa only [allocationStrategy, id_eq, PMF.toMeasure_apply_eq_toOuterMeasure] using h

end GraphicalAllocation.Universal
