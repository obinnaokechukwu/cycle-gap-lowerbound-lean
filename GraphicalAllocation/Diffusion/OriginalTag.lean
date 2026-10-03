import GraphicalAllocation.Process.OriginalTag
import GraphicalAllocation.Diffusion.EmbeddingTail

/-!
# Displacement under the original synchronous tag law

These are probability-integral versions of the cycle and Hilbert displacement
bounds. The initial tag is sampled with the actual allocation rates, and every
subsequent tagged transition is the original independent uniform-mark update.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open Rules Process Palm Transport Geometry SimpleGraph MeasureTheory
open scoped BigOperators NNReal

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Expected endpoint observable of the original source-Palm tag process. -/
def originalTagObservable (A : AllocationRule V E) (x : Profile V) (h : ℕ)
    (D : V → V → ℝ) : ℝ :=
  ∑ i, A.kernel.weight x i *
    ∫ y, D i y.2 ∂(A.originalTagKernel.eventLaw h (x, i)).toMeasure

omit [DecidableEq E] in
/-- Equality with the finite exact experiment for every endpoint observable. -/
theorem originalTagObservable_eq_horizon (A : AllocationRule V E)
    (x : Profile V) (h : ℕ) (D : V → V → ℝ) :
    originalTagObservable A x h D =
      ∑ i, A.kernel.weight x i * (A.horizonMarks x h).tagged.iterate h
        (fun y => D i y.2) (x, i) := by
  unfold originalTagObservable
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [A.originalTagKernel.integral_eventLaw h (x, i) (fun y => D i y.2)
    (∑ j, |D i j|) (fun y => Finset.single_le_sum
      (fun j _ => abs_nonneg (D i j)) (Finset.mem_univ y.2)), A.horizonMarks_tagged_eq]

omit [DecidableEq E] in
/-- The tail hypothesis used by transport is the actual original-tag probability. -/
theorem allocationTagTail_eq_originalTagObservable [Nonempty V]
    (A : AllocationRule V E) (h : ℕ) (x : Profile V) (d : V → V → ℝ) (R : ℝ) :
    allocationTagTail A h x d R =
      originalTagObservable A x h (fun i j => if R ≤ d i j then 1 else 0) := by
  rw [originalTagObservable_eq_horizon]
  rfl

/-- T15 at an exact allocation count, as an integral under the original tag law. -/
theorem original_tag_hilbert_displacement_events
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : AllocationRule V E) (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (F : V → H) (η : ℝ) (hedge : ∀ e, ‖F (A.tail e) - F (A.head e)‖ ≤ η)
    (x : Profile V) (h : ℕ) :
    originalTagObservable A x h (fun i j => ‖F j - F i‖ ^ 2) ≤
      2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * h / Fintype.card E + 2 * η ^ 2 := by
  rw [originalTagObservable_eq_horizon]
  exact allocation_hilbert_displacement_events A Δ hΔ F η hedge x h

/-- T15 in physical time, with an independent rate-|E| Poisson event count. -/
theorem original_tag_hilbert_displacement_physical
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : AllocationRule V E) (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (F : V → H) (η : ℝ) (hedge : ∀ e, ‖F (A.tail e) - F (A.head e)‖ ≤ η)
    (x : Profile V) (s : ℝ≥0) :
    (∫ h, originalTagObservable A x h (fun i j => ‖F j - F i‖ ^ 2)
      ∂ProbabilityTheory.poissonMeasure ((Fintype.card E : ℝ≥0) * s)) ≤
      2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * s + 2 * η ^ 2 := by
  simp_rw [originalTagObservable_eq_horizon]
  exact allocation_hilbert_displacement_physical A Δ hΔ F η hedge x s

/-- T06 at every exact allocation count, with the literal original tag law. -/
theorem original_tag_cycle_displacement_events (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (h : ℕ) :
    originalTagObservable A x h (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ) ^ 2) ≤
      2 * Real.pi ^ 2 * h / (n + 3) + 2 := by
  rw [originalTagObservable_eq_horizon]
  exact allocation_cycle_displacement_events n A hA x h

/-- T06 in physical time, including its exact coefficient and additive constant. -/
theorem original_tag_cycle_displacement_physical (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (s : ℝ≥0) :
    (∫ h, originalTagObservable A x h
      (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ) ^ 2)
      ∂ProbabilityTheory.poissonMeasure ((n + 3 : ℝ≥0) * s)) ≤
      2 * Real.pi ^ 2 * s + 2 := by
  simp_rw [originalTagObservable_eq_horizon]
  exact allocation_cycle_displacement_physical n A hA x s

end GraphicalAllocation.Diffusion
