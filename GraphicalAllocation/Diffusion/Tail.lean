import GraphicalAllocation.Diffusion.AllocationCycle
import GraphicalAllocation.Transport.Tail

/-! # Actual tag tail bounds, ready for transport inequalities -/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators NNReal
open MeasureTheory Rules Process Transport Geometry SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Nonempty V] [DecidableEq E] in
lemma allocationTagTail_nonneg (A : AllocationRule V E) (h : ℕ) (x : Profile V)
    (d : V → V → ℝ) (R : ℝ) : 0 ≤ allocationTagTail A h x d R := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (A.kernel.nonneg x v)
    ((A.horizonMarks x h).tagged.iterate_nonneg h (fun y => by split_ifs <;> norm_num) (x, v))

omit [Nonempty V] in
/-- Markov's event-time tail bound for the actual Hilbert tag moment. -/
theorem allocation_hilbert_tail_events {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : AllocationRule V E) (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (h : ℕ) {R : ℝ} (hR : 0 < R) :
    allocationTagTail A h x (fun i j => ‖f j - f i‖) R ≤
      (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * h / Fintype.card E + 2 * η ^ 2) / R ^ 2 := by
  exact (allocationTagTail_le_moment_div A h x _ hR).trans
    (div_le_div_of_nonneg_right (allocation_hilbert_displacement_events A Δ hΔ f η hedge x h) (sq_nonneg R))

/-- A literal Poisson-mixture tail obtains the same physical-time Markov bound.
This helper also supplies integrability, so no totalized-integral gap is hidden. -/
theorem poisson_tail_from_moment (m : ℕ) (hm : 0 < m) (s : ℝ≥0)
    (tail moment : ℕ → ℝ) (a b : ℝ) {R : ℝ} (hR : 0 < R)
    (ht0 : ∀ h, 0 ≤ tail h) (ht : ∀ h, R ^ 2 * tail h ≤ moment h)
    (hb : ∀ h, moment h ≤ a * h / m + b) :
    (∫ h, tail h ∂ProbabilityTheory.poissonMeasure ((m : ℝ≥0) * s)) ≤
      (a * s + b) / R ^ 2 := by
  have he := poisson_event_to_physical m hm s (fun h => R ^ 2 * tail h) a b
    (fun h => mul_nonneg (sq_nonneg R) (ht0 h)) (fun h => (ht h).trans (hb h))
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  rw [integral_const_mul] at he
  simpa only [mul_comm] using he.2

omit [Nonempty V] in
/-- Physical-time Hilbert tail bound at rate m, with literal source-Palm tags. -/
theorem allocation_hilbert_tail_physical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : AllocationRule V E) (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (s : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    (∫ h, allocationTagTail A h x (fun i j => ‖f j - f i‖) R
      ∂ProbabilityTheory.poissonMeasure ((Fintype.card E : ℝ≥0) * s)) ≤
      (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * s + 2 * η ^ 2) / R ^ 2 := by
  apply poisson_tail_from_moment (Fintype.card E) Fintype.card_pos s
    (fun h => allocationTagTail A h x (fun i j => ‖f j - f i‖) R)
    (fun h => allocationHilbertMoment A x h f)
    (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1)) (2 * η ^ 2) hR
    (fun h => allocationTagTail_nonneg A h x _ R) _
    (fun h => allocation_hilbert_displacement_events A Δ hΔ f η hedge x h)
  intro h
  exact markedTail_mul_sq_le_moment (A.horizonMarks x h) h x (A.kernel.weight x)
    (A.kernel.nonneg x) _ hR

/-- The cycle tail envelope used in all cycle transport applications. -/
theorem allocation_cycle_tail_events (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (h : ℕ) {R : ℝ} (hR : 0 < R) :
    allocationTagTail A h x (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ)) R ≤
      (2 * Real.pi ^ 2 * h / (n + 3) + 2) / R ^ 2 := by
  exact (allocationTagTail_le_moment_div A h x _ hR).trans
    (div_le_div_of_nonneg_right (allocation_cycle_displacement_events n A hA x h) (sq_nonneg R))

/-- The physical-time cycle tail envelope, with the exact rate-N clock count. -/
theorem allocation_cycle_tail_physical (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (x : Profile (Fin (n + 3))) (s : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    (∫ h, allocationTagTail A h x (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ)) R
      ∂ProbabilityTheory.poissonMeasure ((n + 3 : ℝ≥0) * s)) ≤
      (2 * Real.pi ^ 2 * s + 2) / R ^ 2 := by
  have he := poisson_tail_from_moment (n + 3) (by omega) s
    (fun h => allocationTagTail A h x (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ)) R)
    (allocationCycleMoment n A x) (2 * Real.pi ^ 2) 2 hR
    (fun h => allocationTagTail_nonneg A h x _ R)
    (fun h => markedTail_mul_sq_le_moment (A.horizonMarks x h) h x
      (A.kernel.weight x) (A.kernel.nonneg x) _ hR)
    (by intro h; simpa only [Nat.cast_add, Nat.cast_ofNat] using allocation_cycle_displacement_events n A hA x h)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using he

end GraphicalAllocation.Diffusion
