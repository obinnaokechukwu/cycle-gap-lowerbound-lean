import GraphicalAllocation.Diffusion.Tail

/-! # Actual embedding-distance tail bounds

These estimates transfer the proved Hilbert diffusion bound to any dominated
pseudometric, with no connectedness assumption or moment assumption on loads.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators NNReal
open MeasureTheory Rules Process Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Nonempty V] [DecidableEq E] in
lemma allocationTagTail_le_one (A : AllocationRule V E) (h : ℕ) (x : Profile V)
    (d : V → V → ℝ) (R : ℝ) : allocationTagTail A h x d R ≤ 1 := by
  unfold allocationTagTail markedTail
  calc
    _ ≤ ∑ v, A.kernel.weight x v * (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (A.kernel.nonneg x v)
      have he := (A.horizonMarks x h).tagged.iterate_mono h
        (fun y : Profile V × V => show (if R ≤ d v y.2 then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num) (x, v)
      simpa only [FiniteKernel.iterate_const] using he
    _ = 1 := by simpa using A.kernel.total x

omit [Nonempty V] [DecidableEq E] in
lemma allocationTagTail_integrable (A : AllocationRule V E) (x : Profile V)
    (d : V → V → ℝ) (R : ℝ) (r : ℝ≥0) :
    Integrable (fun h => allocationTagTail A h x d R) (ProbabilityTheory.poissonMeasure r) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [] with h
  rw [Real.norm_eq_abs, abs_of_nonneg (allocationTagTail_nonneg A h x d R)]
  exact allocationTagTail_le_one A h x d R

omit [Nonempty V] [DecidableEq E] in
lemma allocationTagTail_event_inclusion (A : AllocationRule V E) (h : ℕ) (x : Profile V)
    (d d' : V → V → ℝ) (R R' : ℝ) (hinc : ∀ i j, R ≤ d i j → R' ≤ d' i j) :
    allocationTagTail A h x d R ≤ allocationTagTail A h x d' R' := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (A.kernel.nonneg x i)
  apply (A.horizonMarks x h).tagged.iterate_mono
  intro y
  by_cases hd : R ≤ d i y.2
  · simp [hd, hinc i y.2 hd]
  · simp only [hd, ite_false]
    split_ifs <;> norm_num

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] [Nonempty V] [DecidableEq E] in
lemma allocationTagTail_le_embedding (A : AllocationRule V E) (h : ℕ) (x : Profile V)
    (d : V → V → ℝ) (f : V → H) {D : ℝ} (hD : 0 < D)
    (hd : ∀ i j, d i j ≤ D * ‖f j - f i‖) (R : ℝ) :
    allocationTagTail A h x d R ≤ allocationTagTail A h x (fun i j => ‖f j - f i‖) (R / D) := by
  apply allocationTagTail_event_inclusion
  intro i j hR
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using hR.trans (hd i j)

omit [Nonempty V] in
/-- Exact-event embedding tail with the constants used in Section 7. -/
theorem allocation_embedding_tail_events (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ) (f : V → H) (η : ℝ)
    (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (d : V → V → ℝ) {D : ℝ} (hD : 0 < D) (hd : ∀ i j, d i j ≤ D * ‖f j - f i‖)
    (x : Profile V) (h : ℕ) {R : ℝ} (hR : 0 < R) :
    allocationTagTail A h x d R ≤ D ^ 2 *
      (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * h / Fintype.card E + 2 * η ^ 2) / R ^ 2 := by
  have he := (allocationTagTail_le_embedding A h x d f hD hd R).trans
    (allocation_hilbert_tail_events A Δ hΔ f η hedge x h (div_pos hR hD))
  convert he using 1
  field_simp

omit [Nonempty V] in
/-- Physical-time embedding tail from the actual source-Palm tag law. -/
theorem allocation_embedding_tail_physical (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ) (f : V → H) (η : ℝ)
    (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (d : V → V → ℝ) {D : ℝ} (hD : 0 < D) (hd : ∀ i j, d i j ≤ D * ‖f j - f i‖)
    (x : Profile V) (s : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    (∫ h, allocationTagTail A h x d R
      ∂ProbabilityTheory.poissonMeasure ((Fintype.card E : ℝ≥0) * s)) ≤
      D ^ 2 * (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * s + 2 * η ^ 2) / R ^ 2 := by
  have he := (integral_mono (allocationTagTail_integrable A x d R _)
      (allocationTagTail_integrable A x (fun i j => ‖f j - f i‖) (R / D) _)
      (fun h => allocationTagTail_le_embedding A h x d f hD hd R)).trans
    (allocation_hilbert_tail_physical A Δ hΔ f η hedge x s (div_pos hR hD))
  convert he using 1
  field_simp

end GraphicalAllocation.Diffusion
