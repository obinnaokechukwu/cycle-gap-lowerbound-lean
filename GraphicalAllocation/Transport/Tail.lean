import GraphicalAllocation.Transport.Allocation

/-! # Markov bounds for the genuine initialized tag -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

/-- Markov's inequality directly in the actual finite marked expectation. -/
theorem markedTail_mul_sq_le_moment (F : FiniteMarks V C) (h : ℕ) (x : Profile V)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (d : V → V → ℝ) {R : ℝ} (hR : 0 < R) :
    R ^ 2 * markedTail F h x w d R ≤
      ∑ v, w v * F.tagged.iterate h (fun y => d v y.2 ^ 2) (x, v) := by
  have hv : ∀ v, R ^ 2 * F.tagged.iterate h
      (fun y => if R ≤ d v y.2 then 1 else 0) (x, v) ≤
      F.tagged.iterate h (fun y => d v y.2 ^ 2) (x, v) := by
    intro v
    have hp : ∀ y : Profile V × V,
        R ^ 2 * (if R ≤ d v y.2 then 1 else 0) ≤ d v y.2 ^ 2 := by
      intro y
      split_ifs with hd
      · simp only [mul_one]
        nlinarith
      · simp only [mul_zero]
        exact sq_nonneg _
    have he := F.tagged.iterate_mono h hp (x, v)
    simpa only [FiniteKernel.iterate_const_mul] using he
  unfold markedTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv'
  simpa [mul_left_comm] using mul_le_mul_of_nonneg_left (hv v) (hw v)

section Actual
variable {E : Type*} [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Nonempty V] [DecidableEq E] in
/-- Actual allocation tag tail from its actual displacement second moment. -/
theorem allocationTagTail_le_moment_div (A : AllocationRule V E) (h : ℕ) (x : Profile V)
    (d : V → V → ℝ) {R : ℝ} (hR : 0 < R) :
    allocationTagTail A h x d R ≤
      (∑ v, A.kernel.weight x v * (A.horizonMarks x h).tagged.iterate h
        (fun y => d v y.2 ^ 2) (x, v)) / R ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [allocationTagTail, mul_comm] using
    markedTail_mul_sq_le_moment (A.horizonMarks x h) h x (A.kernel.weight x)
      (A.kernel.nonneg x) d hR

end Actual
end GraphicalAllocation.Transport
