import GraphicalAllocation.Process.Allocation
import GraphicalAllocation.Transport.Clipped

/-!
# A one-step obstruction to flatness

Two distinct one-ball placements cannot both produce flat profiles. Combined
with the degree bound on allocation rates, this proves the event-count phase
fallback used on cycles, directly from the actual allocation kernel.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators
open Rules Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A state has at most one flat one-step successor. -/
theorem flat_successor_unique (x : Profile V) (u v : V)
    (hu : gap (raise x u) = 0) (hv : gap (raise x v) = 0) : u = v := by
  by_contra hne
  have hu' := (gap_eq_zero_iff _).mp hu u v
  have hv' := (gap_eq_zero_iff _).mp hv u v
  simp [raise, hne, Ne.symm hne] at hu' hv'
  omega

/-- Indicator of nonflatness; integer loads make its threshold exactly one. -/
noncomputable def nonflatIndicator (x : Profile V) : ℝ := if 1 ≤ gap x then 1 else 0

omit [DecidableEq V] in
lemma nonflatIndicator_eq_one_sub_flat (x : Profile V) :
    nonflatIndicator x = 1 - (if gap x = 0 then 1 else 0) := by
  rcases gap_zero_or_one_le x with hz | ho
  · simp [nonflatIndicator, hz]
  · have hz : gap x ≠ 0 := by linarith
    simp [nonflatIndicator, ho, hz]

omit [DecidableEq V] in
lemma nonflatIndicator_bounds (x : Profile V) :
    0 ≤ nonflatIndicator x ∧ nonflatIndicator x ≤ 1 := by
  unfold nonflatIndicator
  split_ifs <;> norm_num

namespace AllocationRule

variable [Fintype E] [Nonempty E] (A : AllocationRule V E)

/-- A probability of a flat one-step successor can be no larger than a single
vertex's allocation probability. -/
theorem step_flatIndicator_le (Δ : ℝ) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (x : Profile V) :
    A.kernel.step (fun y => if gap y = 0 then 1 else 0) x ≤ Δ / Fintype.card E := by
  classical
  have hΔnonneg : 0 ≤ Δ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact (Nat.cast_nonneg (A.degree v)).trans (hΔ v)
  by_cases h : ∃ v, gap (raise x v) = 0
  · obtain ⟨v, hv⟩ := h
    have hs : A.kernel.step (fun y => if gap y = 0 then 1 else 0) x =
        A.rate x v / Fintype.card E := by
      unfold FiniteKernel.step
      rw [Finset.sum_eq_single v]
      · simp [hv]
      · intro w _ hw
        have hn : gap (raise x w) ≠ 0 := fun hh => hw (flat_successor_unique x w v hh hv)
        simp [hn]
      · simp
    rw [hs]
    exact div_le_div_of_nonneg_right ((A.rate_le_degree x v).trans (hΔ v))
      (Nat.cast_nonneg _)
  · have hn : ∀ v, gap (raise x v) ≠ 0 := by simpa using h
    simp only [FiniteKernel.step, kernel_next, hn, ite_false, mul_zero, Finset.sum_const_zero]
    exact div_nonneg hΔnonneg (Nat.cast_nonneg _)

/-- Uniform one-step nonflatness from the actual endpoint-rate bound. -/
theorem step_nonflatIndicator_ge (Δ : ℝ) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (x : Profile V) :
    1 - Δ / Fintype.card E ≤ A.kernel.step nonflatIndicator x := by
  have hid : nonflatIndicator (V := V) =
      (fun _ => (1 : ℝ)) - (fun y => if gap y = 0 then 1 else 0) := by
    funext y
    exact nonflatIndicator_eq_one_sub_flat y
  rw [hid, A.kernel.step_sub, A.kernel.step_const]
  have hb := A.step_flatIndicator_le Δ hΔ x
  simp only [Pi.sub_apply]
  linarith

/-- The fallback persists after every positive number of allocations. -/
theorem iterate_nonflatIndicator_ge (Δ : ℝ) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (k : ℕ) (x : Profile V) :
    1 - Δ / Fintype.card E ≤ A.kernel.iterate (k + 1) nonflatIndicator x := by
  have h := A.kernel.iterate_mono k (A.step_nonflatIndicator_ge Δ hΔ) x
  simpa only [A.kernel.iterate_const, A.kernel.iterate_step, FiniteKernel.iterate_succ] using h

end AllocationRule
end GraphicalAllocation.Process
