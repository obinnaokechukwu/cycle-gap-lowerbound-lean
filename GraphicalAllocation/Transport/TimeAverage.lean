import GraphicalAllocation.Transport.Allocation
import GraphicalAllocation.Transport.IterateAverage

/-! # Actual event-time energy averaged over the preceding base trajectory -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable (A : AllocationRule V E)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- Actual bad-gap probabilities obey the semigroup tower identity. -/
theorem iterate_allocationBadGap (n h : ℕ) (M : ℝ) (x : Profile V) :
    A.kernel.iterate n (fun y => allocationBadGap A h y M) x =
      allocationBadGap A (n + h) x M := by
  exact (congrFun (A.kernel.iterate_add_time n h
    (fun y => if gap y ≤ M - 1 then 0 else 1)) x).symm

omit [DecidableEq E] in
/-- The pointwise energy estimate survives averaging over all preceding events.
The gap tail is measured at exactly the unperturbed terminal time `n+h`. -/
theorem averaged_allocation_transport_energy
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (n h : ℕ) (x : Profile V) (hq : ∀ y, allocationTagTail A h y d R ≤ q) :
    max (1 - allocationBadGap A (n + h) x M - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      ∑ i, A.kernel.iterate n
        (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x := by
  let r : Profile V → ℝ := fun y => 1 - allocationBadGap A h y M - 2 * q
  let e : Profile V → ℝ := fun y =>
    ∑ i, A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M)) y
  have he : ∀ y, max (r y) 0 ^ 2 / (M ^ 2 * B) ≤ e y := fun y =>
    allocation_transport_energy A d hdiag hsym htriangle ψ hR hM hB hsep hvolume
      h y le_rfl (hq y)
  have hden : 0 < M ^ 2 * B := mul_pos (sq_pos_of_pos (by linarith)) hB
  have hresult := A.kernel.iterate_energy_lower n r e hden he x
  have hr : A.kernel.iterate n r x = 1 - allocationBadGap A (n + h) x M - 2 * q := by
    change A.kernel.iterate n (((fun _ => 1) - (fun y => allocationBadGap A h y M)) -
      (fun _ => 2 * q)) x = _
    simp only [FiniteKernel.iterate_sub, FiniteKernel.iterate_const, Pi.sub_apply,
      iterate_allocationBadGap]
  have heq : A.kernel.iterate n e x = ∑ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x := by
    have he' : e = ∑ i, A.kernel.responseEnergy
        (A.kernel.iterate h (clippedContrast i (ψ i) M)) := by
      funext y
      simp [e, Finset.sum_apply]
    rw [he', A.kernel.iterate_finset_sum]
    simp only [Finset.sum_apply]
  rwa [hr, heq] at hresult

end GraphicalAllocation.Transport
