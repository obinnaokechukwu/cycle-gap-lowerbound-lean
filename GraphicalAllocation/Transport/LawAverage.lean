import GraphicalAllocation.Transport.MeasureAverage
import GraphicalAllocation.Transport.TimeAverage
import GraphicalAllocation.Transport.KernelBounds

/-! # Actual energy bounds under arbitrary initial probability laws -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process MeasureTheory
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [OpensMeasurableSpace (Profile V)]
variable (A : AllocationRule V E)

/-- The bad-gap probability obtained by averaging the actual transition law. -/
def allocationBadGapFrom (μ : Measure (Profile V)) (k : ℕ) (M : ℝ) : ℝ :=
  ∫ x, allocationBadGap A k x M ∂μ

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [OpensMeasurableSpace (Profile V)] in
theorem allocationBadGap_abs_le_one (k : ℕ) (M : ℝ) (x : Profile V) :
    |allocationBadGap A k x M| ≤ 1 := by
  apply A.kernel.iterate_bounded k
  intro y
  split_ifs <;> norm_num

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [TopologicalSpace (Profile V)]
  [DiscreteTopology (Profile V)] [MeasurableSpace (Profile V)] [OpensMeasurableSpace (Profile V)] in
theorem energy_sum_abs_le (ψ : Equiv.Perm V) (M : ℝ) (n h : ℕ) (x : Profile V) :
    |∑ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x| ≤
      4 * (Fintype.card V : ℝ) := by
  calc
    _ ≤ ∑ i, |A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : V, (4 : ℝ) := Finset.sum_le_sum (fun i hi =>
      A.kernel.iterate_bounded n (A.kernel.abs_responseEnergy_le_four
        (A.kernel.iterate_bounded h (fun y => abs_clippedContrast_le_one i (ψ i) M y))) x)
    _ = _ := by simp; ring

omit [DecidableEq E] in
/-- Average the actual event-time energy over an arbitrary independent initial
law. The terminal bad-gap probability is averaged before taking its square. -/
theorem averaged_allocation_transport_energy_from
    (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (n h : ℕ) (hq : ∀ y, allocationTagTail A h y d R ≤ q) :
    max (1 - allocationBadGapFrom A μ (n + h) M - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      ∫ x, ∑ i, A.kernel.iterate n
        (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x ∂μ := by
  let r : Profile V → ℝ := fun x => 1 - allocationBadGap A (n + h) x M - 2 * q
  let e : Profile V → ℝ := fun x => ∑ i, A.kernel.iterate n
    (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x
  have hr : ∀ x, |r x| ≤ |1 - 2 * q| + 1 := by
    intro x
    have hp := allocationBadGap_abs_le_one A (n + h) M x
    have ha := abs_sub (1 - 2 * q) (allocationBadGap A (n + h) x M)
    dsimp [r]
    have heq : 1 - allocationBadGap A (n + h) x M - 2 * q =
        (1 - 2 * q) - allocationBadGap A (n + h) x M := by ring
    rw [heq]
    exact ha.trans (add_le_add le_rfl hp)
  have hei : Integrable e μ :=
    integrable_of_bounded μ e (4 * Fintype.card V) (energy_sum_abs_le A ψ M n h)
  have hpoint : ∀ x, max (r x) 0 ^ 2 / (M ^ 2 * B) ≤ e x := fun x =>
    averaged_allocation_transport_energy A d hdiag hsym htriangle ψ hR hM hB hsep hvolume n h x hq
  have hden : 0 < M ^ 2 * B := mul_pos (sq_pos_of_pos (by linarith)) hB
  have hresult := integral_energy_lower μ r e (|1 - 2 * q| + 1) hr hei hden hpoint
  have hpint : Integrable (fun x => allocationBadGap A (n + h) x M) μ :=
    integrable_of_bounded μ _ 1 (allocationBadGap_abs_le_one A (n + h) M)
  have hrint : (∫ x, r x ∂μ) = 1 - allocationBadGapFrom A μ (n + h) M - 2 * q := by
    dsimp [r, allocationBadGapFrom]
    have hs : Integrable (fun x => 1 - allocationBadGap A (n + h) x M) μ :=
      (integrable_const 1).sub hpint
    rw [integral_sub (f := fun x => 1 - allocationBadGap A (n + h) x M)
      (g := fun _ => 2 * q) hs (integrable_const (2 * q)),
      integral_sub (f := fun _ => 1) (g := fun x => allocationBadGap A (n + h) x M)
        (integrable_const 1) hpint]
    simp
  rwa [hrint] at hresult

end GraphicalAllocation.Transport
