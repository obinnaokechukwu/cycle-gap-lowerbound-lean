import GraphicalAllocation.Transport.DiscreteTransport
import GraphicalAllocation.Transport.LawAverage
import GraphicalAllocation.Process.LawExpectation

/-!
# Exact-count transport from arbitrary initial laws

Every integral in this file concerns a bounded test or variance. The initial
profile law may have infinite expected gap. The final gap-tail quantity is
identified with the genuine event-count process law.
-/

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

/-- Averaged lag variance under the arbitrary initial law. -/
def discreteLagVarianceFrom (μ : Measure (Profile V)) (ψ : Equiv.Perm V)
    (M : ℝ) (k h : ℕ) : ℝ := ∫ x, discreteLagVariance A ψ M k h x ∂μ

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [TopologicalSpace (Profile V)]
  [DiscreteTopology (Profile V)] [MeasurableSpace (Profile V)] [OpensMeasurableSpace (Profile V)] in
theorem variance_sum_abs_le (ψ : Equiv.Perm V) (M : ℝ) (n h : ℕ) (x : Profile V) :
    |∑ i, A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x| ≤
      (Fintype.card V : ℝ) := by
  calc
    _ ≤ ∑ i, |A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : V, (1 : ℝ) := Finset.sum_le_sum (fun i hi =>
      A.kernel.iterate_bounded n (A.kernel.abs_variance_le_one
        (A.kernel.iterate_bounded h (fun y => abs_clippedContrast_le_one i (ψ i) M y))) x)
    _ = _ := by simp

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [OpensMeasurableSpace (Profile V)] in
theorem discreteLagVariance_abs_le_one (ψ : Equiv.Perm V) (M : ℝ) (k h : ℕ) (x : Profile V) :
    |discreteLagVariance A ψ M k h x| ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  unfold discreteLagVariance
  rw [abs_div, abs_of_pos hN]
  exact (div_le_one hN).mpr (variance_sum_abs_le A ψ M (k - h) h x)

omit [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [OpensMeasurableSpace (Profile V)] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem discreteLagVarianceFrom_nonneg (μ : Measure (Profile V)) (ψ : Equiv.Perm V)
    (M : ℝ) (k h : ℕ) : 0 ≤ discreteLagVarianceFrom A μ ψ M k h :=
  integral_nonneg (discreteLagVariance_nonneg A ψ M k h)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- Equation (6.7) under arbitrary initial laws, retaining the `k+1` terminal. -/
theorem discrete_lag_budget_from (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (ψ : Equiv.Perm V) (M : ℝ) (k H : ℕ) (hH : H ≤ k + 1) :
    (∑ h ∈ Finset.range H, discreteLagVarianceFrom A μ ψ M k h) ≤ 1 := by
  have hi : ∀ h, Integrable (fun x => discreteLagVariance A ψ M k h x) μ :=
    fun h => integrable_of_bounded μ _ 1 (discreteLagVariance_abs_le_one A ψ M k h)
  unfold discreteLagVarianceFrom
  rw [← integral_finsetSum _ (fun h hh => hi h)]
  have hs := integral_mono (integrable_finsetSum _ (fun h hh => hi h))
    (integrable_const (1 : ℝ)) (discrete_lag_budget A ψ M k H hH)
  simpa using hs

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The pointwise variance correction can be averaged without assuming any
moment of the profile or its gap. -/
theorem averaged_variance_correction_lower_from (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (ψ : Equiv.Perm V) (hψ : ∀ i, i ≠ ψ i) {M Δ : ℝ}
    (hM : 0 < M) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (n h : ℕ) :
    (∫ x, ∑ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x ∂μ) -
      (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
    ∫ x, ∑ i, A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x ∂μ := by
  have he : Integrable (fun x => ∑ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x) μ :=
    integrable_of_bounded μ _ (4 * Fintype.card V) (energy_sum_abs_le A ψ M n h)
  have hv : Integrable (fun x => ∑ i, A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x) μ :=
    integrable_of_bounded μ _ (Fintype.card V) (variance_sum_abs_le A ψ M n h)
  have hm := integral_mono (he.sub (integrable_const _)) hv
    (averaged_variance_correction_lower A ψ hψ hM hΔ n h)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub he (integrable_const ((Fintype.card V : ℝ) *
    (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2))] at hm
  simpa using hm

omit [DecidableEq E] in
/-- The exact single-lag subtraction with the true mixed-law terminal gap tail. -/
theorem discrete_lag_lower_from (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q Δ : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (k h : ℕ) (hh : h ≤ k) (hq : ∀ y, allocationTagTail A h y d R ≤ q) :
    max (max (1 - allocationBadGapFrom A μ k M - 2 * q) 0 ^ 2 /
      ((Fintype.card V : ℝ) * B) - 4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2) 0 ≤
      M ^ 2 * discreteLagVarianceFrom A μ ψ M k h := by
  have hMpos : 0 < M := by linarith
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hm : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have he := averaged_allocation_transport_energy_from A μ d hdiag hsym htriangle ψ hR hM hB hsep
    hvolume (k - h) h hq
  rw [Nat.sub_add_cancel hh] at he
  have hc := averaged_variance_correction_lower_from A μ ψ (ne_of_separated d hdiag ψ hR hsep)
    hMpos hΔ (k - h) h
  have hcomb : max (1 - allocationBadGapFrom A μ k M - 2 * q) 0 ^ 2 / (M ^ 2 * B) -
      (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
      ∫ x, ∑ i, A.kernel.iterate (k - h)
        (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x ∂μ := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcomb (div_nonneg (sq_nonneg M) hN.le)
  have hid : M ^ 2 / (Fintype.card V : ℝ) *
      (max (1 - allocationBadGapFrom A μ k M - 2 * q) 0 ^ 2 / (M ^ 2 * B) -
        (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2) =
      max (1 - allocationBadGapFrom A μ k M - 2 * q) 0 ^ 2 / ((Fintype.card V : ℝ) * B) -
        4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2 := by field_simp; ring
  rw [hid] at hscaled
  apply max_le
  · simpa [discreteLagVarianceFrom, discreteLagVariance, integral_div,
      div_mul_eq_mul_div, mul_div_assoc] using hscaled
  · exact mul_nonneg (sq_nonneg M) (discreteLagVarianceFrom_nonneg A μ ψ M k h)

omit [DecidableEq E] in
/-- The full exact-count transport-volume inequality for the genuine process
from any independent initial probability law, without any gap-moment assumption. -/
theorem discrete_transport_volume_from (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M Δ : ℝ} (hM : 1 ≤ M)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (k H : ℕ) (hH : H ≤ k + 1)
    (R B q : ℕ → ℝ) (hR : ∀ h < H, 0 < R h) (hB : ∀ h < H, 0 < B h)
    (hsep : ∀ h < H, ∀ i, 2 * R h ≤ d i (ψ i))
    (hvolume : ∀ h < H, ∀ v, ((closedBall d (R h) v).card : ℝ) ≤ B h)
    (hq : ∀ h < H, ∀ y, allocationTagTail A h y d (R h) ≤ q h) :
    (∑ h ∈ Finset.range H, max
      (max (1 - allocationBadGapFrom A μ k M - 2 * q h) 0 ^ 2 /
        ((Fintype.card V : ℝ) * B h) - 4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2) 0) ≤ M ^ 2 := by
  calc
    _ ≤ ∑ h ∈ Finset.range H, M ^ 2 * discreteLagVarianceFrom A μ ψ M k h := by
      apply Finset.sum_le_sum
      intro h hh
      have hhH := Finset.mem_range.mp hh
      have hhk : h ≤ k := by omega
      exact discrete_lag_lower_from A μ d hdiag hsym htriangle ψ (hR h hhH) hM (hB h hhH)
        (hsep h hhH) (hvolume h hhH) hΔ k h hhk (hq h hhH)
    _ = M ^ 2 * ∑ h ∈ Finset.range H, discreteLagVarianceFrom A μ ψ M k h := by rw [Finset.mul_sum]
    _ ≤ M ^ 2 * 1 := mul_le_mul_of_nonneg_left (discrete_lag_budget_from A μ ψ M k H hH) (sq_nonneg M)
    _ = M ^ 2 := mul_one _

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- The terminal gap probability in the transport formula is exactly that of
the constructed event-count process, not a separately specified law. -/
theorem allocationBadGapFrom_eq_probability (μ : PMF (Profile V)) (k : ℕ) (M : ℝ) :
    allocationBadGapFrom A μ.toMeasure k M =
      (A.kernel.eventLawFrom μ k).toMeasure.real {x | M - 1 < gap x} := by
  have hs : MeasurableSet {x : Profile V | M - 1 < gap x} :=
    measurableSet_lt measurable_const (measurable_of_countable gap)
  have hf : ∀ y : Profile V, |(if gap y ≤ M - 1 then (0 : ℝ) else 1)| ≤ 1 := by
    intro y
    split_ifs <;> norm_num
  have heq : (fun y : Profile V => if gap y ≤ M - 1 then (0 : ℝ) else 1) =
      Set.indicator {x | M - 1 < gap x} 1 := by
    funext y
    by_cases hy : gap y ≤ M - 1
    · simp [hy, not_lt.mpr hy]
    · simp [hy, lt_of_not_ge hy]
  unfold allocationBadGapFrom allocationBadGap
  rw [← A.kernel.integral_eventLawFrom μ k _ 1 hf, heq]
  exact integral_indicator_one hs

omit [DecidableEq E] in
/-- T13/(6.5) with the paper's literal maximum finite ball volume. -/
theorem discrete_transport_volume_ballVolume (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M Δ : ℝ} (hM : 1 ≤ M)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (k H : ℕ) (hH : H ≤ k + 1)
    (R q : ℕ → ℝ) (hR : ∀ h < H, 0 < R h)
    (hsep : ∀ h < H, ∀ i, 2 * R h ≤ d i (ψ i))
    (hq : ∀ h < H, ∀ y, allocationTagTail A h y d (R h) ≤ q h) :
    (∑ h ∈ Finset.range H, max
      (max (1 - allocationBadGapFrom A μ k M - 2 * q h) 0 ^ 2 /
        ((Fintype.card V : ℝ) * ballVolume d (R h)) -
          4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2) 0) ≤ M ^ 2 := by
  apply discrete_transport_volume_from A μ d hdiag hsym htriangle ψ hM hΔ k H hH R
    (fun h => (ballVolume d (R h) : ℝ)) q hR
  · intro h hh
    exact_mod_cast ballVolume_pos d hdiag (hR h hh).le
  · exact hsep
  · intro h hh v
    exact_mod_cast card_closedBall_le_volume d (R h) v
  · exact hq

end GraphicalAllocation.Transport
