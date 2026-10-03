import GraphicalAllocation.Transport.TimeAverage
import GraphicalAllocation.Transport.Constants
import Mathlib.Tactic.FieldSimp

/-!
# Exact event-count transport

The variance terms use terminal time `k+1` and derivatives terminating at `k`.
The source-tail probability is the actual allocation process probability.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable (A : AllocationRule V E)

/-- Averaged conditional variance of the martingale increment at lag h. -/
def discreteLagVariance (ψ : Equiv.Perm V) (M : ℝ) (k h : ℕ) (x : Profile V) : ℝ :=
  (∑ i, A.kernel.iterate (k - h)
    (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x) / Fintype.card V

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem discreteLagVariance_nonneg (ψ : Equiv.Perm V) (M : ℝ) (k h : ℕ) (x : Profile V) :
    0 ≤ discreteLagVariance A ψ M k h x := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun i hi => A.kernel.iterate_nonneg _ (A.kernel.variance_nonneg _) x
  · exact Nat.cast_nonneg _

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The mean-increment subtraction after any number of preceding events. -/
theorem averaged_variance_correction_lower (ψ : Equiv.Perm V) (hψ : ∀ i, i ≠ ψ i)
    {M Δ : ℝ} (hM : 0 < M) (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (n h : ℕ) (x : Profile V) :
    (∑ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x) -
      (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
    ∑ i, A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x := by
  have hi : ∀ i, A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M))) x -
      (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
      A.kernel.iterate n
      (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x := by
    intro i
    have hpoint : ∀ y, A.kernel.responseEnergy
        (A.kernel.iterate h (clippedContrast i (ψ i) M)) y -
        (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
        A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M)) y := by
      intro y
      rw [A.kernel.variance_eq_responseEnergy]
      have hb := clipped_iterate_mean_increment A i (ψ i) (hψ i) hM hΔ h y
      have habs := abs_le.mp hb
      nlinarith [sq_nonneg (2 * Δ / ((Fintype.card E : ℝ) * M))]
    have hmono := A.kernel.iterate_mono n hpoint x
    change A.kernel.iterate n
      (A.kernel.responseEnergy (A.kernel.iterate h (clippedContrast i (ψ i) M)) -
        (fun _ => (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2)) x ≤ _ at hmono
    simpa [FiniteKernel.iterate_sub, FiniteKernel.iterate_const] using hmono
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i hi' => hi i)
  simpa [Finset.sum_sub_distrib] using hsum

omit [DecidableEq E] in
/-- Single-lag variance lower bound, with the exact positive-part subtraction. -/
theorem discrete_lag_lower
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B q Δ : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ)
    (k h : ℕ) (hh : h ≤ k) (x : Profile V)
    (hq : ∀ y, allocationTagTail A h y d R ≤ q) :
    max (max (1 - allocationBadGap A k x M - 2 * q) 0 ^ 2 /
      ((Fintype.card V : ℝ) * B) - 4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2) 0 ≤
      M ^ 2 * discreteLagVariance A ψ M k h x := by
  have hMpos : 0 < M := by linarith
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hm : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have he := averaged_allocation_transport_energy A d hdiag hsym htriangle ψ hR hM hB hsep
    hvolume (k - h) h x hq
  rw [Nat.sub_add_cancel hh] at he
  have hc := averaged_variance_correction_lower A ψ (ne_of_separated d hdiag ψ hR hsep)
    hMpos hΔ (k - h) h x
  have hcomb : max (1 - allocationBadGap A k x M - 2 * q) 0 ^ 2 / (M ^ 2 * B) -
      (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2 ≤
      ∑ i, A.kernel.iterate (k - h)
        (A.kernel.variance (A.kernel.iterate h (clippedContrast i (ψ i) M))) x := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcomb
    (div_nonneg (sq_nonneg M) hN.le)
  have hid : M ^ 2 / (Fintype.card V : ℝ) *
      (max (1 - allocationBadGap A k x M - 2 * q) 0 ^ 2 / (M ^ 2 * B) -
        (Fintype.card V : ℝ) * (2 * Δ / ((Fintype.card E : ℝ) * M)) ^ 2) =
      max (1 - allocationBadGap A k x M - 2 * q) 0 ^ 2 / ((Fintype.card V : ℝ) * B) -
        4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2 := by
    field_simp
    ring
  rw [hid] at hscaled
  apply max_le
  · simpa [discreteLagVariance, div_mul_eq_mul_div, mul_div_assoc] using hscaled
  · exact mul_nonneg (sq_nonneg M) (discreteLagVariance_nonneg A ψ M k h x)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- The genuine variance budget, restricted to any valid collection of initial lags. -/
theorem discrete_lag_budget (ψ : Equiv.Perm V) (M : ℝ) (k H : ℕ) (hH : H ≤ k + 1)
    (x : Profile V) : (∑ h ∈ Finset.range H, discreteLagVariance A ψ M k h x) ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  unfold discreteLagVariance
  rw [← Finset.sum_div, Finset.sum_comm, div_le_iff₀ hN]
  have hbudget : ∀ i, (∑ h ∈ Finset.range H,
      A.kernel.iterate (k - h) (A.kernel.variance (A.kernel.iterate h
        (clippedContrast i (ψ i) M))) x) ≤ 1 := by
    intro i
    apply le_trans _ (A.kernel.discrete_bracket_budget k
      (fun y => abs_clippedContrast_le_one i (ψ i) M y) x)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hH)
    intro h hh hh'
    exact A.kernel.iterate_nonneg _ (A.kernel.variance_nonneg _) x
  calc
    _ ≤ ∑ i : V, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hbudget i)
    _ = _ := by simp

omit [DecidableEq E] in
/-- Equation (6.5) for every deterministic initial profile of the actual process.
There is no assumed transport inequality or conditional variance budget. -/
theorem discrete_transport_volume
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M Δ : ℝ} (hM : 1 ≤ M)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (k H : ℕ) (hH : H ≤ k + 1)
    (R B q : ℕ → ℝ) (hR : ∀ h < H, 0 < R h) (hB : ∀ h < H, 0 < B h)
    (hsep : ∀ h < H, ∀ i, 2 * R h ≤ d i (ψ i))
    (hvolume : ∀ h < H, ∀ v, ((closedBall d (R h) v).card : ℝ) ≤ B h)
    (hq : ∀ h < H, ∀ y, allocationTagTail A h y d (R h) ≤ q h) (x : Profile V) :
    (∑ h ∈ Finset.range H, max
      (max (1 - allocationBadGap A k x M - 2 * q h) 0 ^ 2 /
        ((Fintype.card V : ℝ) * B h) - 4 * Δ ^ 2 / (Fintype.card E : ℝ) ^ 2) 0) ≤ M ^ 2 := by
  calc
    _ ≤ ∑ h ∈ Finset.range H, M ^ 2 * discreteLagVariance A ψ M k h x := by
      apply Finset.sum_le_sum
      intro h hh
      have hhH := Finset.mem_range.mp hh
      have hhk : h ≤ k := by omega
      exact discrete_lag_lower A d hdiag hsym htriangle ψ (hR h hhH) hM (hB h hhH)
        (hsep h hhH) (hvolume h hhH) hΔ k h hhk x (hq h hhH)
    _ = M ^ 2 * ∑ h ∈ Finset.range H, discreteLagVariance A ψ M k h x := by rw [Finset.mul_sum]
    _ ≤ M ^ 2 * 1 := mul_le_mul_of_nonneg_left (discrete_lag_budget A ψ M k H hH x) (sq_nonneg M)
    _ = M ^ 2 := mul_one _

end GraphicalAllocation.Transport
