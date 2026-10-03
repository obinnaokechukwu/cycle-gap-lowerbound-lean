import GraphicalAllocation.Smoothed.CycleRule
import GraphicalAllocation.Smoothed.Law

/-!
# The exact event-count and physical-time upper bounds on cycles

The six reconstruction stages fix the universal horizons, the integer cycle
profiles and NNReal clock time, the actual `cycleRule` laws, specialization of
the graph theorem followed by Poissonization, the explicit constants, and the
natural/real power casts. The event theorem includes zero, which is needed by
the exact Poisson mixture even at positive physical time.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators NNReal ENNReal
open Process Rules Geometry Transport Spectral MeasureTheory SimpleGraph

lemma cycleRule_kernel_polynomial (n : ℕ) :
    (cycleRule n).kernel =
      (polynomialRule (cycleGraph (n + 3)) 2 10
        (by simp only [Fintype.card_fin]; omega) (by norm_num)).kernel := by
  simpa only [polynomialRule, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using
    cycleRule_kernel n

/-- The exact numerical upper bound for all counts up to the fixed horizon. -/
theorem cycle_smoothed_iterate_gap_le (n k : ℕ) (hk : k ≤ (n + 3) ^ 10) :
    (cycleRule n).kernel.iterate k gap 0 ≤
      300 * Real.sqrt (n + 3) * Real.log (n + 3) := by
  have hN : (3 : ℝ) ≤ n + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [cycleRule_kernel_polynomial]
  have h := smoothed_polynomial_iterate_gap_le (cycleGraph (n + 3)) (cycle_regular n)
    (cycleGraph_connected (n := n + 2)) (by simp only [Fintype.card_fin]; omega)
    (show (1 : ℝ) ≤ 10 by norm_num) k
    (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using cycle_event_horizon n k hk) 0
  refine h.trans ?_
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using
    cycle_bound_le hN (cycle_greenRadius_le n)

/-- The stated event-count conclusion uses the genuine allocation-law integral. -/
theorem cycle_smoothed_event_expectation_le (n k : ℕ) (hk : k ≤ (n + 3) ^ 10) :
    (∫⁻ x, ENNReal.ofReal (gap x) ∂((cycleRule n).kernel.eventLaw k 0).toMeasure) ≤
      ENNReal.ofReal (300 * Real.sqrt (n + 3) * Real.log (n + 3)) := by
  rw [FiniteKernel.lintegral_eventLaw_ofReal _ _ _ _ gap_nonneg]
  exact ENNReal.ofReal_le_ofReal (cycle_smoothed_iterate_gap_le n k hk)

/-- The real integral has no integrability caveat at a finite event count. -/
theorem cycle_smoothed_event_integral_le (n k : ℕ) (hk : k ≤ (n + 3) ^ 10) :
    (∫ x, gap x ∂((cycleRule n).kernel.eventLaw k 0).toMeasure) ≤
      300 * Real.sqrt (n + 3) * Real.log (n + 3) := by
  rw [FiniteKernel.integral_eventLaw_unbounded]
  exact cycle_smoothed_iterate_gap_le n k hk

lemma cycle_smoothed_iterate_gap_le_count (n k : ℕ) :
    (cycleRule n).kernel.iterate k gap 0 ≤ k := by
  rw [cycleRule_kernel]
  exact smoothed_iterate_gap_le_count (cycleGraph (n + 3)) _ k 0

/-- Every edge rings at rate one; the upper bound includes physical time zero. -/
theorem cycle_smoothed_continuous_expectation_le (n : ℕ) (time : ℝ≥0)
    (ht : (time : ℝ) ≤ (n + 3 : ℝ) ^ 4) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ≤
      ENNReal.ofReal (300 * Real.sqrt (n + 3) * Real.log (n + 3) + 2) := by
  have hN : (3 : ℝ) ≤ n + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlog : 0 ≤ Real.log (n + 3) := (by norm_num : (0 : ℝ) ≤ 1).trans (log_ge_one hN)
  have hb : 0 ≤ 300 * Real.sqrt (n + 3) * Real.log (n + 3) := by positivity
  have hh : 0 < (n + 3 : ℝ) ^ 10 := by positivity
  have hsmall (k : ℕ) (hk : (k : ℝ) ≤ (n + 3 : ℝ) ^ 10) :
      (cycleRule n).kernel.iterate k gap 0 ≤
        300 * Real.sqrt (n + 3) * Real.log (n + 3) := by
    apply cycle_smoothed_iterate_gap_le n k
    exact_mod_cast hk
  have h := (cycleRule n).kernel.poisson_upper_of_event_bound (n + 3) time 0 gap
    gap_nonneg hb hh hsmall (cycle_smoothed_iterate_gap_le_count n)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hμ : (((n + 3 : ℝ≥0) * time : ℝ≥0) : ℝ) ≤ (n + 3 : ℝ) ^ 5 := by
    simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat] using
      cycle_poisson_mean_le (show (0 : ℝ) ≤ n + 3 by positivity) ht
  have herr := cycle_poisson_remainder_le_two hN
    (NNReal.coe_nonneg ((n + 3) * time)) hμ
  linarith

/-- Finiteness is established before using a real physical-time expectation. -/
theorem cycle_smoothed_continuous_integrable (n : ℕ) (time : ℝ≥0)
    (ht : (time : ℝ) ≤ (n + 3 : ℝ) ^ 4) :
    Integrable gap ((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_of_countable gap).aestronglyMeasurable (ae_of_all _ gap_nonneg)).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (cycle_smoothed_continuous_expectation_le n time ht)

/-- Literal real-expectation form of the physical-time assertion. -/
theorem cycle_smoothed_continuous_integral_le (n : ℕ) (time : ℝ≥0)
    (ht : (time : ℝ) ≤ (n + 3 : ℝ) ^ 4) :
    (∫ x, gap x ∂((cycleRule n).kernel.continuousLaw (n + 3) time 0).toMeasure) ≤
      300 * Real.sqrt (n + 3) * Real.log (n + 3) + 2 := by
  have hN : (3 : ℝ) ≤ n + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlog : 0 ≤ Real.log (n + 3) := (by norm_num : (0 : ℝ) ≤ 1).trans (log_ge_one hN)
  have h := cycle_smoothed_continuous_expectation_le n time ht
  rw [← ofReal_integral_eq_lintegral_ofReal (cycle_smoothed_continuous_integrable n time ht)
    (ae_of_all _ gap_nonneg)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end GraphicalAllocation.Smoothed
