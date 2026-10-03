import GraphicalAllocation.Gaussian.Range
import GraphicalAllocation.Gaussian.Comparison
import GraphicalAllocation.Smoothed.Law

/-! # Gaussian comparison for the actual smoothed allocation law

These results compose the proved finite-horizon allocation theorem with the
constructed graph Gaussian law. No upper-bound or Gaussian-range premise is
supplied by the caller.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace GraphicalAllocation.Gaussian
open Process Rules Transport Spectral Smoothed

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Nonempty V] [Nonempty G.edgeSet]

omit [DecidableEq V] [Nonempty V] in
private theorem regular_degree_pos {d : ℕ} (hd : G.IsRegularOfDegree d) : 0 < d := by
  have hcount := graph_regular_degree_sum G hd
  by_contra hn
  have hd₀ : d = 0 := Nat.eq_zero_of_not_pos hn
  rw [hd₀] at hcount
  norm_num at hcount

/-- The exact displayed GFF comparison, under the actual smoothed-rule kernel. -/
theorem smoothed_gaussian_iterate_gap_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (polynomialRule G d ζ hN hζ).kernel.iterate k gap (fun _ => a) ≤
      2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt (Real.pi * (4 * (d : ℝ) + 3) / 2) * expectedRange G hG d + 4 / 3) + 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast regular_degree_pos G hd
  exact gaussianRange_substitution hd1 (by exact_mod_cast hN) hζ
    (greenRadius_nonneg G hG) (sqrt_radius_le_expectedRange G hG (Nat.cast_nonneg d))
    (smoothed_polynomial_iterate_gap_le G hd hG hN hζ k hk a)

/-- The one-sided `O_ζ(√d log N)` comparison with an explicit coefficient. -/
theorem smoothed_gaussian_iterate_gap_absorption {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (polynomialRule G d ζ hN hζ).kernel.iterate k gap (fun _ => a) ≤
      (48 * ζ + 54) * Real.sqrt (d : ℝ) * Real.log (Fintype.card V) * expectedRange G hG d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast regular_degree_pos G hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast regular_degree_pos G hd
  have hres := one_third_le_degree_radius G hG d hdpos
    (fun v => by rw [hd.degree_eq]) hN
  simpa only [gaussianRangeComparisonConstant_eq] using
    gaussianRange_absorption hd1 (by exact_mod_cast hN) hζ
      (greenRadius_nonneg G hG) (sqrt_radius_le_expectedRange G hG hdpos.le) hres
      (smoothed_polynomial_iterate_gap_le G hd hG hN hζ k hk a)

variable [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]

/-- The displayed Gaussian comparison for the ordinary expected allocation gap. -/
theorem smoothed_gaussian_integral_gap_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫ x, gap x ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt (Real.pi * (4 * (d : ℝ) + 3) / 2) * expectedRange G hG d + 4 / 3) + 2 := by
  rw [FiniteKernel.integral_eventLaw_unbounded]
  exact smoothed_gaussian_iterate_gap_le G hd hG hN hζ k hk a

/-- The explicit Gaussian-range factor for the ordinary expected allocation gap. -/
theorem smoothed_gaussian_integral_gap_absorption {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫ x, gap x ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      (48 * ζ + 54) * Real.sqrt (d : ℝ) * Real.log (Fintype.card V) * expectedRange G hG d := by
  rw [FiniteKernel.integral_eventLaw_unbounded]
  exact smoothed_gaussian_iterate_gap_absorption G hd hG hN hζ k hk a

/-- The displayed comparison in the paper's extended-expectation convention. -/
theorem smoothed_gaussian_expectation_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      ENNReal.ofReal (2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt (Real.pi * (4 * (d : ℝ) + 3) / 2) * expectedRange G hG d + 4 / 3) + 2) := by
  rw [FiniteKernel.lintegral_eventLaw_ofReal _ _ _ _ gap_nonneg]
  exact ENNReal.ofReal_le_ofReal (smoothed_gaussian_iterate_gap_le G hd hG hN hζ k hk a)

/-- The explicit multiplicative comparison, with every additive term absorbed. -/
theorem smoothed_gaussian_expectation_absorption {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      ENNReal.ofReal ((48 * ζ + 54) * Real.sqrt (d : ℝ) *
        Real.log (Fintype.card V) * expectedRange G hG d) := by
  rw [FiniteKernel.lintegral_eventLaw_ofReal _ _ _ _ gap_nonneg]
  exact ENNReal.ofReal_le_ofReal (smoothed_gaussian_iterate_gap_absorption G hd hG hN hζ k hk a)

end GraphicalAllocation.Gaussian
