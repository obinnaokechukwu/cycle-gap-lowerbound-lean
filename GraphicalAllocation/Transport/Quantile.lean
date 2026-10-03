import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Transport-to-gap reduction with extended expectation

This argument applies to arbitrary nonnegative measurable real random variables.
In particular it never assumes a first moment. The expectation is the Lebesgue
integral in `ℝ≥0∞`, so an infinite expected gap is represented faithfully.
-/

namespace GraphicalAllocation.Transport
open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A lower quantile bounds the extended expectation from below. -/
theorem quantile_le_extended_expectation (μ : Measure Ω) (g : Ω → ℝ)
    (hg : Measurable g) (hgn : ∀ ω, 0 ≤ g ω) {a c : ℝ} (ha : 0 < a) (_hc : 0 ≤ c)
    (htail : ENNReal.ofReal c ≤ μ {ω | a ≤ g ω}) :
    ENNReal.ofReal (a * c) ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
  have hmarkov := mul_meas_ge_le_lintegral (μ := μ) (hg.ennreal_ofReal) (ENNReal.ofReal a)
  have hset : {ω | ENNReal.ofReal a ≤ ENNReal.ofReal (g ω)} = {ω | a ≤ g ω} := by
    ext ω
    exact ENNReal.ofReal_le_ofReal_iff (hgn ω)
  rw [hset] at hmarkov
  rw [ENNReal.ofReal_mul ha.le]
  exact (mul_le_mul_of_nonneg_left htail (zero_le : 0 ≤ ENNReal.ofReal a)).trans hmarkov

/-- A one-unit phase event supplies a first-moment lower bound, with no moment
hypothesis on the initial law. -/
theorem phase_le_extended_expectation (μ : Measure Ω) (g : Ω → ℝ)
    (hg : Measurable g) (hgn : ∀ ω, 0 ≤ g ω) (hphase : (1 / 3 : ℝ≥0∞) ≤ μ {ω | 1 ≤ g ω}) :
    (1 / 3 : ℝ≥0∞) ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
  have h := quantile_le_extended_expectation μ g hg hgn (a := 1) (c := 1 / 3)
    (by norm_num) (by norm_num) (by simpa using hphase)
  simpa using h

/-- Logical form of the transport-to-gap reduction used in T10 and the cycle
applications. For `Q > 2`, the admissible test `M = Q/2 + 1 < Q` forces a tail
larger than `1/8` at `Q/2`; its expectation cost is `Q/16`. For `Q ≤ 2`, the
one-unit phase event supplies both conclusions. No integrability or integer-gap
assumption is necessary. -/
theorem transport_to_gap (μ : Measure Ω) (g : Ω → ℝ) (hg : Measurable g) (hgn : ∀ ω, 0 ≤ g ω)
    (hphase : (1 / 3 : ℝ≥0∞) ≤ μ {ω | 1 ≤ g ω}) (Q : ℝ)
    (htransport : ∀ M : ℝ, 1 ≤ M →
      μ {ω | M - 1 < g ω} ≤ (1 / 8 : ℝ≥0∞) → Q ≤ M) :
    ENNReal.ofReal (Q / 16) ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ ∧
      (1 / 8 : ℝ≥0∞) ≤ μ {ω | Q / 16 ≤ g ω} := by
  by_cases hQ : Q ≤ 2
  · constructor
    · apply le_trans _ (phase_le_extended_expectation μ g hg hgn hphase)
      calc
        ENNReal.ofReal (Q / 16) ≤ ENNReal.ofReal (1 / 3) :=
          ENNReal.ofReal_le_ofReal (by linarith)
        _ = 1 / 3 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    · calc
        (1 / 8 : ℝ≥0∞) ≤ 1 / 3 := by norm_num
        _ ≤ μ {ω | 1 ≤ g ω} := hphase
        _ ≤ μ {ω | Q / 16 ≤ g ω} := measure_mono (fun ω hω => by
          change Q / 16 ≤ g ω
          change 1 ≤ g ω at hω
          linarith)
  · have hQpos : 0 < Q := by linarith
    have htail : (1 / 8 : ℝ≥0∞) < μ {ω | Q / 2 < g ω} := by
      by_contra ht
      have ht' : μ {ω | Q / 2 < g ω} ≤ (1 / 8 : ℝ≥0∞) := le_of_not_gt ht
      have h := htransport (Q / 2 + 1) (by linarith) (by simpa using ht')
      linarith
    have htail' : (1 / 8 : ℝ≥0∞) ≤ μ {ω | Q / 2 ≤ g ω} :=
      htail.le.trans (measure_mono (fun ω hω => by
        change Q / 2 ≤ g ω
        change Q / 2 < g ω at hω
        exact hω.le))
    constructor
    · have h := quantile_le_extended_expectation μ g hg hgn (a := Q / 2) (c := 1 / 8)
        (by linarith) (by norm_num) (by simpa using htail')
      convert h using 1
      congr 1
      ring
    · exact htail.le.trans (measure_mono (fun ω hω => by
        change Q / 16 ≤ g ω
        change Q / 2 < g ω at hω
        linarith))

end GraphicalAllocation.Transport
