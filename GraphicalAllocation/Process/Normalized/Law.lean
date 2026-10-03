import GraphicalAllocation.Process.Normalized.State
import GraphicalAllocation.Process.Law

/-!
# Invariant laws of the normalized process

The normalized transition law samples an anchored profile, runs independent
future allocation events, and returns its unique anchored representative.
An invariant law is fixed by these genuine transition laws. Gap distributions
and extended expectations descend exactly, so stationary corollaries require
no moment, recurrence, or uniqueness assumption.
-/

noncomputable section
namespace GraphicalAllocation.Process

open Rules Transport MeasureTheory
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype E] [Nonempty E]

namespace AllocationRule
variable (A : AllocationRule V E)

/-- Actual normalized continuous-time law, using the canonical representative. -/
def normalizedTimeLaw (anchor : V) (π : PMF (NormalizedProfile anchor)) (t : ℝ≥0) :
    PMF (NormalizedProfile anchor) :=
  (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).map (normalize anchor)

/-- Invariance on the quotient, represented through its proved anchor equivalence. -/
def InvariantNormalizedLaw (anchor : V) (π : PMF (NormalizedProfile anchor)) : Prop :=
  ∀ t : ℝ≥0, A.normalizedTimeLaw anchor π t = π

end AllocationRule

section Expectations
variable [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]

omit [DecidableEq V] in
/-- Normalization preserves the entire gap tail distribution. -/
theorem normalize_gap_tail (anchor : V) (μ : PMF (Profile V)) (a : ℝ) :
    (μ.map (normalize anchor)).toMeasure {y | a ≤ gap y.val} =
      μ.toMeasure {x | a ≤ gap x} := by
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, gap_normalize]

omit [DecidableEq V] in
/-- Normalization preserves a possibly infinite expected gap. -/
theorem normalize_expected_gap (anchor : V) (μ : PMF (Profile V)) :
    (∫⁻ y, ENNReal.ofReal (gap y.val) ∂(μ.map (normalize anchor)).toMeasure) =
      ∫⁻ x, ENNReal.ofReal (gap x) ∂μ.toMeasure := by
  rw [← PMF.toMeasure_map (normalize anchor) μ (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [gap_normalize]

namespace AllocationRule
variable (A : AllocationRule V E) (anchor : V) (π : PMF (NormalizedProfile anchor))

/-- Stationarity identifies the actual finite-time gap tail with the invariant tail. -/
theorem invariant_gap_tail (hπ : A.InvariantNormalizedLaw anchor π) (t : ℝ≥0) (a : ℝ) :
    (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).toMeasure
      {x | a ≤ gap x} = π.toMeasure {y | a ≤ gap y.val} := by
  have h := normalize_gap_tail anchor
    (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t) a
  rw [show (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).map
    (normalize anchor) = π from hπ t] at h
  exact h.symm

/-- The expected-gap identity remains valid when the expectation is infinity. -/
theorem invariant_expected_gap (hπ : A.InvariantNormalizedLaw anchor π) (t : ℝ≥0) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).toMeasure) =
      ∫⁻ y, ENNReal.ofReal (gap y.val) ∂π.toMeasure := by
  have h := normalize_expected_gap anchor
    (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t)
  rw [show (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).map
    (normalize anchor) = π from hπ t] at h
  exact h.symm

/-- Any uniform finite-time gap lower bound transfers to every invariant
normalized law, with no auxiliary moment or uniqueness hypotheses. -/
theorem invariant_gap_lower_bound (hπ : A.InvariantNormalizedLaw anchor π) (t : ℝ≥0)
    (a p : ℝ≥0∞) (threshold : ℝ)
    (hmean : a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).toMeasure)
    (htail : p ≤ (A.kernel.continuousLawFrom (π.map Subtype.val) (Fintype.card E) t).toMeasure
      {x | threshold ≤ gap x}) :
    a ≤ ∫⁻ y, ENNReal.ofReal (gap y.val) ∂π.toMeasure ∧
      p ≤ π.toMeasure {y | threshold ≤ gap y.val} := by
  rw [A.invariant_expected_gap anchor π hπ t] at hmean
  rw [A.invariant_gap_tail anchor π hπ t threshold] at htail
  exact ⟨hmean, htail⟩

end AllocationRule
end Expectations
end GraphicalAllocation.Process
