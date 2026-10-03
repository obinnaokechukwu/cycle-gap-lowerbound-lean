import GraphicalAllocation.Palm.FiniteKernel
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact finite reduction of measurable marks

Along a prescribed finite path, record all selectors (and any finite edge label)
in a finite signature. Pushing the original probability measure through that
signature gives an exact finite weighted model, with no approximation and no
rationality restriction on the thresholds. This is the measure-theoretic bridge
to `FiniteKernel`.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators ENNReal
open MeasureTheory

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Probability weight of one finite observable signature. -/
def atomWeight (ρ : Measure Ω) (signature : Ω → A) (a : A) : ℝ :=
  (Measure.map signature ρ).real {a}

omit [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] in
lemma atomWeight_nonneg (ρ : Measure Ω) (signature : Ω → A) (a : A) :
    0 ≤ atomWeight ρ signature a := ENNReal.toReal_nonneg

omit [Fintype A] [DecidableEq A] in
lemma atomWeight_eq_cell (ρ : Measure Ω) {signature : Ω → A}
    (hs : Measurable signature) (a : A) :
    atomWeight ρ signature a = ρ.real (signature ⁻¹' {a}) := by
  simp [atomWeight, measureReal_def, Measure.map_apply hs (measurableSet_singleton a)]

omit [DecidableEq A] in
/-- Every observable factoring through the signature has exactly the same
expectation in the original probability space and in its finite reduction. -/
lemma integral_eq_atom_sum (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {signature : Ω → A} (hs : Measurable signature) (f : A → ℝ) :
    (∫ ω, f (signature ω) ∂ρ) = ∑ a, atomWeight ρ signature a * f a := by
  have : IsProbabilityMeasure (Measure.map signature ρ) := inferInstance
  rw [← integral_map_of_stronglyMeasurable hs (measurable_of_countable f).stronglyMeasurable]
  simpa [atomWeight, smul_eq_mul] using
    (integral_fintype (μ := Measure.map signature ρ) (f := f) Integrable.of_finite)

omit [DecidableEq A] in
lemma atomWeight_sum (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {signature : Ω → A} (hs : Measurable signature) :
    ∑ a, atomWeight ρ signature a = 1 := by
  simpa using (integral_eq_atom_sum ρ hs (fun _ => (1 : ℝ))).symm

omit [DecidableEq A] in
/-- Exact cell masses are preserved by the finite signature model. -/
lemma cellMass_atomWeight (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {signature : Ω → A} (hs : Measurable signature)
    {V : Type*} [DecidableEq V] (selector : A → V) (v : V) :
    cellMass (atomWeight ρ signature) selector v =
      ρ.real {ω | selector (signature ω) = v} := by
  have h := integral_eq_atom_sum ρ hs (fun a => if selector a = v then (1 : ℝ) else 0)
  have hm : MeasurableSet {ω | selector (signature ω) = v} :=
    hs ((Set.toFinite {a : A | selector a = v}).measurableSet)
  have hi : (∫ ω, (if selector (signature ω) = v then (1 : ℝ) else 0) ∂ρ) =
      ρ.real {ω | selector (signature ω) = v} := by
    simpa [Set.indicator] using integral_indicator_const (μ := ρ) (s := {ω | selector (signature ω) = v}) (1 : ℝ) hm
  rw [hi] at h
  simpa [cellMass, mul_ite] using h.symm

/-- A finite collection of measurable selectors is itself a measurable finite
signature. Include the edge label as another coordinate when retaining the
midpoint observable is necessary. -/
lemma measurable_selector_signature {I V : Type*} [Fintype I]
    [MeasurableSpace V] (selector : I → Ω → V)
    (hselector : ∀ i, Measurable (selector i)) :
    Measurable (fun ω i => selector i ω) :=
  Measurable.of_eval hselector

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Remove null signatures rather than assuming all signatures have positive
probability. This is finite even when some thresholds coincide. -/
abbrev PositiveAtoms (μ : A → ℝ) := {a : A // 0 < μ a}

instance (μ : A → ℝ) : Fintype (PositiveAtoms μ) := by
  classical
  exact Subtype.fintype _
instance (μ : A → ℝ) : DecidableEq (PositiveAtoms μ) := Classical.decEq _

def positiveAtomWeight (μ : A → ℝ) (a : PositiveAtoms μ) : ℝ := μ a.val

omit [Fintype A] [DecidableEq A] in
lemma positiveAtomWeight_pos (μ : A → ℝ) (a : PositiveAtoms μ) :
    0 < positiveAtomWeight μ a := a.property

omit [DecidableEq A] in
/-- Deleting null signatures changes no weighted observable sum. -/
lemma sum_positiveAtoms {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f : A → ℝ) :
    (∑ a : PositiveAtoms μ, positiveAtomWeight μ a * f a.val) = ∑ a, μ a * f a := by
  classical
  symm
  apply Finset.sum_congr_set {a : A | 0 < μ a}
  · intro a ha
    rfl
  · intro a ha
    have hz : μ a = 0 := le_antisymm (le_of_not_gt ha) (hμ a)
    simp [hz]

omit [DecidableEq A] in
lemma positiveAtomWeight_sum {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (hprob : ∑ a, μ a = 1) :
    ∑ a : PositiveAtoms μ, positiveAtomWeight μ a = 1 := by
  simpa using (sum_positiveAtoms hμ (fun _ => (1 : ℝ))).trans (by simpa using hprob)

omit [DecidableEq A] in
lemma cellMass_positiveAtoms {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    {V : Type*} [DecidableEq V] (p : A → V) (v : V) :
    cellMass (positiveAtomWeight μ) (fun a : PositiveAtoms μ => p a.val) v = cellMass μ p v := by
  simpa [cellMass, mul_ite] using sum_positiveAtoms hμ (fun a => if p a = v then (1 : ℝ) else 0)

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open MeasureTheory

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [DecidableEq A] in
lemma positiveAtom_has_representative (ρ : Measure Ω) {signature : Ω → A}
    (hs : Measurable signature) (a : PositiveAtoms (atomWeight ρ signature)) :
    ∃ ω, signature ω = a.val := by
  have hp : 0 < ρ.real (signature ⁻¹' {a.val}) := by
    rw [← atomWeight_eq_cell ρ hs]
    exact a.property
  have hn : ρ (signature ⁻¹' {a.val}) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hp
  exact nonempty_of_measure_ne_zero hn

/-- Choose a genuine original mark in every positive signature atom. -/
def atomRepresentative (ρ : Measure Ω) {signature : Ω → A}
    (hs : Measurable signature) (a : PositiveAtoms (atomWeight ρ signature)) : Ω :=
  Classical.choose (positiveAtom_has_representative ρ hs a)

omit [Fintype A] [DecidableEq A] in
lemma atomRepresentative_spec (ρ : Measure Ω) {signature : Ω → A}
    (hs : Measurable signature) (a : PositiveAtoms (atomWeight ρ signature)) :
    signature (atomRepresentative ρ hs a) = a.val :=
  Classical.choose_spec (positiveAtom_has_representative ρ hs a)

end GraphicalAllocation.Palm
