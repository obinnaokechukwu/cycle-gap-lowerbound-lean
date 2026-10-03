import GraphicalAllocation.Process.Nonflat
import GraphicalAllocation.Process.SemigroupLaw
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Continuous-time one-event phase bound

In a Poisson interval of mean one, both zero events and one event have
probability exp(-1). A flat profile cannot stay flat after one placement;
a nonflat profile stays nonflat if there is no event. Positivity of the
semigroup propagates this uniform bound to all later times.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators NNReal ENNReal BoundedContinuousFunction
open Rules Transport MeasureTheory

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma raise_nonflat_of_flat [Nontrivial V] (x : Profile V) (z : V) (hx : gap x = 0) :
    1 ≤ gap (raise x z) := by
  apply one_le_gap_of_nonflat
  intro hflat
  obtain ⟨v, hv⟩ := exists_ne z
  have heq := (gap_eq_zero_iff _).mp hx z v
  have hnew := hflat z v
  simp [raise, hv] at hnew
  omega

variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]

noncomputable def nonflatTest : Profile V →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete nonflatIndicator 1 (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (nonflatIndicator_bounds x).1]
    exact (nonflatIndicator_bounds x).2)

omit [DecidableEq V] in
@[simp] lemma nonflatTest_apply (x : Profile V) : nonflatTest x = nonflatIndicator x := rfl

namespace FiniteKernel
variable [Nontrivial V] (K : FiniteKernel (Profile V) V)
variable (hnext : ∀ x v, K.next x v = raise x v)
include hnext

lemma step_nonflat_of_flat (x : Profile V) (hx : gap x = 0) :
    K.step nonflatTest x = 1 := by
  unfold FiniteKernel.step
  have he : ∀ v, nonflatTest (raise x v) = 1 := fun v => by
    simp [nonflatIndicator, raise_nonflat_of_flat x v hx]
  simp only [hnext, he, mul_one]
  exact K.total x

/-- Lemma 5.3 at the one-expected-event horizon. -/
theorem phase_one_event (rate : ℝ) (hr : 0 < rate) (x : Profile V) :
    Real.exp (-1) ≤ K.semigroup rate (1 / rate) nonflatTest x := by
  have hprod : (1 / rate) * rate = 1 := by field_simp
  have hnonneg : ∀ n, 0 ≤ FiniteKernel.poissonWeight ((1 / rate) * rate) n *
      K.iterate n nonflatTest x := fun n =>
    mul_nonneg (FiniteKernel.poissonWeight_nonneg (by rw [hprod]; norm_num) n)
      (K.iterate_nonneg n (fun y => (nonflatIndicator_bounds y).1) x)
  have hs := K.semigroup_hasSum rate (1 / rate) nonflatTest x
  by_cases hx : gap x = 0
  · have hl := hs.summable.le_tsum 1 (fun n _ => hnonneg n)
    rw [hs.tsum_eq] at hl
    simpa [hprod, hr.ne', FiniteKernel.poissonWeight, FiniteKernel.iterate_succ,
      K.step_nonflat_of_flat hnext x hx] using hl
  · have hg : 1 ≤ gap x := (gap_zero_or_one_le x).resolve_left hx
    have hl := hs.summable.le_tsum 0 (fun n _ => hnonneg n)
    rw [hs.tsum_eq] at hl
    simpa [hprod, hr.ne', FiniteKernel.poissonWeight, nonflatTest, nonflatIndicator, hg] using hl

/-- The paper's continuous-time phase bound, with arbitrary initial state. -/
theorem phase_later (rate t : ℝ) (hr : 0 < rate) (ht : 1 / rate ≤ t)
    (x : Profile V) :
    Real.exp (-1) ≤ K.semigroup rate t nonflatTest x := by
  have h := K.semigroup_mono hr.le (sub_nonneg.mpr ht)
    (f := BoundedContinuousFunction.const (Profile V) (Real.exp (-1)))
    (g := K.semigroup rate (1 / rate) nonflatTest)
    (K.phase_one_event hnext rate hr) x
  simp only [K.semigroup_const, BoundedContinuousFunction.const_apply] at h
  have he : t = (t - 1 / rate) + 1 / rate := by ring
  rw [he, K.semigroup_add]
  exact h

end FiniteKernel

namespace AllocationRule
variable [Fintype E] [Nonempty E] [Nontrivial V] (A : AllocationRule V E)

theorem phase_one_event (rate : ℝ) (hr : 0 < rate) (x : Profile V) :
    Real.exp (-1) ≤ A.kernel.semigroup rate (1 / rate) nonflatTest x :=
  A.kernel.phase_one_event (fun _ _ => rfl) rate hr x

theorem phase_later (rate t : ℝ) (hr : 0 < rate) (ht : 1 / rate ≤ t) (x : Profile V) :
    Real.exp (-1) ≤ A.kernel.semigroup rate t nonflatTest x :=
  A.kernel.phase_later (fun _ _ => rfl) rate t hr ht x

end AllocationRule

section Laws
variable [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]

omit [DecidableEq V] in
lemma integral_nonflatTest_eq (μ : PMF (Profile V)) :
    ∫ x, nonflatTest x ∂μ.toMeasure = μ.toMeasure.real {x | 1 ≤ gap x} := by
  have hm : MeasurableSet {x : Profile V | 1 ≤ gap x} := Set.Countable.measurableSet (Set.to_countable _)
  simpa [nonflatTest, nonflatIndicator, Set.indicator] using
    integral_indicator_const (μ := μ.toMeasure) (1 : ℝ) hm

namespace FiniteKernel
variable [Nontrivial V] (K : FiniteKernel (Profile V) V)

/-- The phase lemma for every finite-branching rule that adds exactly one ball. -/
theorem continuous_phase_probability (hnext : ∀ x v, K.next x v = raise x v) (μ : PMF (Profile V)) (rate time : ℝ≥0)
    (hr : 0 < rate) (ht : 1 / (rate : ℝ) ≤ time) :
    Real.exp (-1) ≤ (K.continuousLawFrom μ rate time).toMeasure.real
      {x | 1 ≤ gap x} := by
  have hrate : 0 < (rate : ℝ) := hr
  have hi : Integrable (fun x => K.semigroup rate time nonflatTest x) μ.toMeasure :=
    FiniteKernel.integrable_pmf_of_bounded μ _ 1
      (fun x => K.semigroup_bounded rate.property time.property
        (fun y => by
          rw [nonflatTest_apply, abs_of_nonneg (nonflatIndicator_bounds y).1]
          exact (nonflatIndicator_bounds y).2) x)
  have h := integral_mono (integrable_const (Real.exp (-1))) hi
    (K.phase_later hnext rate time hrate ht)
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  rw [← K.integral_continuousLawFrom_eq_semigroup] at h
  rwa [integral_nonflatTest_eq] at h

end FiniteKernel

namespace AllocationRule
variable [Fintype E] [Nonempty E] [Nontrivial V] (A : AllocationRule V E)

/-- Lemma 5.3 for the actual process law and every initial distribution. -/
theorem continuous_phase_probability (μ : PMF (Profile V)) (rate time : ℝ≥0)
    (hr : 0 < rate) (ht : 1 / (rate : ℝ) ≤ time) :
    Real.exp (-1) ≤ (A.kernel.continuousLawFrom μ rate time).toMeasure.real
      {x | 1 ≤ gap x} :=
  A.kernel.continuous_phase_probability (fun _ _ => rfl) μ rate time hr ht

omit [Nontrivial V] in
/-- The one-step event-count fallback as a probability statement under the
constructed law, uniformly over the initial distribution. -/
theorem discrete_nonflat_probability (μ : PMF (Profile V)) (Δ : ℝ)
    (hΔ : ∀ v, (A.degree v : ℝ) ≤ Δ) (k : ℕ) :
    1 - Δ / Fintype.card E ≤ (A.kernel.eventLawFrom μ (k + 1)).toMeasure.real
      {x | 1 ≤ gap x} := by
  have hb : ∀ x, |nonflatIndicator (V := V) x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (nonflatIndicator_bounds x).1]
    exact (nonflatIndicator_bounds x).2
  have hi := FiniteKernel.integrable_pmf_of_bounded μ _ 1
    (A.kernel.iterate_bounded (k + 1) hb)
  have h := integral_mono (integrable_const (1 - Δ / Fintype.card E)) hi
    (A.iterate_nonflatIndicator_ge Δ hΔ k)
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  rw [← A.kernel.integral_eventLawFrom μ (k + 1) nonflatIndicator 1 hb] at h
  change _ ≤ ∫ x, nonflatTest x ∂(A.kernel.eventLawFrom μ (k + 1)).toMeasure at h
  rwa [integral_nonflatTest_eq] at h

/-- A convenient rational phase constant for the no-moment quantile reduction. -/
theorem continuous_phase_third (μ : PMF (Profile V)) (rate time : ℝ≥0)
    (hr : 0 < rate) (ht : 1 / (rate : ℝ) ≤ time) :
    (1 / 3 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ rate time).toMeasure
      {x | 1 ≤ gap x} := by
  have hthird : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1) Real.exp_one_lt_three.le
  have h := hthird.trans (A.continuous_phase_probability μ rate time hr ht)
  have he := ENNReal.ofReal_le_ofReal h
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using he

end AllocationRule
end Laws
end GraphicalAllocation.Process
