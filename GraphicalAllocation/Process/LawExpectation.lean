import GraphicalAllocation.Process.Law

/-!
# Probability-law / transition-operator bridge

The event-count expectations used in the algebraic proofs equal the integrals
under the explicitly constructed process laws.
-/

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators NNReal ENNReal
open MeasureTheory

variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

section General

variable [MeasurableSpace State]

theorem toMeasure_bind_fintype (p : PMF Choice) (q : Choice → PMF State) :
    (p.bind q).toMeasure = ∑ c, p c • (q c).toMeasure := by
  ext s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, tsum_fintype, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem integral_bind_fintype (p : PMF Choice) (q : Choice → PMF State)
    (f : State → ℝ) (hi : ∀ c, Integrable f (q c).toMeasure) :
    ∫ y, f y ∂(p.bind q).toMeasure = ∑ c, (p c).toReal * ∫ y, f y ∂(q c).toMeasure := by
  rw [toMeasure_bind_fintype, integral_finsetSum_measure]
  · simp only [integral_smul_measure, smul_eq_mul]
  · intro c _
    exact (hi c).smul_measure (p.apply_ne_top c)

end General

section ArbitraryBind

variable {Index : Type*} [MeasurableSpace State]

theorem toMeasure_bind_sum (p : PMF Index) (q : Index → PMF State) :
    (p.bind q).toMeasure = Measure.sum (fun i => p i • (q i).toMeasure) := by
  ext s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Fubini for a probability mixture, with genuine integrability rather than
an implicit finite-moment assumption. -/
theorem integral_bind (p : PMF Index) (q : Index → PMF State)
    (f : State → ℝ) (hi : Integrable f (p.bind q).toMeasure) :
    ∫ y, f y ∂(p.bind q).toMeasure =
      ∑' i, (p i).toReal * ∫ y, f y ∂(q i).toMeasure := by
  rw [toMeasure_bind_sum] at hi ⊢
  rw [integral_sum_measure hi]
  simp only [integral_smul_measure, smul_eq_mul]

end ArbitraryBind

section Countable

variable [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem integrable_pmf_of_bounded (p : PMF State) (f : State → ℝ) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) : Integrable f p.toMeasure := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) ?_⟩
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using hb x

/-- The explicitly constructed law realizes the finite-branching expectation operator. -/
theorem integral_eventLaw (k : ℕ) (x : State) (f : State → ℝ) (C : ℝ)
    (hb : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂(K.eventLaw k x).toMeasure = K.iterate k f x := by
  induction k generalizing x with
  | zero => simp [PMF.toMeasure_pure]
  | succ k ih =>
    rw [eventLaw_succ, integral_bind_fintype]
    · simp only [choiceLaw_apply, ENNReal.toReal_ofReal (K.nonneg _ _), ih, iterate_succ, step]
    · intro c
      exact integrable_pmf_of_bounded _ f C hb

/-- Averaging the initial state preserves the same transition expectations. -/
theorem integral_eventLawFrom (μ : PMF State) (k : ℕ) (f : State → ℝ) (C : ℝ)
    (hb : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂(K.eventLawFrom μ k).toMeasure =
      ∫ x, K.iterate k f x ∂μ.toMeasure := by
  unfold eventLawFrom
  rw [integral_bind _ _ _ (integrable_pmf_of_bounded _ f C hb)]
  rw [PMF.integral_eq_tsum μ _ (integrable_pmf_of_bounded _ _ C (K.iterate_bounded k hb))]
  congr 1
  funext x
  simp only [K.integral_eventLaw k x f C hb, smul_eq_mul]

/-- The genuine continuous-time law is exactly the independent Poisson mixture
of event-count expectations. -/
theorem integral_continuousLaw (rate time : ℝ≥0) (x : State)
    (f : State → ℝ) (C : ℝ) (hb : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂(K.continuousLaw rate time x).toMeasure =
      ∫ k, K.iterate k f x ∂ProbabilityTheory.poissonMeasure (rate * time) := by
  let p := (ProbabilityTheory.poissonMeasure (rate * time)).toPMF
  have hbounded : ∀ k, |K.iterate k f x| ≤ C := fun k => K.iterate_bounded k hb x
  have hi := integrable_pmf_of_bounded p (fun k => K.iterate k f x) C hbounded
  unfold continuousLaw
  rw [integral_bind _ _ _ (integrable_pmf_of_bounded _ f C hb)]
  have h := PMF.integral_eq_tsum p (fun k => K.iterate k f x) hi
  rw [Measure.toPMF_toMeasure] at h
  rw [h]
  congr 1
  funext k
  simp only [K.integral_eventLaw k x f C hb, smul_eq_mul]
  rfl

/-- Extended expectation equals the nonnegative integral even for infinite means. -/
theorem nonnegativeExpectation_eq_lintegral (μ : PMF State) (g : State → ℝ≥0∞) :
    nonnegativeExpectation μ g = ∫⁻ x, g x ∂μ.toMeasure := by
  rw [lintegral_countable']
  unfold nonnegativeExpectation
  apply tsum_congr
  intro x
  rw [PMF.toMeasure_apply_singleton μ x (measurableSet_singleton x)]
  exact mul_comm _ _

end Countable

end GraphicalAllocation.Process.FiniteKernel
