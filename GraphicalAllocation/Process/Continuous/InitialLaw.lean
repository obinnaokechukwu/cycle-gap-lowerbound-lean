import GraphicalAllocation.Process.Continuous.Variance

/-!
# Arbitrary independent initial distributions

All initial-law integrals below are of bounded functions. Thus no moment
assumption on the initial state or its gap is needed.
-/

noncomputable section

namespace GraphicalAllocation.Process

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

variable {State : Type*} [TopologicalSpace State] [MeasurableSpace State]
variable [OpensMeasurableSpace State]

/-- Integration of bounded tests against an arbitrary probability law. -/
def boundedExpectation (μ : Measure State) [IsProbabilityMeasure μ] :
    (State →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun a f => integral_smul a f }
    1 (fun f => by simpa using f.norm_integral_le_norm μ)

@[simp] theorem boundedExpectation_apply (μ : Measure State) [IsProbabilityMeasure μ]
    (f : State →ᵇ ℝ) : boundedExpectation μ f = ∫ x, f x ∂μ := rfl

@[simp] theorem boundedExpectation_const (μ : Measure State) [IsProbabilityMeasure μ]
    (c : ℝ) : boundedExpectation μ (BoundedContinuousFunction.const State c) = c := by
  simp [boundedExpectation]

theorem boundedExpectation_nonneg (μ : Measure State) [IsProbabilityMeasure μ]
    {f : State →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ boundedExpectation μ f :=
  integral_nonneg hf

theorem boundedExpectation_mono (μ : Measure State) [IsProbabilityMeasure μ]
    {f g : State →ᵇ ℝ} (hfg : ∀ x, f x ≤ g x) :
    boundedExpectation μ f ≤ boundedExpectation μ g :=
  integral_mono (f.integrable μ) (g.integrable μ) hfg

/-- Jensen's square inequality, proved from the nonnegative centered square. -/
theorem boundedExpectation_sq (μ : Measure State) [IsProbabilityMeasure μ]
    (f : State →ᵇ ℝ) : (boundedExpectation μ f) ^ 2 ≤ boundedExpectation μ (f ^ 2) := by
  let c := boundedExpectation μ f
  have h := boundedExpectation_nonneg μ
    (f := (f - BoundedContinuousFunction.const State c) ^ 2) (fun x => sq_nonneg _)
  have he : (f - BoundedContinuousFunction.const State c) ^ 2 =
      f ^ 2 - (2 * c) • f + BoundedContinuousFunction.const State (c ^ 2) := by
    ext x
    simp
    ring
  rw [he, map_add, map_sub, map_smul, boundedExpectation_const] at h
  change 0 ≤ boundedExpectation μ (f ^ 2) - 2 * c * c + c ^ 2 at h
  change c ^ 2 ≤ boundedExpectation μ (f ^ 2)
  nlinarith

namespace FiniteKernel

variable {Choice : Type*} [Fintype Choice] [DiscreteTopology State]
variable (K : FiniteKernel State Choice)
variable (μ : Measure State) [IsProbabilityMeasure μ]

/-- The actual Poissonized terminal variance in transition-expectation form. -/
def continuousVariance (rate t : ℝ) (f : State →ᵇ ℝ) : ℝ :=
  boundedExpectation μ (K.semigroup rate t (f ^ 2)) -
    (boundedExpectation μ (K.semigroup rate t f)) ^ 2

/-- Average response energy expressed with the paper's backward lag variable. -/
def lagResponseEnergy (rate t : ℝ) (f : State →ᵇ ℝ) (s : ℝ) : ℝ :=
  boundedExpectation μ (K.semigroup rate (t - s) (K.energy rate (K.semigroup rate s f)))

theorem continuous_lagResponseEnergy (rate t : ℝ) (f : State →ᵇ ℝ) :
    Continuous (K.lagResponseEnergy μ rate t f) := by
  have h := (boundedExpectation μ).continuous.comp
    ((K.continuous_transportedEnergy rate t f).comp
      (show Continuous (fun s : ℝ => t - s) from continuous_const.sub continuous_id))
  change Continuous (fun s => boundedExpectation μ
    (K.semigroup rate (t - s) (K.energy rate (K.semigroup rate s f))))
  simpa only [Function.comp_def, transportedEnergy, sub_sub_cancel] using h

/-- Exact finite-horizon conditional-variance identity, averaged over the initial law. -/
theorem integral_lagResponseEnergy (rate t : ℝ) (f : State →ᵇ ℝ) :
    (∫ s in (0 : ℝ)..t, K.lagResponseEnergy μ rate t f s) =
      boundedExpectation μ (K.semigroup rate t (f ^ 2)) -
        boundedExpectation μ ((K.semigroup rate t f) ^ 2) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun u => boundedExpectation μ (K.transportedEnergy rate t f u)) t (a := 0) (b := t)
  simp only [sub_self, sub_zero] at h
  have heq : (fun s => boundedExpectation μ (K.transportedEnergy rate t f (t - s))) =
      K.lagResponseEnergy μ rate t f := by
    funext s
    simp [transportedEnergy, lagResponseEnergy, sub_sub_cancel]
  rw [heq] at h
  rw [h, (boundedExpectation μ).intervalIntegral_comp_comm
    ((K.continuous_transportedEnergy rate t f).intervalIntegrable 0 t),
    K.integral_transportedEnergy, map_sub]

/-- Finite-horizon response-energy budget for any independent initial law. -/
theorem integral_lagResponseEnergy_le_variance (rate t : ℝ) (f : State →ᵇ ℝ) :
    (∫ s in (0 : ℝ)..t, K.lagResponseEnergy μ rate t f s) ≤
      K.continuousVariance μ rate t f := by
  rw [K.integral_lagResponseEnergy, continuousVariance]
  exact sub_le_sub_left (boundedExpectation_sq μ _) _

theorem lagResponseEnergy_nonneg {rate t s : ℝ} (hr : 0 ≤ rate) (hs : s ≤ t)
    (f : State →ᵇ ℝ) : 0 ≤ K.lagResponseEnergy μ rate t f s :=
  boundedExpectation_nonneg μ (K.semigroup_nonneg hr (sub_nonneg.mpr hs)
    (K.energy_nonneg hr _))

/-- Restricting to a shorter lag interval only decreases nonnegative energy. -/
theorem integral_lagResponseEnergy_le_variance_of_le {rate t T : ℝ}
    (hr : 0 ≤ rate) (hT : 0 ≤ T) (hTt : T ≤ t) (f : State →ᵇ ℝ) :
    (∫ s in (0 : ℝ)..T, K.lagResponseEnergy μ rate t f s) ≤
      K.continuousVariance μ rate t f := by
  apply le_trans _ (K.integral_lagResponseEnergy_le_variance μ rate t f)
  apply intervalIntegral.integral_mono_interval le_rfl hT hTt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact K.lagResponseEnergy_nonneg μ hr hs.2 f
  · exact (K.continuous_lagResponseEnergy μ rate t f).intervalIntegrable 0 t

/-- A test valued in `[-1,1]` has terminal variance at most one. -/
theorem continuousVariance_le_one {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t)
    {f : State →ᵇ ℝ} (hf : ∀ x, |f x| ≤ 1) : K.continuousVariance μ rate t f ≤ 1 := by
  have hf2 : ∀ x, f x ^ 2 ≤ 1 := fun x => by
    have ha := abs_le.mp (hf x)
    nlinarith [sq_nonneg (f x - 1), sq_nonneg (f x + 1)]
  have hp : ∀ x, K.semigroup rate t (f ^ 2) x ≤ 1 := fun x => by
    have h := K.semigroup_mono hr ht (f := f ^ 2)
      (g := BoundedContinuousFunction.const State 1) hf2 x
    simpa using h
  have hm := boundedExpectation_mono μ
    (f := K.semigroup rate t (f ^ 2)) (g := BoundedContinuousFunction.const State 1) hp
  rw [boundedExpectation_const] at hm
  unfold continuousVariance
  nlinarith [sq_nonneg (boundedExpectation μ (K.semigroup rate t f))]

/-- The unit variance budget used by the clipped-test transport inequality. -/
theorem integral_lagResponseEnergy_le_one {rate t T : ℝ}
    (hr : 0 ≤ rate) (hT : 0 ≤ T) (hTt : T ≤ t)
    {f : State →ᵇ ℝ} (hf : ∀ x, |f x| ≤ 1) :
    (∫ s in (0 : ℝ)..T, K.lagResponseEnergy μ rate t f s) ≤ 1 :=
  (K.integral_lagResponseEnergy_le_variance_of_le μ hr hT hTt f).trans
    (K.continuousVariance_le_one μ hr (hT.trans hTt) hf)

end FiniteKernel
end GraphicalAllocation.Process
