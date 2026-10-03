import GraphicalAllocation.Rules.Coupling
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating the one-ball coupling

This bridge works on an arbitrary measure space of finite event sequences.
The number of events may depend on the sample. Thus it applies to a fixed
finite horizon of a nonexplosive graphical construction, including a Poisson
clock construction, once its event-sequence law and integrability are supplied.
No specific graphical construction or Poisson existence theorem is asserted here.
-/

namespace GraphicalAllocation.Rules

open MeasureTheory

variable {V Ω : Type*} [DecidableEq V] [MeasurableSpace Ω]

/-- Equations (2.4)–(2.5) for any integrable distribution of finite event lists.
The two assumptions are exactly the integrability needed to subtract the two
expectations; the pathwise coupling itself was proved without them. -/
theorem finiteDifference_integral (μ : Measure Ω) (events : Ω → List (Event V))
    (f : Profile V → ℝ) (x : Profile V) (z : V)
    (hplus : Integrable (fun ω => f (run (events ω) (raise x z))) μ)
    (hbase : Integrable (fun ω => f (run (events ω) x)) μ) :
    finiteDifference (fun y => ∫ ω, f (run (events ω) y) ∂μ) x z =
      ∫ ω, finiteDifference f (run (events ω) x) (runTag (events ω) x z) ∂μ := by
  simp only [finiteDifference]
  rw [← integral_sub hplus hbase]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [run_oneBall]

/-- The response random variable is integrable whenever the two terminal
observables are. -/
theorem integrable_tag_response (μ : Measure Ω) (events : Ω → List (Event V))
    (f : Profile V → ℝ) (x : Profile V) (z : V)
    (hplus : Integrable (fun ω => f (run (events ω) (raise x z))) μ)
    (hbase : Integrable (fun ω => f (run (events ω) x)) μ) :
    Integrable
      (fun ω => finiteDifference f (run (events ω) x) (runTag (events ω) x z)) μ := by
  apply (hplus.sub hbase).congr
  filter_upwards [] with ω
  change f (run (events ω) (raise x z)) - f (run (events ω) x) =
    finiteDifference f (run (events ω) x) (runTag (events ω) x z)
  simp only [finiteDifference, run_oneBall]

/-- Bounded measurable terminal tests automatically meet the integral identity's
hypotheses for every finite measure, in particular every probability measure. -/
theorem finiteDifference_integral_of_bounded (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : Ω → List (Event V)) (f : Profile V → ℝ)
    (C : ℝ) (hbound : ∀ y, |f y| ≤ C)
    (hmeas : ∀ y, AEStronglyMeasurable (fun ω => f (run (events ω) y)) μ)
    (x : Profile V) (z : V) :
    finiteDifference (fun y => ∫ ω, f (run (events ω) y) ∂μ) x z =
      ∫ ω, finiteDifference f (run (events ω) x) (runTag (events ω) x z) ∂μ := by
  have hi : ∀ y, Integrable (fun ω => f (run (events ω) y)) μ := by
    intro y
    refine ⟨hmeas y, HasFiniteIntegral.of_bounded (C := C) ?_⟩
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hbound (run (events ω) y)
  exact finiteDifference_integral μ events f x z (hi (raise x z)) (hi x)

end GraphicalAllocation.Rules
