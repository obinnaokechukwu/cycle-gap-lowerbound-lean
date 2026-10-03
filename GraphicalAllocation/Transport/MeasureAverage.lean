import GraphicalAllocation.Process.PositiveJensen
import GraphicalAllocation.Transport.IterateAverage

/-! # Arbitrary initial-law averaging without load-moment hypotheses -/

noncomputable section
namespace GraphicalAllocation.Transport
open MeasureTheory Process
open scoped BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [OpensMeasurableSpace S]

/-- Bounded observables on the discrete state space are integrable under every
probability law, irrespective of its load or gap moments. -/
theorem integrable_of_bounded (μ : Measure S) [IsProbabilityMeasure μ]
    (f : S → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : Integrable f μ := by
  exact (BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf).integrable μ

/-- Positive-part response energy survives an arbitrary initial probability law. -/
theorem integral_energy_lower (μ : Measure S) [IsProbabilityMeasure μ]
    (f e : S → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) (he : Integrable e μ)
    {B : ℝ} (hB : 0 < B) (hpoint : ∀ x, max (f x) 0 ^ 2 / B ≤ e x) :
    max (∫ x, f x ∂μ) 0 ^ 2 / B ≤ ∫ x, e x ∂μ := by
  let f' : S →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf
  have hi : Integrable (fun x => max (f x) 0 ^ 2) μ :=
    (positiveTest f' ^ 2).integrable μ
  have hm := integral_mono (hi.div_const B) he hpoint
  rw [integral_div] at hm
  exact (div_le_div_of_nonneg_right (integral_pospart_sq μ f C hf) hB.le).trans hm

end GraphicalAllocation.Transport
