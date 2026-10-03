import GraphicalAllocation.Transport.ContinuousTransport
import GraphicalAllocation.Transport.VolumeMeasurable

/-! # The repaired measurable-radius transport-volume theorem -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process MeasureTheory
open scoped BigOperators NNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
  [OpensMeasurableSpace (Profile V)]
variable (A : AllocationRule V E)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [MeasurableSingletonClass (Profile V)] in
theorem continuousBadGapFrom_nonneg (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (M : ℝ) : 0 ≤ continuousBadGapFrom A μ t M := by
  apply boundedExpectation_nonneg
  apply A.kernel.semigroup_nonneg (Nat.cast_nonneg _) t.property
  intro x
  simp only [badGapObservable_apply]
  split_ifs <;> norm_num

omit [DecidableEq E] in
/-- T08/(5.4) in its exact repaired form: measurable lag-dependent radius and
tail envelope, actual finite maximum ball volume, and any independent initial
law. Integrability is proved, not supplied as an extra hypothesis. -/
theorem continuous_transport_volume_measurable (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M : ℝ} (hM : 1 ≤ M) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (R q : ℝ → ℝ)
    (hRm : Measurable R) (hqm : Measurable q)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s)
    (hsep : ∀ s ∈ Set.Icc 0 T, ∀ i, 2 * R s ≤ d i (ψ i))
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d (R s) ≤ q s) :
    (Fintype.card E : ℝ) / Fintype.card V *
      (∫ s in (0 : ℝ)..T, max (1 - continuousBadGapFrom A μ t M - 2 * q s) 0 ^ 2 /
        (ballVolume d (R s) : ℝ)) ≤ M ^ 2 := by
  have hq0 : ∀ s ∈ Set.Icc 0 T, 0 ≤ q s := fun s hs =>
    (continuousTagTail_bounds A (Real.toNNReal s) (fun _ => 0) d (R s)).1.trans (hq s hs _)
  apply continuous_transport_volume A μ d hdiag hsym htriangle ψ hM t hT hTt R
    (fun s => (ballVolume d (R s) : ℝ)) q hR
  · intro s hs
    exact_mod_cast ballVolume_pos d hdiag (hR s hs).le
  · exact hsep
  · intro s hs v
    exact_mod_cast card_closedBall_le_volume d (R s) v
  · exact hq
  · exact intervalIntegrable_transport_ballVolume d hdiag R q hRm hqm
      (continuousBadGapFrom_nonneg A μ t M) hT hR hq0

omit [DecidableEq E] in
/-- The exact `p,q ≤ 1/8` specialization with the actual measurable maximal
ball-volume function, without any unproved integral side condition. -/
theorem continuous_transport_volume_simple_measurable (μ : Measure (Profile V)) [IsProbabilityMeasure μ]
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {M : ℝ} (hM : 1 ≤ M) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (R : ℝ → ℝ) (hRm : Measurable R)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s)
    (hsep : ∀ s ∈ Set.Icc 0 T, ∀ i, 2 * R s ≤ d i (ψ i))
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d (R s) ≤ 1 / 8)
    (hp : continuousBadGapFrom A μ t M ≤ 1 / 8) :
    (Fintype.card E : ℝ) / (4 * Fintype.card V) *
      (∫ s in (0 : ℝ)..T, 1 / (ballVolume d (R s) : ℝ)) ≤ M ^ 2 := by
  apply continuous_transport_volume_simple A μ d hdiag hsym htriangle ψ hM t hT hTt R
    (fun s => (ballVolume d (R s) : ℝ)) hR
  · intro s hs
    exact_mod_cast ballVolume_pos d hdiag (hR s hs).le
  · exact hsep
  · intro s hs v
    exact_mod_cast card_closedBall_le_volume d (R s) v
  · exact hq
  · exact hp
  · exact intervalIntegrable_inverse_ballVolume d hdiag R hRm hT hR

end GraphicalAllocation.Transport
