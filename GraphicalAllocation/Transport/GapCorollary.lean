import GraphicalAllocation.Transport.ContinuousVolume
import GraphicalAllocation.Transport.Quantile
import GraphicalAllocation.Process.Phase
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The transport-to-gap corollary for the genuine allocation process -/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process MeasureTheory
open scoped BigOperators NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
  [OpensMeasurableSpace (Profile V)]
variable (A : AllocationRule V E)

omit [DecidableEq E] in
/-- T10, the paper's transport-to-gap corollary. Both the expected-gap and lower
quantile bounds hold for the genuine rate-m process from any independent initial
PMF. Expected gap is an extended nonnegative integral, allowing infinity. -/
theorem transport_gap (μ : PMF (Profile V))
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) (t : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (htime : 1 / (Fintype.card E : ℝ) ≤ t) (R : ℝ → ℝ) (hRm : Measurable R)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s)
    (hsep : ∀ s ∈ Set.Icc 0 T, ∀ i, 2 * R s ≤ d i (ψ i))
    (hq : ∀ s ∈ Set.Icc 0 T, ∀ x, continuousTagTail A (Real.toNNReal s) x d (R s) ≤ 1 / 8) :
    let I := (Fintype.card E : ℝ) / Fintype.card V *
      (∫ s in (0 : ℝ)..T, 1 / (ballVolume d (R s) : ℝ))
    ENNReal.ofReal (Real.sqrt I / 32) ≤
      ∫⁻ x, ENNReal.ofReal (gap x)
        ∂(A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure
      {x | Real.sqrt I / 32 ≤ gap x} := by
  let I : ℝ := (Fintype.card E : ℝ) / Fintype.card V *
    (∫ s in (0 : ℝ)..T, 1 / (ballVolume d (R s) : ℝ))
  let Q := Real.sqrt I / 2
  have hm : (0 : ℝ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have hphase := A.continuous_phase_third μ (Fintype.card E) t hm htime
  have htransport : ∀ M : ℝ, 1 ≤ M →
      (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure
        {x | M - 1 < gap x} ≤ (1 / 8 : ℝ≥0∞) → Q ≤ M := by
    intro M hM htail
    have hp : continuousBadGapFrom A μ.toMeasure t M ≤ 1 / 8 := by
      rw [continuousBadGapFrom_eq_probability, measureReal_def]
      simpa using ENNReal.toReal_mono (by norm_num : (1 / 8 : ℝ≥0∞) ≠ ⊤) htail
    have hs := continuous_transport_volume_simple_measurable A μ.toMeasure d hdiag hsym htriangle
      ψ hM t hT hTt R hRm hR hsep hq hp
    have hI : I = 4 * ((Fintype.card E : ℝ) / (4 * Fintype.card V) *
        (∫ s in (0 : ℝ)..T, 1 / (ballVolume d (R s) : ℝ))) := by dsimp [I]; ring
    have hIbound : I ≤ (2 * M) ^ 2 := by rw [hI]; nlinarith
    have hsqrt : Real.sqrt I ≤ 2 * M := Real.sqrt_le_iff.mpr ⟨by linarith, hIbound⟩
    dsimp [Q]
    linarith
  have h := transport_to_gap (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure
    gap (measurable_of_countable gap) gap_nonneg hphase Q htransport
  have hscale : Q / 16 = Real.sqrt I / 32 := by dsimp [Q]; ring
  rw [hscale] at h
  exact h

end GraphicalAllocation.Transport
