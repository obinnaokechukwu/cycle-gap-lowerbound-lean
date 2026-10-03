import GraphicalAllocation.Applications.Graphs.SingleScale
import GraphicalAllocation.Diffusion.EmbeddingTail
import GraphicalAllocation.Transport.ContinuousTransport
import GraphicalAllocation.Transport.Quantile
import GraphicalAllocation.Process.Phase

/-! # Actual-process single-scale embedding lower bound

This instantiates both the Hilbert tag estimate and the transport theorem for
the actual allocation law. No diffusion or transport conclusion is a hypothesis.
The positivity D>0 is the explicit repair recorded in the mathematical audit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Diffusion MeasureTheory
open scoped ENNReal NNReal

variable {V E H : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
  [OpensMeasurableSpace (Profile V)]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype V] [Nontrivial V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [TopologicalSpace (Profile V)]
  [DiscreteTopology (Profile V)] [MeasurableSpace (Profile V)]
  [MeasurableSingletonClass (Profile V)] [OpensMeasurableSpace (Profile V)] in
/-- A nonempty clock set forces every upper bound on vertex degrees to be positive. -/
lemma allocation_degree_bound_pos (A : AllocationRule V E) (Δ : ℕ)
    (hΔ : ∀ v, A.degree v ≤ Δ) : 1 ≤ Δ := by
  obtain ⟨e⟩ := ‹Nonempty E›
  apply le_trans _ (hΔ (A.tail e))
  unfold AllocationRule.degree
  calc
    1 ≤ (if A.tail e = A.tail e then 1 else 0) +
        (if A.tail e = A.head e then 1 else 0) := by simp
    _ ≤ ∑ e', ((if A.tail e = A.tail e' then 1 else 0) +
        (if A.tail e = A.head e' then 1 else 0)) :=
      Finset.single_le_sum (f := fun e' =>
        (if A.tail e = A.tail e' then 1 else 0) +
        (if A.tail e = A.head e' then 1 else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)

omit [Nontrivial V] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
  [OpensMeasurableSpace (Profile V)] in
/-- The literal actual-process form of (7.3), including the probability cap. -/
theorem allocation_embedding_tail_envelope (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ 1)
    (d : V → V → ℝ) {D R : ℝ} (hD : 0 < D)
    (hd : ∀ i j, d i j ≤ D * ‖f j - f i‖) (hR : 0 < R)
    (x : Profile V) (s : ℝ≥0) :
    continuousTagTail A s x d R ≤
      min 1 (D ^ 2 * (2 * (Δ : ℝ) * (Δ + 1) * s + 2) / R ^ 2) := by
  refine le_min (continuousTagTail_bounds A s x d R).2 ?_
  simpa only [continuousTagTail, one_pow, mul_one] using
    allocation_embedding_tail_physical A Δ hΔ f 1 hedge d hD hd x s hR

/-- Equation (7.4), simultaneously as an extended expectation and a lower
quantile, for every independent initial PMF and every genuine allocation rule. -/
theorem allocation_embedding_lower_bound (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ 1)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    {D R B : ℝ} (hD : 0 < D) (hd : ∀ i j, d i j ≤ D * ‖f j - f i‖)
    (hR : 8 * D ≤ R) (hB : 0 < B) (ψ : Equiv.Perm V)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (μ : PMF (Profile V)) (t : ℝ≥0)
    (ht : embeddingHorizon D ((Δ : ℝ) * (Δ + 1)) R ≤ t)
    (hphaseTime : 1 / (Fintype.card E : ℝ) ≤ t) :
    let a := R / (256 * D * Real.sqrt ((Δ : ℝ) * (Δ + 1))) *
      Real.sqrt ((Fintype.card E : ℝ) / (Fintype.card V * B))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure
      {x | a ≤ gap x} := by
  dsimp only
  have hΔpos := allocation_degree_bound_pos A Δ hΔ
  have hδ : 0 < (Δ : ℝ) * (Δ + 1) := by
    have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔpos
    positivity
  have hRp : 0 < R := by linarith
  have hm : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos (α := E)
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hT := embeddingHorizon_pos hD hδ hRp
  let Q := Real.sqrt ((Fintype.card E : ℝ) / Fintype.card V *
    embeddingHorizon D ((Δ : ℝ) * (Δ + 1)) R / (4 * B))
  have hphase := A.continuous_phase_third μ (Fintype.card E) t
    (by exact_mod_cast Fintype.card_pos (α := E)) hphaseTime
  have hresult := transport_to_gap
    (A.kernel.continuousLawFrom μ (Fintype.card E) t).toMeasure gap
    (measurable_of_countable gap) gap_nonneg hphase Q (by
      intro M hM hp
      have hp' : continuousBadGapFrom A μ.toMeasure t M ≤ 1 / 8 := by
        rw [continuousBadGapFrom_eq_probability, measureReal_def]
        simpa using ENNReal.toReal_mono (by norm_num : (1 / 8 : ℝ≥0∞) ≠ ⊤) hp
      have hq : ∀ s ∈ Set.Icc 0 (embeddingHorizon D ((Δ : ℝ) * (Δ + 1)) R),
          ∀ x, continuousTagTail A (Real.toNNReal s) x d R ≤ 1 / 8 := by
        intro s hs x
        have he := allocation_embedding_tail_physical A Δ hΔ f 1 hedge d hD hd
          x (Real.toNNReal s) hRp
        change continuousTagTail A (Real.toNNReal s) x d R ≤ _ at he
        simp only [one_pow, mul_one, Real.coe_toNNReal s hs.1] at he
        have htau := embedding_horizon_tail hD hδ hR hs.2
        have halg : D ^ 2 * (2 * (Δ : ℝ) * (Δ + 1) * s + 2) / R ^ 2 =
            D ^ 2 * (2 * ((Δ : ℝ) * (Δ + 1)) * s + 2) / R ^ 2 := by ring
        rw [halg] at he
        exact he.trans (htau.trans (by norm_num))
      have htsp := continuous_transport_volume_constant A μ.toMeasure d hdiag hsym htriangle
        ψ hM hRp hB t hT.le ht hsep hvolume hq hp'
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by linarith, ?_⟩
      convert htsp using 1
      ring)
  have hid := embedding_scale_identity hD hδ hRp.le hm.le hN hB
  change Q / 16 = _ at hid
  rwa [hid] at hresult

end GraphicalAllocation.Applications.Graphs
