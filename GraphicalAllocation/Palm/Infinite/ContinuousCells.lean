import GraphicalAllocation.Palm.Infinite.CellKernel

/-! # Continuous conditional-cell intertwining

Restrictions to selection cells make the uniform-in-cell invariant explicit,
including null cells. The local kernel is the genuine regular conditional
resampling kernel on the original marked probability space.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace GraphicalAllocation.Palm.Infinite
variable {Ω V : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V] in
lemma localCode_selection (σ : Ω → V) (S : Finset V) (a : Ω) :
    (localCode σ S a).2.1 = σ a := by
  unfold localCode
  split_ifs <;> rfl

lemma localKernel_retains_selection (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂localKernel μ σ hσ S a, σ b = σ a := by
  filter_upwards [localKernel_map_code μ σ hσ S] with a ha
  have h : ∀ᵐ c ∂(localKernel μ σ hσ S a).map (localCode σ S),
      c = localCode σ S a := by rw [ha]; simp
  filter_upwards [ae_of_ae_map (localCode_measurable hσ S).aemeasurable h] with b hb
  simpa only [localCode_selection] using congrArg (fun c : Bool × V × Ω => c.2.1) hb

lemma localKernel_restrict_other (σ : Ω → V) (hσ : Measurable σ) (S : Finset V)
    (k : V) : ∀ᵐ a ∂μ, σ a ≠ k →
      (localKernel μ σ hσ S a).restrict {b | σ b = k} = 0 := by
  filter_upwards [localKernel_retains_selection μ σ hσ S] with a ha hk
  apply Measure.restrict_eq_zero.mpr
  have h : ∀ᵐ b ∂localKernel μ σ hσ S a, ¬ σ b = k := by
    filter_upwards [ha] with b hb
    simpa [hb] using hk
  simpa only [ae_iff, not_not] using h

lemma localKernel_restrict_active (σ : Ω → V) (hσ : Measurable σ) (S : Finset V)
    (k : V) (hk : k ∈ S) (hpos : μ {b | σ b = k} ≠ 0) :
    ∀ᵐ a ∂μ, (localKernel μ σ hσ S a).restrict {b | σ b = k} =
      if σ a = k then (μ {b | σ b = k})⁻¹ • μ.restrict {b | σ b = k} else 0 := by
  have hc : MeasurableSet {b | σ b = k} := hσ (measurableSet_singleton k)
  filter_upwards [localKernel_restrict_other μ σ hσ S k] with a ha
  by_cases hak : σ a = k
  · rw [ite_eq_left hak]
    ext t ht
    rw [Measure.restrict_apply ht, Measure.smul_apply, Measure.restrict_apply ht,
      localKernel_active_cell μ σ hσ S a (hak ▸ hk) (hak ▸ hpos) _
        (ht.inter hc)]
    simp only [hak, inter_self, inter_assoc, smul_eq_mul]
  · rw [ite_eq_right hak, ha hak]

lemma oldCell_localKernel_active (old new : Ω → V) (_hold : Measurable old)
    (hnew : Measurable new) (S : Finset V) (i k : V) (hk : k ∈ S)
    (hpos : μ {b | new b = k} ≠ 0) :
    (localKernel μ new hnew S ∘ₘ μ.restrict {a | old a = i}).restrict {b | new b = k} =
      (μ {a | old a = i ∧ new a = k} / μ {b | new b = k}) •
        μ.restrict {b | new b = k} := by
  have hc : MeasurableSet {b | new b = k} := hnew (measurableSet_singleton k)
  ext t ht
  rw [Measure.restrict_apply ht, Measure.bind_apply
    (ht.inter hc) (Kernel.aemeasurable _)]
  have hh : (fun a => localKernel μ new hnew S a (t ∩ {b | new b = k})) =ᵐ[
      μ.restrict {a | old a = i}]
      ({a | new a = k}.indicator (fun _ =>
        (μ {b | new b = k})⁻¹ * μ (t ∩ {b | new b = k}))) := by
    filter_upwards [ae_restrict_of_ae (localKernel_restrict_active μ new hnew S k hk hpos)]
      with a ha
    have he := congrArg (fun ν : Measure Ω => ν t) ha
    rw [Measure.restrict_apply ht] at he
    by_cases ha : new a = k <;>
      simpa [ha, Measure.smul_apply, Measure.restrict_apply ht] using he
  rw [lintegral_congr_ae hh, lintegral_indicator hc,
    setLIntegral_const, Measure.restrict_apply hc,
    Measure.smul_apply, Measure.restrict_apply ht]
  have hi : {a | new a = k} ∩ {a | old a = i} = {a | old a = i ∧ new a = k} := by
    ext a; simp [and_comm]
  rw [hi]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ac_rfl

lemma oldCell_localKernel_inactive (old new : Ω → V) (_hold : Measurable old)
    (hnew : Measurable new) (S : Finset V)
    (houtside : ∀ a, new a ∉ S → old a = new a) (i k : V) (hk : k ∉ S) :
    (localKernel μ new hnew S ∘ₘ μ.restrict {a | old a = i}).restrict {b | new b = k} =
      if i = k then μ.restrict {b | new b = k} else 0 := by
  have hc : MeasurableSet {b | new b = k} := hnew (measurableSet_singleton k)
  ext t ht
  rw [Measure.restrict_apply ht, Measure.bind_apply (ht.inter hc) (Kernel.aemeasurable _)]
  have hh : (fun a => localKernel μ new hnew S a (t ∩ {b | new b = k})) =ᵐ[
      μ.restrict {a | old a = i}] (fun a => Measure.dirac a (t ∩ {b | new b = k})) := by
    filter_upwards [ae_restrict_of_ae (localKernel_restrict_other μ new hnew S k),
      ae_restrict_of_ae (localKernel_inactive μ new hnew S)] with a ha hb
    by_cases hak : new a = k
    · rw [hb (hak ▸ hk)]
    · have he := congrArg (fun ν : Measure Ω => ν t) (ha hak)
      rw [Measure.restrict_apply ht] at he
      simpa [Measure.dirac_apply' a (ht.inter hc), hak] using he
  rw [lintegral_congr_ae hh]
  simp_rw [Measure.dirac_apply' _ (ht.inter hc)]
  rw [lintegral_indicator_one (ht.inter hc), Measure.restrict_apply (ht.inter hc)]
  have hs : (t ∩ {b | new b = k}) ∩ {a | old a = i} =
      if i = k then t ∩ {b | new b = k} else ∅ := by
    ext a
    by_cases hi : i = k
    · simp only [hi, ite_true, mem_inter_iff, mem_ofPred_eq, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.1⟩,
        fun h => ⟨h.1, h.2, (houtside a (h.2 ▸ hk)).trans h.2⟩⟩
    · simp only [hi, ite_false, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
        iff_false, not_and]
      intro hn ho
      exact hi (ho.symm.trans ((houtside a (hn.2 ▸ hk)).trans hn.2))
  rw [hs]
  by_cases hi : i = k <;> simp [hi, Measure.restrict_apply ht]

lemma oldCell_localKernel (old new : Ω → V) (hold : Measurable old)
    (hnew : Measurable new) (S : Finset V)
    (houtside : ∀ a, new a ∉ S → old a = new a) (i k : V) :
    (localKernel μ new hnew S ∘ₘ μ.restrict {a | old a = i}).restrict {b | new b = k} =
      (μ {a | old a = i ∧ new a = k} / μ {b | new b = k}) •
        μ.restrict {b | new b = k} := by
  have hc : MeasurableSet {b | new b = k} := hnew (measurableSet_singleton k)
  by_cases hpos : μ {b | new b = k} = 0
  · have hμc : μ.restrict {b | new b = k} = 0 := Measure.restrict_eq_zero.mpr hpos
    rw [hμc, smul_zero]
    apply Measure.restrict_eq_zero.mpr
    apply le_antisymm _ zero_le
    calc
      (localKernel μ new hnew S ∘ₘ μ.restrict {a | old a = i}) {b | new b = k}
        = ∫⁻ a, localKernel μ new hnew S a {b | new b = k}
            ∂μ.restrict {a | old a = i} :=
          Measure.bind_apply hc (Kernel.aemeasurable _)
      _ ≤ ∫⁻ a, localKernel μ new hnew S a {b | new b = k} ∂μ := by
        exact lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
      _ = (localKernel μ new hnew S ∘ₘ μ) {b | new b = k} :=
        (Measure.bind_apply hc (Kernel.aemeasurable _)).symm
      _ = 0 := by rw [localKernel_preserves, hpos]
  · by_cases hk : k ∈ S
    · exact oldCell_localKernel_active μ old new hold hnew S i k hk hpos
    · rw [oldCell_localKernel_inactive μ old new hold hnew S houtside i k hk]
      have hs : {a | old a = i ∧ new a = k} =
          if i = k then {a | new a = k} else ∅ := by
        ext a
        by_cases hi : i = k
        · simp only [hi, ite_true, mem_ofPred_eq]
          exact ⟨And.right, fun h => ⟨(houtside a (h ▸ hk)).trans h, h⟩⟩
        · simp only [hi, ite_false, mem_ofPred_eq, mem_empty_iff_false, iff_false,
            not_and]
          intro ho hn
          exact hi (ho.symm.trans ((houtside a (hn ▸ hk)).trans hn))
      rw [hs]
      by_cases hi : i = k
      · rw [ite_eq_left hi, ite_eq_left hi, ENNReal.div_self hpos (measure_ne_top μ _), one_smul]
      · simp [hi]

end GraphicalAllocation.Palm.Infinite
