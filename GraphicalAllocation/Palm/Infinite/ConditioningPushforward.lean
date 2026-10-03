import Mathlib.Probability.Kernel.CondDistrib

/-! # Independent seeds and observation-dependent conditional pushforwards

These measure-theoretic bridges retain an independent random initial seed and
allow the transformation of the hidden source to depend on the observed path.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace GraphicalAllocation.Palm.Infinite

variable {Ω Base Seed Z : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Base] [MeasurableSpace Seed] [MeasurableSpace Z]

/-- Adjoining an independent seed does not change the hidden-source
conditional distribution. The seed keeps its original law conditionally. -/
theorem condDistrib_id_independent_seed
    [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Seed] [Nonempty Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Base) (hY : Measurable Y) :
    condDistrib id (fun s : Seed × Ω => Y s.2) (ν.prod P) =ᵐ[P.map Y]
      (Kernel.const Base ν).prod (condDistrib id Y P) := by
  have hm : (ν.prod P).map (fun s : Seed × Ω => Y s.2) = P.map Y := by
    change (ν.prod P).map (Y ∘ Prod.snd) = P.map Y
    rw [← Measure.map_map hY measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hm]
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) measurable_id
  rw [hm]
  apply Measure.ext_prod₃
  intro S T U hS hT hU
  have hpre : (fun s : Seed × Ω => (Y s.2, s)) ⁻¹' (S ×ˢ T ×ˢ U) =
      T ×ˢ (Y ⁻¹' S ∩ U) := by
    ext p
    simp only [mem_preimage, mem_prod, mem_inter_iff]
    tauto
  have hdis : (∫⁻ b in S, condDistrib id Y P b U ∂P.map Y) = P (Y ⁻¹' S ∩ U) := by
    have he := congrArg (fun μ : Measure (Base × Ω) => μ (S ×ˢ U))
      (compProd_map_condDistrib (μ := P) hY.aemeasurable aemeasurable_id)
    rw [Measure.compProd_apply_prod hS hU, Measure.map_apply (by fun_prop) (hS.prod hU)] at he
    exact he
  rw [Measure.map_apply (by fun_prop) (hS.prod (hT.prod hU))]
  change (ν.prod P) ((fun s : Seed × Ω => (Y s.2, s)) ⁻¹' (S ×ˢ T ×ˢ U)) = _
  rw [hpre,
    Measure.prod_prod, Measure.compProd_apply_prod hS (hT.prod hU)]
  simp_rw [Kernel.prod_apply_prod, Kernel.const_apply]
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hU), hdis]

/-- Push a kernel forward by a jointly measurable transformation that may read
both the observation and the hidden source. -/
def observationMapKernel (κ : Kernel Base Ω) (F : Base × Ω → Z) : Kernel Base Z :=
  (Kernel.id.prod κ).map F

lemma observationMapKernel_isMarkov (κ : Kernel Base Ω) [IsMarkovKernel κ]
    (F : Base × Ω → Z) (hF : Measurable F) :
    IsMarkovKernel (observationMapKernel κ F) := by
  unfold observationMapKernel
  exact Kernel.IsMarkovKernel.map _ hF

instance (κ : Kernel Base Ω) [IsSFiniteKernel κ] (F : Base × Ω → Z) :
    IsSFiniteKernel (observationMapKernel κ F) := by
  unfold observationMapKernel
  infer_instance

instance (κ : Kernel Base Ω) [IsFiniteKernel κ] (F : Base × Ω → Z) :
    IsFiniteKernel (observationMapKernel κ F) := by
  unfold observationMapKernel
  infer_instance

lemma observationMapKernel_apply (κ : Kernel Base Ω) [IsSFiniteKernel κ]
    (F : Base × Ω → Z) (hF : Measurable F) (b : Base) :
    observationMapKernel κ F b = (κ b).map (fun ω => F (b, ω)) := by
  apply Measure.ext
  intro S hS
  rw [observationMapKernel, Kernel.map_apply' _ hF _ hS,
    Kernel.id_prod_apply' _ _ (hS.preimage hF),
    Measure.map_apply (by fun_prop) hS]
  rfl

lemma compProd_observationMapKernel (μ : Measure Base) [SFinite μ]
    (κ : Kernel Base Ω) [IsSFiniteKernel κ]
    (F : Base × Ω → Z) (hF : Measurable F) :
    μ ⊗ₘ observationMapKernel κ F =
      (μ ⊗ₘ κ).map (fun bω => (bω.1, F bω)) := by
  apply Measure.ext
  intro S hS
  rw [Measure.compProd_apply hS, Measure.map_apply (by fun_prop) hS,
    Measure.compProd_apply (hS.preimage (by fun_prop))]
  congr 1
  funext b
  rw [observationMapKernel_apply κ F hF,
    Measure.map_apply (by fun_prop) (hS.preimage measurable_prodMk_left)]
  rfl

/-- Conditional distributions commute with jointly measurable transformations
that depend on the observed value as well as the hidden source. -/
theorem condDistrib_observationMap
    [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Z] [Nonempty Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Base) (hY : Measurable Y)
    (F : Base × Ω → Z) (hF : Measurable F) :
    condDistrib (fun ω => F (Y ω, ω)) Y P =ᵐ[P.map Y]
      fun b => (condDistrib id Y P b).map (fun ω => F (b, ω)) := by
  have he : condDistrib (fun ω => F (Y ω, ω)) Y P =ᵐ[P.map Y]
      observationMapKernel (condDistrib id Y P) F := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY (by fun_prop)
    rw [compProd_observationMapKernel _ _ _ hF,
      compProd_map_condDistrib hY.aemeasurable aemeasurable_id,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  exact he.mono (fun b hb => hb.trans (observationMapKernel_apply _ _ hF b))

/-- Combining the two bridges: an observation-dependent transformation of an
independent seed and the hidden source has the pushforward of their conditional
product law. -/
theorem condDistrib_observationMap_independent_seed
    [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Seed] [Nonempty Seed]
    [StandardBorelSpace Z] [Nonempty Z]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Base) (hY : Measurable Y)
    (F : Base × (Seed × Ω) → Z) (hF : Measurable F) :
    condDistrib (fun s : Seed × Ω => F (Y s.2, s))
      (fun s : Seed × Ω => Y s.2) (ν.prod P) =ᵐ[P.map Y]
        fun b => (ν.prod (condDistrib id Y P b)).map (fun s => F (b, s)) := by
  have hm : (ν.prod P).map (fun s : Seed × Ω => Y s.2) = P.map Y := by
    change (ν.prod P).map (Y ∘ Prod.snd) = P.map Y
    rw [← Measure.map_map hY measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have hp := condDistrib_observationMap (ν.prod P)
    (fun s : Seed × Ω => Y s.2) (by fun_prop) F hF
  rw [hm] at hp
  filter_upwards [hp, condDistrib_id_independent_seed ν P Y hY] with b hb hseed
  rw [hb, hseed, Kernel.prod_apply, Kernel.const_apply]

/-- The combined seed/pushforward law with any already identified version of
the hidden-source conditional distribution. -/
theorem condDistrib_observationMap_independent_seed_of_ae_eq
    [StandardBorelSpace Ω] [Nonempty Ω] [StandardBorelSpace Seed] [Nonempty Seed]
    [StandardBorelSpace Z] [Nonempty Z]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Base) (hY : Measurable Y)
    (κ : Base → Measure Ω) (hκ : condDistrib id Y P =ᵐ[P.map Y] κ)
    (F : Base × (Seed × Ω) → Z) (hF : Measurable F) :
    condDistrib (fun s : Seed × Ω => F (Y s.2, s))
      (fun s : Seed × Ω => Y s.2) (ν.prod P) =ᵐ[P.map Y]
        fun b => (ν.prod (κ b)).map (fun s => F (b, s)) := by
  filter_upwards [condDistrib_observationMap_independent_seed ν P Y hY F hF, hκ]
    with b hb hκb
  rw [hb, hκb]

end GraphicalAllocation.Palm.Infinite
