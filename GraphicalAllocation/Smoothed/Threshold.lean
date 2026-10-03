import GraphicalAllocation.Smoothed.Rule
import GraphicalAllocation.Palm.Allocation
import Mathlib.Probability.Independence.Basic

/-!
# Literal uniform thresholds for the smoothed rule

The affine transform of the original unit mark has normalized Lebesgue law on
`[-θ, θ]`. Thus the threshold formulation in Section 8 is an equality of actual
probability laws, including selection events and independent fresh marks.

The six-stage reconstruction is: the law implication for `θ > 0`; real random
variables and Lebesgue measures; Mathlib's `pdf.IsUniform`; affine change of
variables followed by restriction; selection-event equivalence; and the
null-endpoint and normalization identities.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

/-- The threshold represented by the original uniform mark. -/
def threshold (θ u : ℝ) : ℝ := θ - 2 * θ * u

lemma threshold_measurable (θ : ℝ) : Measurable (threshold θ) := by
  unfold threshold
  fun_prop

/-- The literal uniform law, defined by normalized restricted Lebesgue measure. -/
def thresholdMeasure (θ : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * θ))⁻¹ • volume.restrict (Icc (-θ) θ)

lemma threshold_preimage_interval {θ : ℝ} (hθ : 0 < θ) :
    threshold θ ⁻¹' Ioo (-θ) θ = Ioo 0 1 := by
  ext u
  simp only [mem_preimage, mem_Ioo, threshold]
  constructor
  · intro h
    constructor <;> nlinarith
  · intro h
    constructor <;> nlinarith

lemma threshold_map_volume {θ : ℝ} (hθ : 0 < θ) :
    (volume : Measure ℝ).map (threshold θ) =
      (ENNReal.ofReal (2 * θ))⁻¹ • volume := by
  have hn : -2 * θ ≠ 0 := by positivity
  have heq : threshold θ = (fun x : ℝ => θ + x) ∘ (fun u : ℝ => (-2 * θ) * u) := by
    funext u
    simp only [threshold, Function.comp_apply]
    ring
  rw [heq, ← Measure.map_map (measurable_const_add θ) (measurable_const_mul _),
    Real.map_volume_mul_left hn,
    Measure.map_smul _ (measurable_const_add θ).aemeasurable, map_add_left_eq_self]
  congr 1
  rw [abs_inv, abs_of_neg (by nlinarith : -2 * θ < 0)]
  simp only [neg_mul, neg_neg]
  exact ENNReal.ofReal_inv_of_pos (by positivity)

/-- Exact affine change of variables, with endpoints justified by nullity. -/
theorem map_threshold_unitMarkMeasure {θ : ℝ} (hθ : 0 < θ) :
    Palm.unitMarkMeasure.map (threshold θ) = thresholdMeasure θ := by
  unfold Palm.unitMarkMeasure thresholdMeasure
  rw [← threshold_preimage_interval hθ,
    ← Measure.restrict_map (threshold_measurable θ) measurableSet_Ioo,
    threshold_map_volume hθ, Measure.restrict_smul, restrict_Ioo_eq_restrict_Icc]

lemma thresholdMeasure_eq_cond (θ : ℝ) :
    thresholdMeasure θ = ProbabilityTheory.cond volume (Icc (-θ) θ) := by
  simp only [thresholdMeasure, ProbabilityTheory.cond, Real.volume_Icc]
  congr 2
  congr 1
  ring

/-- The transformed mark is uniform on the paper's closed interval in the
literal Mathlib sense, not merely a law named "uniform". -/
theorem threshold_isUniform {θ : ℝ} (hθ : 0 < θ) :
    MeasureTheory.pdf.IsUniform (threshold θ) (Icc (-θ) θ) Palm.unitMarkMeasure where
  aemeasurable := (threshold_measurable θ).aemeasurable
  map_eq := (map_threshold_unitMarkMeasure hθ).trans (thresholdMeasure_eq_cond θ)

/-- The two decisions agree for almost every original mark, including clipped
probabilities zero and one. -/
lemma threshold_decision_ae {θ : ℝ} (hθ : 0 < θ) (z : ℝ) :
    ∀ᵐ u ∂Palm.unitMarkMeasure, (z ≤ threshold θ u ↔ u ≤ probability θ z) := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with u hu
  exact (mark_le_probability_iff hθ hu.1 hu.2).symm

/-- The closed upper-tail probability is exactly the clipped affine rule. -/
theorem thresholdMeasure_Ici {θ : ℝ} (hθ : 0 < θ) (z : ℝ) :
    (thresholdMeasure θ).real (Ici z) = probability θ z := by
  rw [← map_threshold_unitMarkMeasure hθ,
    map_measureReal_apply (threshold_measurable θ) measurableSet_Ici]
  calc
    _ = Palm.unitMarkMeasure.real (Iic (probability θ z)) := by
      apply measureReal_congr
      filter_upwards [threshold_decision_ae hθ z] with u hu
      exact propext hu
    _ = probability θ z :=
      Palm.unitMarkMeasure_le (probability_nonneg θ z) (probability_le_one θ z)

/-- Every threshold random variable with the paper's literal uniform law has
the prescribed clipped selection probability. -/
theorem uniform_threshold_selection_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T : Ω → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hT : MeasureTheory.pdf.IsUniform T (Icc (-θ) θ) P) (z : ℝ) :
    P.real {ω | z ≤ T ω} = probability θ z := by
  calc
    _ = (ProbabilityTheory.cond volume (Icc (-θ) θ)).real (Ici z) :=
      hT.measureReal_eq measurableSet_Ici
    _ = (thresholdMeasure θ).real (Ici z) := by rw [thresholdMeasure_eq_cond]
    _ = probability θ z := thresholdMeasure_Ici hθ z

/-- Literal threshold selection has exactly the original endpoint distribution. -/
theorem threshold_selection_measure {V : Type*} [DecidableEq V] {θ : ℝ}
    (hθ : 0 < θ) (left right v : V) (z : ℝ) :
    (thresholdMeasure θ).real {t | (if z ≤ t then left else right) = v} =
      (if v = left then probability θ z else 0) +
        (if v = right then 1 - probability θ z else 0) := by
  have hs : MeasurableSet {t : ℝ | (if z ≤ t then left else right) = v} := by
    have heq : {t : ℝ | (if z ≤ t then left else right) = v} =
        (if left = v then Ici z else ∅) ∪ (if right = v then (Ici z)ᶜ else ∅) := by
      ext t
      by_cases h : z ≤ t <;> simp [h]
      exact fun _ => lt_of_not_ge h
    rw [heq]
    apply MeasurableSet.union <;> split_ifs <;> simp
  rw [← map_threshold_unitMarkMeasure hθ,
    map_measureReal_apply (threshold_measurable θ) hs]
  calc
    _ = Palm.unitMarkMeasure.real
        {u | (if u ≤ probability θ z then left else right) = v} := by
      apply measureReal_congr
      filter_upwards [threshold_decision_ae hθ z] with u hu
      simp only [mem_preimage, mem_ofPred_eq, hu]
    _ = _ := Palm.unitMarkMeasure_selection left right v (probability θ z)
      (probability_nonneg θ z) (probability_le_one θ z)

/-- The normalized Lebesgue law is a probability measure for every positive cutoff. -/
lemma thresholdMeasure_isProbability {θ : ℝ} (hθ : 0 < θ) :
    IsProbabilityMeasure (thresholdMeasure θ) := by
  rw [← map_threshold_unitMarkMeasure hθ]
  infer_instance

/-- Any random mark with the original unit law yields the literal uniform
threshold law on its own probability space. -/
theorem threshold_isUniform_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U Palm.unitMarkMeasure P)
    {θ : ℝ} (hθ : 0 < θ) :
    MeasureTheory.pdf.IsUniform (threshold θ ∘ U) (Icc (-θ) θ) P :=
  (threshold_isUniform hθ).comp hU

/-- Independent fresh marks remain independent after the threshold transform. -/
theorem independent_thresholds {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ι → Ω → ℝ} (hU : iIndepFun U P) (θ : ℝ) :
    iIndepFun (fun i => threshold θ ∘ U i) P :=
  hU.comp (fun _ => threshold θ) (fun _ => threshold_measurable θ)

/-- A family of independent original marks gives a family of independent
thresholds, each genuinely uniform on `[-θ, θ]`. -/
theorem independent_uniform_thresholds {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : ι → Ω → ℝ} (hU : iIndepFun U P)
    (hLaw : ∀ i, HasLaw (U i) Palm.unitMarkMeasure P) {θ : ℝ} (hθ : 0 < θ) :
    iIndepFun (fun i => threshold θ ∘ U i) P ∧
      ∀ i, MeasureTheory.pdf.IsUniform (threshold θ ∘ U i) (Icc (-θ) θ) P :=
  ⟨independent_thresholds hU θ, fun i => threshold_isUniform_of_hasLaw (hLaw i) hθ⟩

section MarkedAllocation

open GraphicalAllocation.Process GraphicalAllocation.Rules

variable {E V : Type*} [Fintype E] [Nonempty E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

/-- A uniform edge and an independent literal normalized-Lebesgue threshold. -/
def thresholdMarkedMeasure (θ : ℝ) : Measure (E × ℝ) :=
  (PMF.uniformOfFintype E).toMeasure.prod (thresholdMeasure θ)

omit [MeasurableSingletonClass E] in
lemma map_threshold_markedMeasure {θ : ℝ} (hθ : 0 < θ) :
    (Palm.markedMeasure (E := E)).map (Prod.map id (threshold θ)) =
      thresholdMarkedMeasure (E := E) θ := by
  unfold Palm.markedMeasure thresholdMarkedMeasure
  rw [← Measure.map_prod_map _ _ measurable_id (threshold_measurable θ),
    Measure.map_id, map_threshold_unitMarkMeasure hθ]

/-- The endpoint selected by the literal threshold at an oriented edge. -/
def thresholdAllocationSelector (G : OrientedGraph V E) (x : Profile V)
    (a : E × ℝ) : V :=
  if ((x (G.tail a.1) - x (G.head a.1) : ℤ) : ℝ) ≤ a.2
    then G.tail a.1 else G.head a.1

omit [Nonempty E] in
lemma thresholdAllocationSelector_measurable [MeasurableSpace V]
    (G : OrientedGraph V E) (x : Profile V) :
    Measurable (thresholdAllocationSelector G x) := by
  apply Measurable.ite
  · exact measurableSet_le ((measurable_of_countable
      (fun e => ((x (G.tail e) - x (G.head e) : ℤ) : ℝ))).comp measurable_fst) measurable_snd
  · exact (measurable_of_countable G.tail).comp measurable_fst
  · exact (measurable_of_countable G.head).comp measurable_fst

omit [MeasurableSingletonClass E] in
lemma thresholdAllocationSelector_ae [DecidableEq V] (G : OrientedGraph V E)
    (x : Profile V) {θ : ℝ} (hθ : 0 < θ) :
    thresholdAllocationSelector G x ∘ Prod.map id (threshold θ) =ᵐ[Palm.markedMeasure]
      Palm.allocationSelector G.tail G.head (rule G θ hθ).probability x := by
  have hs : ∀ᵐ a ∂Palm.markedMeasure (E := E), a.2 ∈ Ioo (0 : ℝ) 1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae
      (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo)
  rw [Palm.allocationSelector_eq]
  filter_upwards [hs] with a ha
  change (if ((x (G.tail a.1) - x (G.head a.1) : ℤ) : ℝ) ≤ threshold θ a.2
      then G.tail a.1 else G.head a.1) =
    (if a.2 ≤ probability θ ((x (G.tail a.1) - x (G.head a.1) : ℤ) : ℝ)
      then G.tail a.1 else G.head a.1)
  simp only [threshold, ← mark_le_probability_iff hθ ha.1 ha.2]

/-- Equality of the actual endpoint laws with a uniform edge: the literal
uniform-threshold experiment and the previously defined allocation rule. -/
theorem thresholdAllocationSelector_law [DecidableEq V] [MeasurableSpace V]
    (G : OrientedGraph V E) (x : Profile V) {θ : ℝ} (hθ : 0 < θ) :
    (thresholdMarkedMeasure (E := E) θ).map (thresholdAllocationSelector G x) =
      Palm.markedMeasure.map
        (Palm.allocationSelector G.tail G.head (rule G θ hθ).probability x) := by
  rw [← map_threshold_markedMeasure hθ,
    Measure.map_map (thresholdAllocationSelector_measurable G x)
      (measurable_id.prodMap (threshold_measurable θ))]
  exact Measure.map_congr (thresholdAllocationSelector_ae G x hθ)

/-- The literal threshold experiment has exactly the smoothed allocation
kernel weights, hence the same one-event law used by the process. -/
theorem thresholdAllocationSelector_kernel_weight [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : OrientedGraph V E) (x : Profile V) {θ : ℝ} (hθ : 0 < θ) (v : V) :
    (thresholdMarkedMeasure (E := E) θ).real {a | thresholdAllocationSelector G x a = v} =
      (rule G θ hθ).kernel.weight x v := by
  have hm := congrArg (fun μ : Measure V => μ.real {v})
    (thresholdAllocationSelector_law G x hθ)
  rw [map_measureReal_apply (thresholdAllocationSelector_measurable G x)
    (measurableSet_singleton v),
    map_measureReal_apply (by
      rw [Palm.allocationSelector_eq]
      exact Palm.thresholdMarkSelector_measurable _ _ _) (measurableSet_singleton v)] at hm
  exact hm.trans ((rule G θ hθ).selectionCell_eq_kernel x v)

end MarkedAllocation

end GraphicalAllocation.Smoothed
