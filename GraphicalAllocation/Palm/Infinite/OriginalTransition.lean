import GraphicalAllocation.Process.OriginalTag
import Mathlib.Probability.Kernel.Basic

/-!
# Conditional transitions of the original marked discrepancy

Conditioning an original event on its selected base vertex gives normalized
restriction to that selection cell. Its synchronous discrepancy transition is
exactly the chronological cell-overlap row. Empty source-tag cells receive an
identity row, while a zero-probability base selection is explicitly excluded.
-/

noncomputable section
namespace GraphicalAllocation.Palm.Infinite
open MeasureTheory ProbabilityTheory Set Rules Process
open scoped ENNReal

variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]

/-- The chronological transition from an old uniform cell to its new selection.
The identity convention on a null old cell never affects the Palm law. -/
def continuousTagWeight (μ : Measure Ω) (old new : Ω → V) (i k : V) : ℝ≥0∞ :=
  if μ {a | old a = i} = 0 then (if i = k then 1 else 0)
  else μ {a | old a = i ∧ new a = k} / μ {a | old a = i}

/-- Original mark law conditional on a specified positive-mass selection cell. -/
def conditionalSelectionMeasure (μ : Measure Ω) (old : Ω → V) (j : V) : Measure Ω :=
  (μ {a | old a = j})⁻¹ • μ.restrict {a | old a = j}

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V] in
lemma conditionalSelectionMeasure_univ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (old : Ω → V) (j : V) (hj : μ {a | old a = j} ≠ 0) :
    conditionalSelectionMeasure μ old j univ = 1 := by
  rw [conditionalSelectionMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hj (measure_ne_top _ _)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] in
/-- Changes can leave only the selected cell, so every other tag row is identity,
including a null source cell. -/
lemma continuousTagWeight_of_not_selected (μ : Measure Ω) [IsProbabilityMeasure μ]
    (old new : Ω → V) (j : V) (hchange : ChangesOnlyFrom old new j)
    {i : V} (hi : i ≠ j) (k : V) :
    continuousTagWeight μ old new i k = if i = k then 1 else 0 := by
  by_cases hzero : μ {a | old a = i} = 0
  · simp [continuousTagWeight, hzero]
  by_cases hik : i = k
  · subst k
    have hs : {a | old a = i ∧ new a = i} = {a | old a = i} := by
      ext a
      exact ⟨And.left, fun ha => ⟨ha, (hchange a (ha ▸ hi)).trans ha⟩⟩
    simp only [continuousTagWeight, hzero, ite_false, ite_true, hs]
    exact ENNReal.div_self hzero (measure_ne_top _ _)
  · have hs : {a | old a = i ∧ new a = k} = ∅ := by
      ext a
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro ha hn
      exact hik (((hchange a (ha ▸ hi)).trans ha).symm.trans hn)
    simp [continuousTagWeight, hzero, hik, hs]

/-- The conditional event tag row is the overlap row for every source tag. -/
theorem conditionalSelection_tag_transition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (old new : Ω → V) (_hold : Measurable old) (hnew : Measurable new)
    (j : V) (hj : μ {a | old a = j} ≠ 0)
    (hchange : ChangesOnlyFrom old new j) (i k : V) :
    conditionalSelectionMeasure μ old j {a | (if i = j then new a else i) = k} =
      continuousTagWeight μ old new i k := by
  by_cases hij : i = j
  · subst i
    simp only [ite_true, continuousTagWeight, hj, ite_false]
    have hset : MeasurableSet {a | new a = k} := measurableSet_eq_fun hnew measurable_const
    rw [conditionalSelectionMeasure, Measure.smul_apply, Measure.restrict_apply hset]
    simp only [smul_eq_mul, div_eq_mul_inv]
    rw [mul_comm]
    congr 2
    ext a
    simp [and_comm]
  · rw [continuousTagWeight_of_not_selected μ old new j hchange hij]
    simp only [hij, ite_false]
    by_cases hik : i = k
    · simp only [hik, ite_true, Set.ofPred_true]
      exact conditionalSelectionMeasure_univ μ old j hj
    · simp [hik]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V] in
/-- A zero-mass selection cannot occur under the original mark law. -/
lemma null_selection_ae (μ : Measure Ω) (old : Ω → V) (j : V)
    (hj : μ {a | old a = j} = 0) : ∀ᵐ a ∂μ, old a ≠ j := by
  apply ae_iff.mpr
  simpa only [not_not] using hj

section Allocation
variable {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable (A : AllocationRule V E)

omit [DecidableEq E] [Nonempty E] in
/-- Measurability of the actual synchronous discrepancy under original marks. -/
lemma original_event_tag_measurable (x : Profile V) (i : V) :
    Measurable (fun a : E × ℝ => (A.event a.1 a.2).tag x i) := by
  have heq : (fun a : E × ℝ => (A.event a.1 a.2).tag x i) =
      (fun c : V × V => if i = c.1 then c.2 else i) ∘ A.originalTagSignature x i := by
    funext a
    exact (congrArg Prod.snd (A.originalTag_next x i a)).symm
  rw [heq]
  exact (measurable_of_countable _).comp (A.originalTagSignature_measurable x i)

omit [DecidableEq E] in
/-- Equation (3.5), including unchanged source tags: conditioning the genuine
uniform-edge/uniform-mark event on its base selection yields the overlap kernel. -/
theorem original_mark_conditional_transition (x : Profile V) (j i k : V)
    (hj : (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability x a = j} ≠ 0) :
    conditionalSelectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability x) j
      {a | (A.event a.1 a.2).tag x i = k} =
    continuousTagWeight markedMeasure
      (allocationSelector A.tail A.head A.probability x)
      (allocationSelector A.tail A.head A.probability (raise x j)) i k := by
  let old := allocationSelector A.tail A.head A.probability x
  let new := allocationSelector A.tail A.head A.probability (raise x j)
  have hold : Measurable old := by
    dsimp [old]
    rw [allocationSelector_eq]
    exact thresholdMarkSelector_measurable _ _ _
  have hnew : Measurable new := by
    dsimp [new]
    rw [allocationSelector_eq]
    exact thresholdMarkSelector_measurable _ _ _
  have htag : Measurable (fun a : E × ℝ => if i = j then new a else i) := by
    split_ifs <;> first | exact hnew | exact measurable_const
  calc
    _ = conditionalSelectionMeasure markedMeasure old j
        {a | (if i = j then new a else i) = k} := by
      unfold conditionalSelectionMeasure
      have hs₁ : MeasurableSet {a : E × ℝ | (A.event a.1 a.2).tag x i = k} :=
        measurableSet_eq_fun (original_event_tag_measurable A x i) measurable_const
      have hs₂ : MeasurableSet {a | (if i = j then new a else i) = k} :=
        measurableSet_eq_fun htag measurable_const
      rw [Measure.smul_apply, Measure.smul_apply,
        Measure.restrict_apply hs₁, Measure.restrict_apply hs₂]
      congr 2
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro ha
        refine ⟨?_, ha.2⟩
        have ht : (A.event a.1 a.2).tag x i = (if i = j then new a else i) :=
          event_tag_given_selection (A.event a.1 a.2) x j i ha.2
        exact ht.symm.trans ha.1
      · intro ha
        refine ⟨?_, ha.2⟩
        have ht : (A.event a.1 a.2).tag x i = (if i = j then new a else i) :=
          event_tag_given_selection (A.event a.1 a.2) x j i ha.2
        exact ht.trans ha.1
    _ = _ := conditionalSelection_tag_transition markedMeasure old new hold hnew j hj
      (allocationSelector_changesOnlyFrom A.tail A.head A.distinct A.probability
        A.probability_antitone x j) i k


/-- The original synchronous discrepancy kernel conditional on a selected base
vertex. This is the pushforward of the genuine conditional mark distribution. -/
def conditionalOriginalTagKernel (x : Profile V) (j : V)
    (_hj : (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability x a = j} ≠ 0) : Kernel V V :=
  Kernel.ofFunOfCountable (fun i =>
    (conditionalSelectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability x) j).map
        (fun a => (A.event a.1 a.2).tag x i))

instance conditionalOriginalTagKernel_isMarkov (x : Profile V) (j : V)
    (hj : (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability x a = j} ≠ 0) :
    IsMarkovKernel (conditionalOriginalTagKernel A x j hj) where
  isProbabilityMeasure i := by
    let : IsProbabilityMeasure (conditionalSelectionMeasure markedMeasure
        (allocationSelector A.tail A.head A.probability x) j) :=
      ⟨conditionalSelectionMeasure_univ markedMeasure _ j hj⟩
    change IsProbabilityMeasure ((conditionalSelectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability x) j).map
        (fun a => (A.event a.1 a.2).tag x i))
    infer_instance

omit [DecidableEq E] in
/-- Every singleton probability of the actual conditioned tag kernel is exactly
the chronological overlap row, with its stated null-cell convention. -/
theorem conditionalOriginalTagKernel_singleton (x : Profile V) (j : V)
    (hj : (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability x a = j} ≠ 0) (i k : V) :
    conditionalOriginalTagKernel A x j hj i {k} =
      continuousTagWeight markedMeasure
        (allocationSelector A.tail A.head A.probability x)
        (allocationSelector A.tail A.head A.probability (raise x j)) i k := by
  change (conditionalSelectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability x) j).map
        (fun a => (A.event a.1 a.2).tag x i) {k} = _
  rw [Measure.map_apply (original_event_tag_measurable A x i) (measurableSet_singleton k)]
  exact original_mark_conditional_transition A x j i k hj

end Allocation
end GraphicalAllocation.Palm.Infinite
