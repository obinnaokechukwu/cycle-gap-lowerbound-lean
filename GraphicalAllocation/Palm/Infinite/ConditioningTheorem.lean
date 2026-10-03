import GraphicalAllocation.Palm.Infinite.ConditioningTag
import GraphicalAllocation.Palm.Infinite.ConditioningPushforward

/-! # The original tag's regular conditional law is the auxiliary Palm law

This is the source-semantic conditional-law conclusion of Proposition 3.1.
The source is an independent Palm initial tag and the original infinite iid
marked-edge process. The conditioning variable is its complete causal selected
base path. Both infinite tag processes are identified as regular conditional
laws, not merely as chains sharing individual transition formulas.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open GraphicalAllocation.Rules GraphicalAllocation.Process

namespace GraphicalAllocation.Palm.Infinite

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Independent Palm initialization and the actual iid original event marks. -/
def originalPalmSourceLaw (A : AllocationRule V E) (x : Profile V) :
    Measure (V × (ℕ → E × ℝ)) :=
  (markedMeasure.map (allocationSelector A.tail A.head A.probability x)).prod independentMarkLaw

instance originalPalmSourceLaw_isProbability (A : AllocationRule V E) (x : Profile V) :
    IsProbabilityMeasure (originalPalmSourceLaw A x) := by
  let : IsProbabilityMeasure
      ((markedMeasure (E := E)).map (allocationSelector A.tail A.head A.probability x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (allocationSelector_measurable A x).aemeasurable).mpr inferInstance
  unfold originalPalmSourceLaw
  infer_instance

omit [Nonempty V] [DecidableEq E] in
lemma originalPalmSourceLaw_observed (A : AllocationRule V E) (x : Profile V) :
    (originalPalmSourceLaw A x).map (fun s => originalSelection A x s.2) =
      (independentMarkLaw (E := E)).map (originalSelection A x) := by
  let : IsProbabilityMeasure
      ((markedMeasure (E := E)).map (allocationSelector A.tail A.head A.probability x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (allocationSelector_measurable A x).aemeasurable).mpr inferInstance
  change Measure.map ((originalSelection A x) ∘ Prod.snd) _ = _
  rw [← Measure.map_map (originalSelection_measurable A x) measurable_snd,
    originalPalmSourceLaw, Measure.map_snd_prod, measure_univ, one_smul]

omit [DecidableEq E] in
/-- Proposition 3.1's full conditional-law assertion for the actual synchronous
original process. The entire selected path is the conditioning variable. -/
theorem originalTag_condDistrib_eq_auxiliary (A : AllocationRule V E) (x : Profile V) :
    condDistrib (originalTagProcess A x) (fun s => originalSelection A x s.2)
      (originalPalmSourceLaw A x)
      =ᵐ[(independentMarkLaw (E := E)).map (originalSelection A x)]
        (fun j => (allocationPathLaw A x j).map (openAllocationTagProcess A x j)) := by
  let ν : Measure V := markedMeasure.map (allocationSelector A.tail A.head A.probability x)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff
      (allocationSelector_measurable A x).aemeasurable).mpr inferInstance
  have hc := condDistrib_observationMap_independent_seed_of_ae_eq ν
    (independentMarkLaw (E := E)) (originalSelection A x) (originalSelection_measurable A x)
    _ (originalMarks_condDistrib_normalized A x)
    (fun js => conditionalOriginalTagProcess A x js.1 js.2)
    (conditionalOriginalTagProcess_joint_measurable A x)
  have he : (fun s => conditionalOriginalTagProcess A x (originalSelection A x s.2) s) =
      originalTagProcess A x := by
    funext s
    exact conditionalOriginalTagProcess_observed A x s
  rw [he] at hc
  filter_upwards [hc, observedSelection_feasible_ae A x] with j hj hp
  exact hj.trans (open_marks_eq_independent_conditioned_tags A x j hp).symm

omit [DecidableEq E] in
/-- Equation (3.3) for the actual original discrepancy's regular conditional
law, simultaneously at every event count and vertex. -/
theorem originalTag_condDistrib_marginal (A : AllocationRule V E) (x : Profile V) :
    ∀ᵐ j ∂(independentMarkLaw (E := E)).map (originalSelection A x), ∀ n v,
      (condDistrib (originalTagProcess A x) (fun s => originalSelection A x s.2)
        (originalPalmSourceLaw A x) j).real {z | z n = v} =
          A.rate (selectedProfile x j n) v / Fintype.card E := by
  filter_upwards [originalTag_condDistrib_eq_auxiliary A x] with j hj n v
  rw [hj, Measure.map_congr (openAllocationTagProcess_ae A x j)]
  rw [measureReal_def, Measure.map_apply (allocationTagProcess_measurable A x j)
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)]
  exact allocationPathLaw_selected_marginal A x j n v

end GraphicalAllocation.Palm.Infinite
