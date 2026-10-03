import GraphicalAllocation.Palm.Infinite.Conditioning
import GraphicalAllocation.Palm.Infinite.ConditioningProduct
import GraphicalAllocation.Palm.Infinite.OriginalTransition
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Measurable conditional prefix kernels for the original mark process

Finite observed histories form a countable space. Their normalized conditional
mark products therefore define genuine probability kernels. Impossible selection
cells use the original probability law as a harmless total fallback.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open GraphicalAllocation.Rules GraphicalAllocation.Process
attribute [local instance] Classical.propDecidable

namespace GraphicalAllocation.Palm.Infinite

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [DecidableEq V] [MeasurableSingletonClass V] [Nonempty E] [DecidableEq E] in
lemma allocationSelector_joint_measurable (A : AllocationRule V E) :
    Measurable (fun z : Profile V × (E × ℝ) =>
      allocationSelector A.tail A.head A.probability z.1 z.2) :=
  measurable_from_prod_countable_right (fun x => allocationSelector_measurable A x)

omit [Nonempty E] [DecidableEq E] in
lemma originalUpdate_joint_measurable (A : AllocationRule V E) :
    Measurable (fun z : Profile V × (E × ℝ) => (A.event z.2.1 z.2.2).apply z.1) := by
  apply measurable_from_prod_countable_right
  intro x
  exact (measurable_of_countable (raise x)).comp (allocationSelector_measurable A x)

omit [Nonempty E] [DecidableEq E] in
lemma originalProfile_measurable (A : AllocationRule V E) (x : Profile V) (n : ℕ) :
    Measurable (fun ω : ℕ → E × ℝ => originalProfile A x ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (originalUpdate_joint_measurable A).comp (ih.prodMk (measurable_pi_apply n))

omit [Nonempty E] [DecidableEq E] in
lemma originalSelection_coordinate_measurable (A : AllocationRule V E) (x : Profile V) (n : ℕ) :
    Measurable (fun ω : ℕ → E × ℝ => originalSelection A x ω n) :=
  (allocationSelector_joint_measurable A).comp
    ((originalProfile_measurable A x n).prodMk (measurable_pi_apply n))

omit [Nonempty E] [DecidableEq E] in
/-- The entire causally observed selected-base path is measurable. -/
lemma originalSelection_measurable (A : AllocationRule V E) (x : Profile V) :
    Measurable (originalSelection A x) :=
  Measurable.of_eval (fun n => originalSelection_coordinate_measurable A x n)

section SelectionMeasure
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditional mark law, with an explicit probability fallback on null cells. -/
def selectionMeasure (μ : Measure Ω) (old : Ω → V) (j : V) : Measure Ω :=
  if μ {a | old a = j} = 0 then μ else normalizedRestriction μ {a | old a = j}

instance selectionMeasure_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (old : Ω → V) (j : V) : IsProbabilityMeasure (selectionMeasure μ old j) := by
  unfold selectionMeasure
  split_ifs with hz
  · infer_instance
  · exact normalizedRestriction_isProbability μ _ hz

omit [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma selectionMeasure_of_pos (μ : Measure Ω) (old : Ω → V) (j : V)
    (hj : μ {a | old a = j} ≠ 0) :
    selectionMeasure μ old j = normalizedRestriction μ {a | old a = j} := by
  simp [selectionMeasure, hj]

omit [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma selectionMeasure_eq_conditional (μ : Measure Ω) (old : Ω → V) (j : V)
    (hj : μ {a | old a = j} ≠ 0) :
    selectionMeasure μ old j = conditionalSelectionMeasure μ old j := by
  rw [selectionMeasure_of_pos μ old j hj]
  rfl

end SelectionMeasure

/-- Extend a finite observed prefix; the arbitrary tail is never read by its kernel. -/
def extendSelectionPrefix (A : AllocationRule V E) (h : ℕ)
    (j : (Finset.range h) → V) (n : ℕ) : V :=
  if hn : n < h then j ⟨n, Finset.mem_range.mpr hn⟩
  else A.tail (Classical.choice (inferInstance : Nonempty E))

omit [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma extendSelectionPrefix_restrict (A : AllocationRule V E) (h : ℕ) (j : ℕ → V)
    (n : ℕ) (hn : n < h) :
    extendSelectionPrefix A h ((Finset.range h).restrict j) n = j n := by
  simp [extendSelectionPrefix, hn]

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] in
lemma selectedProfile_prefix_congr (x : Profile V) (j k : ℕ → V) (n : ℕ)
    (h : ∀ r, r < n → j r = k r) : selectedProfile x j n = selectedProfile x k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [selectedProfile, selectedProfile, h n (by omega), ih]
    exact fun r hr => h r (by omega)

/-- A finite-history-domain probability kernel; countability proves measurability. -/
def finiteConditionalPrefixKernel (A : AllocationRule V E) (x : Profile V) (h : ℕ) :
    Kernel ((Finset.range h) → V) ((Finset.range h) → E × ℝ) :=
  Kernel.ofFunOfCountable (fun j => Measure.pi (fun r : Finset.range h =>
    selectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability
        (selectedProfile x (extendSelectionPrefix A h j) r)) (j r)))

instance finiteConditionalPrefixKernel_isMarkov (A : AllocationRule V E) (x : Profile V) (h : ℕ) :
    IsMarkovKernel (finiteConditionalPrefixKernel A x h) where
  isProbabilityMeasure _ := by
    change IsProbabilityMeasure (Measure.pi _)
    infer_instance

/-- The same kernel indexed by the full observed path, depending only on its prefix. -/
def conditionalPrefixKernel (A : AllocationRule V E) (x : Profile V) (h : ℕ) :
    Kernel (ℕ → V) ((Finset.range h) → E × ℝ) :=
  (finiteConditionalPrefixKernel A x h).comap (Finset.range h).restrict (by fun_prop)

instance conditionalPrefixKernel_isMarkov (A : AllocationRule V E) (x : Profile V) (h : ℕ) :
    IsMarkovKernel (conditionalPrefixKernel A x h) := by
  unfold conditionalPrefixKernel
  infer_instance

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Exact formula at every observed path; impossible cells have the specified fallback. -/
theorem conditionalPrefixKernel_apply (A : AllocationRule V E) (x : Profile V) (h : ℕ)
    (j : ℕ → V) :
    conditionalPrefixKernel A x h j = Measure.pi (fun r : Finset.range h =>
      selectionMeasure markedMeasure
        (allocationSelector A.tail A.head A.probability (selectedProfile x j r)) (j r)) := by
  change Measure.pi _ = Measure.pi _
  congr 1
  funext r
  have hr : (r : ℕ) < h := Finset.mem_range.mp r.property
  have hp : selectedProfile x (extendSelectionPrefix A h ((Finset.range h).restrict j)) r =
      selectedProfile x j r := by
    apply selectedProfile_prefix_congr
    intro q hq
    exact extendSelectionPrefix_restrict A h j q (by omega)
  rw [hp]
  rfl

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- No later observed selection can change this finite conditional mark law. -/
theorem conditionalPrefixKernel_prefix (A : AllocationRule V E) (x : Profile V) (h : ℕ)
    (j k : ℕ → V) (hjk : ∀ r, r < h → j r = k r) :
    conditionalPrefixKernel A x h j = conditionalPrefixKernel A x h k := by
  have he : (Finset.range h).restrict j = (Finset.range h).restrict k := by
    funext r
    exact hjk r (Finset.mem_range.mp r.property)
  unfold conditionalPrefixKernel
  rw [Kernel.comap_apply, Kernel.comap_apply, he]

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- On a feasible observed history this is exactly the normalized-cell product. -/
theorem conditionalPrefixKernel_eq_normalized (A : AllocationRule V E) (x : Profile V) (h : ℕ)
    (j : ℕ → V)
    (hj : ∀ r, r < h → (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r} ≠ 0) :
    conditionalPrefixKernel A x h j = Measure.pi (fun r : Finset.range h =>
      normalizedRestriction markedMeasure
        {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r}) := by
  rw [conditionalPrefixKernel_apply]
  congr 1
  funext r
  exact selectionMeasure_of_pos _ _ _ (hj r (Finset.mem_range.mp r.property))

end GraphicalAllocation.Palm.Infinite
