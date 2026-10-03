import GraphicalAllocation.Palm.Infinite.ConditioningKernel
import GraphicalAllocation.Palm.Infinite.ConditioningLimit
import GraphicalAllocation.Palm.Infinite.ConditioningProduct

/-! # Original hidden marks conditional on the selected base path

The original source is the single infinite independent marked experiment.
First the exact conditional law of an earlier mark prefix is proved after any
longer selected-base prefix. The final identities upgrade these computations to
regular conditional distributions given the complete infinite observed path.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process

namespace GraphicalAllocation.Palm.Infinite

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Fintype V] [DecidableEq E] in
/-- All earlier hidden marks retain their independent cell-conditional laws
when an arbitrarily longer actual base history is observed. -/
theorem originalMarks_conditional_prefix (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (h n : ℕ) (hhn : h ≤ n)
    (hpos : independentMarkLaw (originalBaseCylinder A x j n) ≠ 0) :
    (normalizedRestriction independentMarkLaw (originalBaseCylinder A x j n)).map
      (Finset.range h).restrict =
    Measure.pi (fun r : Finset.range h => normalizedRestriction (markedMeasure (E := E))
      {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r}) := by
  have hp := (originalBaseCylinder_ne_zero_iff A x j n).mp hpos
  unfold normalizedRestriction
  rw [originalBaseCylinder_eq_rectangle]
  exact normalized_restrict_infinitePi_map _ _
    (fun r => allocationSelector_measurable A _ (measurableSet_singleton _))
    (Finset.range h) (Finset.range n) (Finset.range_mono hhn)
    (fun r hr => hp r (Finset.mem_range.mp hr))

/-- Undo a normalized conditional law without making any division convention
part of the probabilistic conclusion. -/
lemma restricted_map_eq_smul_of_normalized
    {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    (P : Measure Ω) [IsProbabilityMeasure P] (C : Set Ω) (X : Ω → W)
    (hX : Measurable X) (hC : P C ≠ 0) (ν : Measure W)
    (h : (normalizedRestriction P C).map X = ν) :
    (P.restrict C).map X = P C • ν := by
  rw [← h, normalizedRestriction, Measure.map_smul _ hX.aemeasurable, smul_smul,
    ENNReal.mul_inv_cancel hC (measure_ne_top _ _), one_smul]

omit [DecidableEq E] in
/-- Exact unnormalized joint factorization against every longer observed base
prefix. Impossible base histories contribute zero on both sides. -/
theorem originalMarks_joint_prefix (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (h n : ℕ) (hhn : h ≤ n) :
    ((independentMarkLaw (E := E)).restrict (originalBaseCylinder A x j n)).map
      (Finset.range h).restrict =
      independentMarkLaw (originalBaseCylinder A x j n) • conditionalPrefixKernel A x h j := by
  by_cases hp : independentMarkLaw (originalBaseCylinder A x j n) = 0
  · rw [Measure.restrict_eq_zero.mpr hp, Measure.map_zero, hp, zero_smul]
  · apply restricted_map_eq_smul_of_normalized _ _ _ (by fun_prop) hp
    rw [conditionalPrefixKernel_eq_normalized A x h j (fun r hr =>
      (originalBaseCylinder_ne_zero_iff A x j n).mp hp r (by omega))]
    exact originalMarks_conditional_prefix A x j h n hhn hp

/-- A countable-valued observation almost surely lies in a positive-mass fiber. -/
lemma ae_observed_fiber_ne_zero {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) (f : Ω → I) : ∀ᵐ ω ∂P, P {a | f a = f ω} ≠ 0 := by
  have h : ∀ i : I, ∀ᵐ ω ∂P, f ω = i → P {a | f a = i} ≠ 0 := by
    intro i
    by_cases hi : P {a | f a = i} = 0
    · filter_upwards [null_selection_ae P f i hi] with ω hω
      exact fun h => (hω h).elim
    · exact Filter.Eventually.of_forall (fun _ _ => hi)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact hω (f ω) rfl

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma originalBaseCylinder_eq_fiber (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    originalBaseCylinder A x j n =
      {ω | (Finset.range n).restrict (originalSelection A x ω) = (Finset.range n).restrict j} := by
  ext ω
  simp only [originalBaseCylinder, Set.mem_ofPred_eq]
  constructor
  · intro h
    funext r
    exact h r (Finset.mem_range.mp r.2)
  · intro h r hr
    exact congrFun h ⟨r, Finset.mem_range.mpr hr⟩

omit [DecidableEq E] in
/-- Every cell on the actually observed infinite selected path has positive
original mark probability, simultaneously for all event indices. -/
theorem originalSelection_feasible_ae (A : AllocationRule V E) (x : Profile V) :
    ∀ᵐ ω ∂(independentMarkLaw (E := E)), ∀ n,
      (markedMeasure (E := E))
        {a | allocationSelector A.tail A.head A.probability
          (selectedProfile x (originalSelection A x ω) n) a = originalSelection A x ω n} ≠ 0 := by
  rw [ae_all_iff]
  intro n
  filter_upwards [ae_observed_fiber_ne_zero (independentMarkLaw (E := E))
    (fun ω => (Finset.range (n + 1)).restrict (originalSelection A x ω))] with ω hω
  have hb : independentMarkLaw (originalBaseCylinder A x (originalSelection A x ω) (n + 1)) ≠ 0 := by
    rwa [originalBaseCylinder_eq_fiber]
  exact (originalBaseCylinder_ne_zero_iff A x _ (n + 1)).mp hb n (by omega)

omit [DecidableEq E] in
/-- Feasibility also holds under the observed-path law itself, so downstream
conditional representation theorems need no extra original-process assumption. -/
theorem observedSelection_feasible_ae (A : AllocationRule V E) (x : Profile V) :
    ∀ᵐ j ∂(independentMarkLaw (E := E)).map (originalSelection A x), ∀ n,
      (markedMeasure (E := E))
        {a | allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0 := by
  rw [ae_all_iff]
  intro n
  filter_upwards [ae_observed_fiber_ne_zero
    ((independentMarkLaw (E := E)).map (originalSelection A x))
    (Finset.range (n + 1)).restrict] with j hj
  rw [Measure.map_apply (originalSelection_measurable A x)
    (measurableSet_eq_fun (Finset.measurable_restrict _) measurable_const)] at hj
  have hb : independentMarkLaw (originalBaseCylinder A x j (n + 1)) ≠ 0 := by
    rwa [originalBaseCylinder_eq_fiber]
  exact (originalBaseCylinder_ne_zero_iff A x _ (n + 1)).mp hb n (by omega)

omit [DecidableEq E] in
/-- The genuine regular conditional law of every hidden mark prefix, given
all selected base vertices at once, is the independent product of its cell
conditions. This proves that later observations introduce no hidden-mark bias. -/
theorem originalMarks_condDistrib_prefix (A : AllocationRule V E) (x : Profile V)
    (h : ℕ) :
    condDistrib (Finset.range h).restrict (originalSelection A x)
      (independentMarkLaw (E := E)) =ᵐ[(independentMarkLaw (E := E)).map (originalSelection A x)]
        conditionalPrefixKernel A x h := by
  apply condDistrib_ae_eq_of_prefix_fiber_factorization _ _ _
    (originalSelection_measurable A x) (by fun_prop) (conditionalPrefixKernel A x h) h
  · intro j k hjk
    apply conditionalPrefixKernel_prefix
    intro r hr
    exact congrFun hjk ⟨r, Finset.mem_Iic.mpr (by omega)⟩
  · intro n hn j S hS
    have hc : {ω | frestrictLe n (originalSelection A x ω) = frestrictLe n j} =
        originalBaseCylinder A x j (n + 1) := by
      ext ω
      simp only [originalBaseCylinder, Set.mem_ofPred_eq]
      constructor
      · intro h r hr
        exact congrFun h ⟨r, Finset.mem_Iic.mpr (by omega)⟩
      · intro h
        funext r
        exact h r (by have := Finset.mem_Iic.mp r.2; omega)
    have hm := congrArg (fun ν : Measure ((Finset.range h) → E × ℝ) => ν S)
      (originalMarks_joint_prefix A x j h (n + 1) (by omega))
    rw [Measure.map_apply (by fun_prop) hS,
      Measure.restrict_apply ((Finset.measurable_restrict _) hS),
      Measure.smul_apply, smul_eq_mul] at hm
    rw [← hc] at hm
    convert hm using 1
    congr 1
    ext ω
    simp [and_comm]

/-- Independent cell-conditional marks along a complete selected base path.
The total probability convention at impossible cells has no effect almost surely. -/
def conditionalMarkPathLaw (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    Measure (ℕ → E × ℝ) :=
  Measure.infinitePi (fun n => selectionMeasure markedMeasure
    (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n))

instance conditionalMarkPathLaw_isProbability (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) : IsProbabilityMeasure (conditionalMarkPathLaw A x j) := by
  unfold conditionalMarkPathLaw
  infer_instance

omit [DecidableEq E] in
/-- The full original hidden-mark path, conditioned on the full selected-base
path, is the independent infinite product of successive cell conditions. -/
theorem originalMarks_condDistrib (A : AllocationRule V E) (x : Profile V) :
    condDistrib id (originalSelection A x) (independentMarkLaw (E := E))
      =ᵐ[(independentMarkLaw (E := E)).map (originalSelection A x)] conditionalMarkPathLaw A x := by
  have hp : ∀ h, ∀ᵐ j ∂(independentMarkLaw (E := E)).map (originalSelection A x),
      (condDistrib id (originalSelection A x) (independentMarkLaw (E := E)) j).map
        (Finset.range h).restrict = conditionalPrefixKernel A x h j := by
    intro h
    have hc := condDistrib_comp (μ := independentMarkLaw (E := E))
      (originalSelection_measurable A x).aemeasurable measurable_id.aemeasurable
      (Finset.measurable_restrict (Finset.range h) (X := fun _ : ℕ => E × ℝ))
    filter_upwards [hc, originalMarks_condDistrib_prefix A x h] with j hj hk
    rw [Kernel.map_apply _ (by fun_prop)] at hj
    exact hj.symm.trans hk
  filter_upwards [ae_all_iff.mpr hp] with j hj
  let η : ℕ → Measure (E × ℝ) := fun n => selectionMeasure markedMeasure
    (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n)
  have hproj : IsProjectiveLimit
      (condDistrib id (originalSelection A x) (independentMarkLaw (E := E)) j)
      (fun I : Finset ℕ => Measure.pi (fun i : I => η i)) := by
    apply (isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_pi η) _).mpr
    intro n
    have hh := hj (n + 1)
    rw [conditionalPrefixKernel_apply] at hh
    have haux (s : Finset ℕ) (hs : s = Finset.range (n + 1)) :
        (condDistrib id (originalSelection A x) (independentMarkLaw (E := E)) j).map s.restrict =
          Measure.pi (fun i : s => η i) := by
      subst s
      exact hh
    exact haux (Finset.Iic n) (Nat.range_succ_eq_Iic n).symm
  exact hproj.unique (Measure.isProjectiveLimit_infinitePi η)

omit [DecidableEq E] in
/-- The no-further-bias statement with the paper's literal normalized original
mark laws, without fallback conventions or any assumed path-conditioning law. -/
theorem originalMarks_condDistrib_normalized (A : AllocationRule V E) (x : Profile V) :
    condDistrib id (originalSelection A x) (independentMarkLaw (E := E))
      =ᵐ[(independentMarkLaw (E := E)).map (originalSelection A x)]
        (fun j => Measure.infinitePi (fun n => conditionalSelectionMeasure markedMeasure
          (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n))) := by
  filter_upwards [originalMarks_condDistrib A x, observedSelection_feasible_ae A x] with j hj hp
  rw [hj, conditionalMarkPathLaw]
  congr 1
  funext n
  exact selectionMeasure_eq_conditional _ _ _ (hp n)

end GraphicalAllocation.Palm.Infinite
