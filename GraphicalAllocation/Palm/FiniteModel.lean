import GraphicalAllocation.Palm.Allocation

/-! # A genuine finite marked realization for a finite family of profiles -/

noncomputable section
namespace GraphicalAllocation.Process.AllocationRule

open scoped BigOperators
open MeasureTheory GraphicalAllocation.Rules GraphicalAllocation.Palm

variable {E V I : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype I] [DecidableEq I]

/-- The full finite signature retains the edge and every profile's selected endpoint. -/
abbrev finiteMarkWeight (A : AllocationRule V E) (x : I → Profile V) : (E × (I → V)) → ℝ :=
  atomWeight markedMeasure (pathSignature A.tail A.head (fun i => A.edgeProbability (x i)))

abbrev FiniteMark (A : AllocationRule V E) (x : I → Profile V) :=
  PositiveAtoms (A.finiteMarkWeight x)

/-- An actual original mark realizing each positive signature atom. -/
def finiteMarkRepresentative (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) : E × ℝ :=
  atomRepresentative markedMeasure (pathSignature_measurable A.tail A.head
    (fun i => A.edgeProbability (x i))) a

omit [DecidableEq E] [Fintype V] [DecidableEq V] [DecidableEq I] in
lemma finiteMarkRepresentative_spec (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) :
    pathSignature A.tail A.head (fun i => A.edgeProbability (x i))
      (A.finiteMarkRepresentative x a) = a.val :=
  atomRepresentative_spec markedMeasure (pathSignature_measurable A.tail A.head
    (fun i => A.edgeProbability (x i))) a

omit [DecidableEq E] [Fintype V] [DecidableEq V] [DecidableEq I] in
lemma finiteMarkRepresentative_edge (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) : (A.finiteMarkRepresentative x a).1 = a.val.1 :=
  congrArg Prod.fst (A.finiteMarkRepresentative_spec x a)

/-- The finite atom supplies a genuine monotone one-ball allocation event. -/
def finiteEvent (A : AllocationRule V E) (x : I → Profile V) (a : A.FiniteMark x) : Event V :=
  A.event (A.finiteMarkRepresentative x a).1 (A.finiteMarkRepresentative x a).2

omit [DecidableEq E] [Fintype V] [DecidableEq I] in
lemma finiteEvent_selected (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) (i : I) :
    selected (A.finiteEvent x a).first (A.finiteEvent x a).second
      (A.finiteEvent x a).selector (x i) = a.val.2 i := by
  have h := congrArg (fun s : E × (I → V) => s.2 i) (A.finiteMarkRepresentative_spec x a)
  change allocationSelector A.tail A.head A.probability (x i) (A.finiteMarkRepresentative x a) = _
  rw [allocationSelector_eq]
  exact h

omit [DecidableEq E] [MeasurableSingletonClass E] [Fintype V] [DecidableEq V]
  [MeasurableSingletonClass V] [Fintype I] [DecidableEq I] in
lemma finiteEvent_weight_pos (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) : 0 < positiveAtomWeight (A.finiteMarkWeight x) a := a.property

omit [DecidableEq E] [DecidableEq V] in
lemma finiteEvent_weight_sum (A : AllocationRule V E) (x : I → Profile V) :
    ∑ a : A.FiniteMark x, positiveAtomWeight (A.finiteMarkWeight x) a = 1 :=
  positiveAtomWeight_sum (atomWeight_nonneg _ _)
    (atomWeight_sum _ (pathSignature_measurable _ _ _))

omit [DecidableEq E] in
/-- Every profile in the family sees exactly the actual allocation kernel. -/
lemma finiteEvent_selection_weight (A : AllocationRule V E) (x : I → Profile V)
    (i : I) (v : V) :
    (∑ a : A.FiniteMark x, if selected (A.finiteEvent x a).first (A.finiteEvent x a).second
      (A.finiteEvent x a).selector (x i) = v then positiveAtomWeight (A.finiteMarkWeight x) a else 0) =
      A.kernel.weight (x i) v := by
  simp_rw [finiteEvent_selected]
  exact A.positiveFiniteSignature_kernel_weight x i v

end GraphicalAllocation.Process.AllocationRule

namespace GraphicalAllocation.Palm
open scoped BigOperators
open MeasureTheory Set
variable {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

omit [DecidableEq E] in
/-- The exact mass of a collection of edge fibers. -/
lemma markedMeasure_edge_set (T : Finset E) :
    (markedMeasure (E := E)).real ((T : Set E) ×ˢ (univ : Set ℝ)) =
      (T.card : ℝ) / Fintype.card E := by
  rw [measureReal_def, markedMeasure, Measure.prod_prod, measure_univ, mul_one,
    PMF.toMeasure_uniformOfFintype_apply (T : Set E) T.finite_toSet.measurableSet]
  simp [ENNReal.toReal_div]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Process.AllocationRule
open scoped BigOperators
open MeasureTheory GraphicalAllocation.Rules GraphicalAllocation.Palm

variable {E V I : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype I] [DecidableEq I]

omit [DecidableEq V] in
/-- Finite signature compression preserves exact edge-fiber masses, so local
energy bounds retain their graph-size normalization. -/
lemma finiteMark_edge_set_mass (A : AllocationRule V E) (x : I → Profile V) (T : Finset E) :
    (∑ a : A.FiniteMark x, if a.val.1 ∈ T then positiveAtomWeight (A.finiteMarkWeight x) a else 0) =
      (T.card : ℝ) / Fintype.card E := by
  calc
    _ = ∑ s : E × (I → V), A.finiteMarkWeight x s * (if s.1 ∈ T then 1 else 0) := by
      simpa [mul_ite] using sum_positiveAtoms (atomWeight_nonneg markedMeasure
        (pathSignature A.tail A.head (fun i => A.edgeProbability (x i))))
        (fun s : E × (I → V) => if s.1 ∈ T then (1 : ℝ) else 0)
    _ = ∫ a : E × ℝ, (if a.1 ∈ T then (1 : ℝ) else 0) ∂markedMeasure := by
      exact (integral_eq_atom_sum markedMeasure (pathSignature_measurable _ _ _)
        (fun s : E × (I → V) => if s.1 ∈ T then (1 : ℝ) else 0)).symm
    _ = (markedMeasure (E := E)).real ((T : Set E) ×ˢ Set.univ) := by
      simpa [Set.indicator] using integral_indicator_const (μ := markedMeasure (E := E))
        (1 : ℝ) (T.finite_toSet.measurableSet.prod MeasurableSet.univ)
    _ = (T.card : ℝ) / Fintype.card E := markedMeasure_edge_set T

end GraphicalAllocation.Process.AllocationRule
