import GraphicalAllocation.Palm.FiniteReduction
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # The original marked edge probability space

The mark is an edge and a real number. The measure is supported on E × (0,1),
so using the ambient real line does not alter the paper's marked space.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators ENNReal
open MeasureTheory Set

/-- Lebesgue-uniform law on the open unit interval. -/
def unitMarkMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unitMarkMeasure where
  measure_univ := by simp [unitMarkMeasure]

variable {E V : Type*} [Fintype E] [Nonempty E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

/-- Each edge fiber has mass `1 / |E|`, and each fiber carries a uniform mark. -/
def markedMeasure : Measure (E × ℝ) :=
  (PMF.uniformOfFintype E).toMeasure.prod unitMarkMeasure

instance : IsProbabilityMeasure (markedMeasure (E := E)) := by
  unfold markedMeasure
  infer_instance

lemma markedMeasure_fiber (e : E) :
    markedMeasure ({e} ×ˢ (univ : Set ℝ)) = (Fintype.card E : ℝ≥0∞)⁻¹ := by
  rw [markedMeasure, Measure.prod_prod, measure_univ, mul_one,
    (PMF.uniformOfFintype E).toMeasure_apply_singleton e (measurableSet_singleton e), PMF.uniformOfFintype_apply]

omit [MeasurableSingletonClass E] in
lemma markedMeasure_supported :
    markedMeasure (E := E) (univ ×ˢ Ioo (0 : ℝ) 1) = 1 := by
  simp [markedMeasure, Measure.prod_prod, unitMarkMeasure]

/-- Selection with a fresh uniform threshold mark. -/
def thresholdMarkSelector (left right : E → V) (p : E → ℝ) (a : E × ℝ) : V :=
  if a.2 ≤ p a.1 then left a.1 else right a.1

omit [Nonempty E] in
lemma thresholdMarkSelector_measurable [MeasurableSpace V]
    (left right : E → V) (p : E → ℝ) :
    Measurable (thresholdMarkSelector left right p) := by
  apply Measurable.ite
  · exact measurableSet_le measurable_snd ((measurable_of_countable p).comp measurable_fst)
  · exact (measurable_of_countable left).comp measurable_fst
  · exact (measurable_of_countable right).comp measurable_fst

/-- All selectors on a fixed finite path, together with the edge identity,
form one finite exact signature. -/
def pathSignature {I : Type*} (left right : E → V) (p : I → E → ℝ)
    (a : E × ℝ) : E × (I → V) :=
  (a.1, fun i => thresholdMarkSelector left right (p i) a)

omit [Nonempty E] in
lemma pathSignature_measurable {I : Type*} [MeasurableSpace V]
    (left right : E → V) (p : I → E → ℝ) :
    Measurable (pathSignature left right p) := by
  exact measurable_fst.prodMk (Measurable.of_eval (fun i =>
    thresholdMarkSelector_measurable left right (p i)))

/-- The original continuous marks admit an exact finite weighted expectation
formula for every observable of the path's edge/selection signature. -/
lemma marked_integral_eq_finite_sum {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq E] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (left right : E → V) (p : I → E → ℝ) (f : (E × (I → V)) → ℝ) :
    (∫ a, f (pathSignature left right p a) ∂markedMeasure) =
      ∑ s, atomWeight markedMeasure (pathSignature left right p) s * f s :=
  integral_eq_atom_sum markedMeasure (pathSignature_measurable left right p) f

/-- Exact uniform-threshold probability, including p = 0 and p = 1. -/
lemma unitMarkMeasure_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    unitMarkMeasure.real (Iic p) = p := by
  rw [unitMarkMeasure, restrict_Ioo_eq_restrict_Ioc]
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iic]
  have hset : Iic p ∩ Ioc (0 : ℝ) 1 = Ioc 0 p := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, h.2.trans hp1⟩
  rw [hset, Real.volume_Ioc]
  simpa using ENNReal.toReal_ofReal hp0

/-- Disintegration over the finite edge coordinate, with its exact uniform weight. -/
lemma markedMeasure_real_set (s : Set (E × ℝ)) (hs : MeasurableSet s) :
    (markedMeasure (E := E)).real s =
      ∑ e, unitMarkMeasure.real ((Prod.mk e) ⁻¹' s) / Fintype.card E := by
  rw [measureReal_def, markedMeasure, Measure.prod_apply hs, lintegral_fintype,
    ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro e _
    rw [ENNReal.toReal_mul,
      (PMF.uniformOfFintype E).toMeasure_apply_singleton e (measurableSet_singleton e),
      PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    simp [measureReal_def, div_eq_mul_inv]
  · intro e _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Selection-cell probability for one edge, derived from the uniform mark. -/
lemma unitMarkMeasure_selection [DecidableEq V] (left right v : V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    unitMarkMeasure.real {u | (if u ≤ p then left else right) = v} =
      (if v = left then p else 0) + (if v = right then 1 - p else 0) := by
  by_cases hl : v = left
  · subst left
    by_cases hr : v = right
    · subst right
      simp
    · have hrv : right ≠ v := Ne.symm hr
      have heq : {u : ℝ | (if u ≤ p then v else right) = v} = Iic p := by
        ext u
        simp only [mem_ofPred_eq, mem_Iic]
        by_cases hu : u ≤ p <;> simp [hu, hrv]
      rw [heq, unitMarkMeasure_le hp0 hp1]
      simp [hr]
  · by_cases hr : v = right
    · subst right
      have hlv : left ≠ v := Ne.symm hl
      have heq : {u : ℝ | (if u ≤ p then left else v) = v} = (Iic p)ᶜ := by
        ext u
        simp only [mem_ofPred_eq, mem_compl_iff, mem_Iic]
        by_cases hu : u ≤ p <;> simp [hu, hlv]
      rw [heq, probReal_compl_eq_one_sub measurableSet_Iic, unitMarkMeasure_le hp0 hp1]
      simp [hl]
    · have heq : {u : ℝ | (if u ≤ p then left else right) = v} = ∅ := by
        ext u
        by_cases hu : u ≤ p <;> simp [hu, Ne.symm hl, Ne.symm hr]
      simp [heq, hl, hr]

end GraphicalAllocation.Palm
