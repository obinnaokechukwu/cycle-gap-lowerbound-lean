import GraphicalAllocation.Process.FiniteAllocation
import GraphicalAllocation.Process.LawExpectation

/-!
# The synchronous tag driven by original uniform marks

The global tagged kernel samples the joint pair of endpoint choices at a profile
and its one-ball perturbation under the original uniform marked-edge measure.
Every horizon-dependent finite signature experiment has exactly this tagged law
on its reachable states. Thus the finite-model displacement estimates describe
the original synchronous tag, including joint observables of its base and tag.
-/

noncomputable section
namespace GraphicalAllocation.Process.AllocationRule

open Rules Palm MeasureTheory
open scoped BigOperators

variable {V E I : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype I] [DecidableEq I]
variable (A : AllocationRule V E)

/-- Both synchronous choices use the very same original edge and uniform mark. -/
def originalTagSignature (x : Profile V) (z : V) (a : E × ℝ) : V × V :=
  (allocationSelector A.tail A.head A.probability x a,
    allocationSelector A.tail A.head A.probability (raise x z) a)

omit [Fintype V] [MeasurableSingletonClass V] [DecidableEq E] [Nonempty E] in
lemma originalTagSignature_measurable (x : Profile V) (z : V) :
    Measurable (A.originalTagSignature x z) := by
  unfold originalTagSignature
  simp only [allocationSelector_eq]
  exact (thresholdMarkSelector_measurable _ _ _).prodMk
    (thresholdMarkSelector_measurable _ _ _)

/-- The tag moves to the perturbed choice exactly when its vertex was selected. -/
def tagNext (x : Profile V × V) (c : V × V) : Profile V × V :=
  (raise x.1 c.1, if x.2 = c.1 then c.2 else x.2)

/-- Global transition derived from the original mark law, independent of horizon. -/
def originalTagKernel : FiniteKernel (Profile V × V) (V × V) where
  weight x := atomWeight markedMeasure (A.originalTagSignature x.1 x.2)
  nonneg _ := atomWeight_nonneg _ _
  total x := atomWeight_sum _ (A.originalTagSignature_measurable x.1 x.2)
  next := tagNext

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The kernel's deterministic transition is the original synchronous update. -/
lemma originalTag_next (x : Profile V) (z : V) (a : E × ℝ) :
    tagNext (x, z) (A.originalTagSignature x z a) =
      ((A.event a.1 a.2).apply x, (A.event a.1 a.2).tag x z) := by
  apply Prod.ext
  · rfl
  · have ht := event_tag_given_selection (A.event a.1 a.2) x
      (allocationSelector A.tail A.head A.probability x a) z rfl
    change (if z = allocationSelector A.tail A.head A.probability x a then
      allocationSelector A.tail A.head A.probability (raise x z) a else z) = _
    rw [ht]
    split_ifs with hz
    · subst z
      rfl
    · rfl

omit [DecidableEq E] in
/-- One original uniform-mark step, as an integral over the literal marked space. -/
theorem originalTag_step_eq_integral (f : Profile V × V → ℝ) (x : Profile V) (z : V) :
    A.originalTagKernel.step f (x, z) =
      ∫ a : E × ℝ, f ((A.event a.1 a.2).apply x, (A.event a.1 a.2).tag x z)
        ∂markedMeasure := by
  unfold FiniteKernel.step originalTagKernel
  rw [← integral_eq_atom_sum markedMeasure (A.originalTagSignature_measurable x z)
    (fun c => f (tagNext (x, z) c))]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [A.originalTag_next]

omit [DecidableEq E] in
/-- Signature compression preserves the joint base/tag transition whenever both
profiles used by the synchronous update belong to the finite family. -/
theorem finiteMarks_tagged_step_eq (family : I → Profile V) (x : Profile V) (z : V)
    (i j : I) (hi : family i = x) (hj : family j = raise x z)
    (f : Profile V × V → ℝ) :
    A.originalTagKernel.step f (x, z) = (A.finiteMarks family).tagged.step f (x, z) := by
  let g : (E × (I → V)) → ℝ := fun s => f (tagNext (x, z) (s.2 i, s.2 j))
  have horiginal : A.originalTagKernel.step f (x, z) =
      ∫ a : E × ℝ, g (pathSignature A.tail A.head
        (fun k => A.edgeProbability (family k)) a) ∂markedMeasure := by
    unfold FiniteKernel.step originalTagKernel
    rw [← integral_eq_atom_sum markedMeasure (A.originalTagSignature_measurable x z)
      (fun c => f (tagNext (x, z) c))]
    apply integral_congr_ae
    filter_upwards [] with a
    simp only [g, pathSignature, hi, hj, originalTagSignature,
      allocationSelector_eq]
    rfl
  rw [horiginal, integral_eq_atom_sum markedMeasure (pathSignature_measurable _ _ _) g,
    ← sum_positiveAtoms (atomWeight_nonneg markedMeasure
      (pathSignature A.tail A.head (fun k => A.edgeProbability (family k)))) g]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have hbase := A.finiteEvent_selected family a i
  have hraised := A.finiteEvent_selected family a j
  rw [hi] at hbase
  rw [hj] at hraised
  have htag := event_tag_given_selection (A.finiteEvent family a) x (a.val.2 i) z hbase
  change f (tagNext (x, z) (a.val.2 i, a.val.2 j)) =
    f ((A.finiteEvent family a).apply x, (A.finiteEvent family a).tag x z)
  congr 1
  apply Prod.ext
  · change raise x (a.val.2 i) = raise x
      (selected (A.finiteEvent family a).first (A.finiteEvent family a).second
        (A.finiteEvent family a).selector x)
    rw [hbase]
  · change (if z = a.val.2 i then a.val.2 j else z) = _
    rw [htag]
    split_ifs with hz
    · subst z
      exact hraised.symm
    · rfl

omit [DecidableEq E] in
/-- Full joint-law equality at each finite horizon for every terminal observable.
The original kernel is fixed; only the exact finite representation depends on h. -/
theorem horizonMarks_tagged_eq (origin : Profile V) (h : ℕ) (z : V)
    (f : Profile V × V → ℝ) :
    A.originalTagKernel.iterate h f (origin, z) =
      (A.horizonMarks origin h).tagged.iterate h f (origin, z) := by
  let region : ℕ → Profile V × V → Prop := fun n y =>
    n ≤ h ∧ ∀ v, origin v ≤ y.1 v ∧ y.1 v ≤ origin v + (h - n)
  apply FiniteKernel.iterate_eq_of_region A.originalTagKernel
    (A.horizonMarks origin h).tagged region ?_ ?_ h f (origin, z) ?_
  · intro n y hy a
    change n ≤ h ∧ ∀ v, origin v ≤ ((A.horizonMarks origin h).event a).apply y.1 v ∧
      ((A.horizonMarks origin h).event a).apply y.1 v ≤ origin v + (h - n)
    constructor
    · omega
    · intro v
      have hb := hy.2 v
      have he := event_coordinate_bounds ((A.horizonMarks origin h).event a) y.1 v
      have hn := hy.1
      constructor <;> omega
  · intro n y hy g
    obtain ⟨i, hi⟩ := mem_profileFamily_of_bounds origin y.1 (h + 1) (by
      intro v
      have hv := hy.2 v
      constructor <;> omega)
    obtain ⟨j, hj⟩ := mem_profileFamily_of_bounds origin (raise y.1 y.2) (h + 1) (by
      intro v
      have hv := hy.2 v
      have hr := raise_coordinate_bounds y.1 y.2 v
      constructor <;> omega)
    exact A.finiteMarks_tagged_step_eq (profileFamily origin (h + 1)) y.1 y.2 i j hi hj g
  · constructor
    · rfl
    · intro v
      constructor <;> simp

omit [DecidableEq E] in
/-- The original synchronous tag gives the same derivative identity at all counts. -/
theorem derivative_eq_original_tag (origin : Profile V) (h : ℕ) (z : V)
    (f : Profile V → ℝ) :
    A.kernel.iterate h f (raise origin z) - A.kernel.iterate h f origin =
      A.originalTagKernel.iterate h (fun y => finiteDifference f y.1 y.2) (origin, z) := by
  rw [A.horizonMarks_tagged_eq]
  exact A.derivative_eq_horizon_tag origin h z f


omit [DecidableEq E] in
/-- Equation (2.4) for the original synchronous tag and every bounded test,
expressed directly under the independently Poissonized process laws. -/
theorem derivative_eq_original_tag_physical (origin : Profile V) (z : V)
    (rate time : NNReal) (f : Profile V → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    (∫ y, f y ∂(A.kernel.continuousLaw rate time (raise origin z)).toMeasure) -
      (∫ y, f y ∂(A.kernel.continuousLaw rate time origin).toMeasure) =
      ∫ y, finiteDifference f y.1 y.2
        ∂(A.originalTagKernel.continuousLaw rate time (origin, z)).toMeasure := by
  have hdf : ∀ y : Profile V × V, |finiteDifference f y.1 y.2| ≤ 2 * C := by
    intro y
    exact (abs_sub (f (raise y.1 y.2)) (f y.1)).trans (by linarith [hf (raise y.1 y.2), hf y.1])
  have hi (x : Profile V) : Integrable (fun h => A.kernel.iterate h f x)
      (ProbabilityTheory.poissonMeasure (rate * time)) := by
    refine ⟨(measurable_of_countable _).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C) ?_⟩
    filter_upwards [] with h
    simpa only [Real.norm_eq_abs] using A.kernel.iterate_bounded h hf x
  rw [A.kernel.integral_continuousLaw rate time (raise origin z) f C hf,
    A.kernel.integral_continuousLaw rate time origin f C hf,
    A.originalTagKernel.integral_continuousLaw rate time (origin, z)
      (fun y => finiteDifference f y.1 y.2) (2 * C) hdf,
    ← integral_sub (hi (raise origin z)) (hi origin)]
  apply integral_congr_ae
  filter_upwards [] with h
  exact A.derivative_eq_original_tag origin h z f

end GraphicalAllocation.Process.AllocationRule
