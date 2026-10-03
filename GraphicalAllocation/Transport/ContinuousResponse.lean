import GraphicalAllocation.Transport.Allocation
import GraphicalAllocation.Transport.Bounded
import GraphicalAllocation.Process.SemigroupLaw

/-!
# Actual continuous-time protected response

Poisson averaging of the exact allocation derivative/tag identity gives the
protected response of the actual analytic semigroup. The tag tail is the genuine
Poisson mixture of the finite-horizon tagged experiments.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules Process MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
variable (A : AllocationRule V E)

/-- The terminal bad-gap indicator, as a bounded observable. -/
def badGapObservable (M : ℝ) : Profile V →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => if gap x ≤ M - 1 then 0 else 1) 1 (fun x => by split_ifs <;> norm_num)

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [MeasurableSpace (Profile V)]
  [MeasurableSingletonClass (Profile V)] in
@[simp] theorem badGapObservable_apply (M : ℝ) (x : Profile V) :
    badGapObservable M x = if gap x ≤ M - 1 then 0 else 1 := rfl

/-- The actual rate-m Poisson mixture of source-Palm tag tails. -/
def continuousTagTail (s : ℝ≥0) (x : Profile V) (d : V → V → ℝ) (R : ℝ) : ℝ :=
  ∫ h, allocationTagTail A h x d R ∂poissonMeasure ((Fintype.card E : ℝ≥0) * s)

/-- Actual physical-time probability of the bad-gap event. -/
def continuousBadGap (s : ℝ≥0) (x : Profile V) (M : ℝ) : ℝ :=
  A.kernel.semigroup (Fintype.card E) s (badGapObservable M) x

omit [Nonempty V] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)] [DecidableEq E] in
theorem allocationTagTail_bounds (h : ℕ) (x : Profile V) (d : V → V → ℝ) (R : ℝ) :
    0 ≤ allocationTagTail A h x d R ∧ allocationTagTail A h x d R ≤ 1 := by
  unfold allocationTagTail markedTail
  constructor
  · apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg (A.kernel.nonneg x v)
    apply FiniteKernel.iterate_nonneg
    intro y
    split_ifs <;> norm_num
  · calc
      _ ≤ ∑ v, A.kernel.weight x v * 1 := by
        apply Finset.sum_le_sum
        intro v _
        apply mul_le_mul_of_nonneg_left _ (A.kernel.nonneg x v)
        have hi := (A.horizonMarks x h).tagged.iterate_mono h
          (f := fun y => if R ≤ d v y.2 then (1 : ℝ) else 0)
          (g := fun _ => (1 : ℝ)) (fun y => by split_ifs <;> norm_num) (x, v)
        simpa using hi
      _ = 1 := by simpa using A.kernel.total x

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)] in
theorem allocationBadGap_bounds (h : ℕ) (x : Profile V) (M : ℝ) :
    0 ≤ allocationBadGap A h x M ∧ allocationBadGap A h x M ≤ 1 := by
  constructor
  · exact A.kernel.iterate_nonneg h (fun y => by split_ifs <;> norm_num) x
  · have hi := A.kernel.iterate_mono h
      (f := fun y => if gap y ≤ M - 1 then (0 : ℝ) else 1)
      (g := fun _ => (1 : ℝ)) (fun y => by split_ifs <;> norm_num) x
    simpa [allocationBadGap] using hi

/-- All bounded count observables are integrable for the exact Poisson law. -/
theorem integrable_poisson_bounded (r : ℝ≥0) (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) : Integrable f (poissonMeasure r) := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) ?_⟩
  filter_upwards [] with n
  exact hf n

omit [Nonempty V] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)] [DecidableEq E] in
theorem integrable_allocationTagTail (s : ℝ≥0) (x : Profile V) (d : V → V → ℝ) (R : ℝ) :
    Integrable (fun h => allocationTagTail A h x d R)
      (poissonMeasure ((Fintype.card E : ℝ≥0) * s)) := by
  apply integrable_poisson_bounded _ _ 1
  intro h
  rw [abs_of_nonneg (allocationTagTail_bounds A h x d R).1]
  exact (allocationTagTail_bounds A h x d R).2

omit [Nonempty V] [TopologicalSpace (Profile V)] [DiscreteTopology (Profile V)]
  [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)] [DecidableEq E] in
theorem continuousTagTail_bounds (s : ℝ≥0) (x : Profile V) (d : V → V → ℝ) (R : ℝ) :
    0 ≤ continuousTagTail A s x d R ∧ continuousTagTail A s x d R ≤ 1 := by
  constructor
  · exact integral_nonneg (fun h => (allocationTagTail_bounds A h x d R).1)
  · have hi := integral_mono (integrable_allocationTagTail A s x d R)
      (integrable_const (1 : ℝ)) (fun h => (allocationTagTail_bounds A h x d R).2)
    simpa [continuousTagTail] using hi

omit [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
/-- Poisson averaging the event-count bad-gap probability gives the actual semigroup. -/
theorem integral_allocationBadGap (s : ℝ≥0) (x : Profile V) (M : ℝ) :
    (∫ h, allocationBadGap A h x M ∂poissonMeasure ((Fintype.card E : ℝ≥0) * s)) =
      continuousBadGap A s x M :=
  A.kernel.integral_poisson_iterate_eq_semigroup _ s x (badGapObservable M)

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Directional derivatives commute with the genuine Poisson expectation. -/
theorem integral_clipped_derivative (s : ℝ≥0) (x : Profile V) (i j v : V) (M : ℝ) :
    (∫ h, finiteDifference (A.kernel.iterate h (clippedContrast i j M)) x v
      ∂poissonMeasure ((Fintype.card E : ℝ≥0) * s)) =
    finiteDifference (A.kernel.semigroup (Fintype.card E) s (clippedObservable i j M)) x v := by
  have hi (y : Profile V) := integrable_poisson_bounded
    ((Fintype.card E : ℝ≥0) * s) (fun h => A.kernel.iterate h (clippedContrast i j M) y)
    1 (fun h => A.kernel.iterate_bounded h (abs_clippedContrast_le_one i j M) y)
  unfold finiteDifference
  rw [integral_sub (hi _) (hi _)]
  exact congrArg₂ (· - ·)
    (A.kernel.integral_poisson_iterate_eq_semigroup (Fintype.card E) s (raise x v) (clippedObservable i j M))
    (A.kernel.integral_poisson_iterate_eq_semigroup (Fintype.card E) s x (clippedObservable i j M))

omit [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [TopologicalSpace (Profile V)]
  [DiscreteTopology (Profile V)] [MeasurableSpace (Profile V)]
  [MeasurableSingletonClass (Profile V)] in
theorem integrable_clipped_derivative (s : ℝ≥0) (x : Profile V) (i j v : V) (M : ℝ) :
    Integrable (fun h => finiteDifference (A.kernel.iterate h (clippedContrast i j M)) x v)
      (poissonMeasure ((Fintype.card E : ℝ≥0) * s)) := by
  have hi (y : Profile V) := integrable_poisson_bounded
    ((Fintype.card E : ℝ≥0) * s) (fun h => A.kernel.iterate h (clippedContrast i j M) y)
    1 (fun h => A.kernel.iterate_bounded h (abs_clippedContrast_le_one i j M) y)
  exact (hi (raise x v)).sub (hi x)

omit [DecidableEq E] in
/-- Exact protected response at physical time, for the actual allocation semigroup. -/
theorem continuous_protected_response
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (s : ℝ≥0) (x : Profile V) :
    (1 - continuousBadGap A s x M - 2 * continuousTagTail A s x d R) / M ≤
      ∑ i, ∑ v, if d i v ≤ R then
        A.kernel.weight x v * finiteDifference
          (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M)) x v else 0 := by
  let ρ := poissonMeasure ((Fintype.card E : ℝ≥0) * s)
  have hb : Integrable (fun h => allocationBadGap A h x M) ρ := by
    apply integrable_poisson_bounded _ _ 1
    intro h
    rw [abs_of_nonneg (allocationBadGap_bounds A h x M).1]
    exact (allocationBadGap_bounds A h x M).2
  have hq : Integrable (fun h => allocationTagTail A h x d R) ρ :=
    integrable_allocationTagTail A s x d R
  have ht (i v : V) : Integrable (fun h => if d i v ≤ R then
      A.kernel.weight x v * finiteDifference
        (A.kernel.iterate h (clippedContrast i (ψ i) M)) x v else 0) ρ := by
    by_cases hh : d i v ≤ R
    · simp only [hh, ite_true]
      exact (integrable_clipped_derivative A s x i (ψ i) v M).const_mul _
    · simp only [hh, ite_false]
      exact integrable_const 0
  have hs (i : V) : Integrable (fun h => ∑ v, if d i v ≤ R then
      A.kernel.weight x v * finiteDifference
        (A.kernel.iterate h (clippedContrast i (ψ i) M)) x v else 0) ρ :=
    integrable_finsetSum _ (fun v _ => ht i v)
  have hsum : Integrable (fun h => ∑ i, ∑ v, if d i v ≤ R then
      A.kernel.weight x v * finiteDifference
        (A.kernel.iterate h (clippedContrast i (ψ i) M)) x v else 0) ρ :=
    integrable_finsetSum _ (fun i _ => hs i)
  have hlow := (((integrable_const (1 : ℝ)).sub hb).sub (hq.const_mul 2)).div_const M
  have h := integral_mono hlow hsum (fun h =>
    allocation_protected_response A d hdiag hsym htriangle ψ hR hM hsep h x)
  have hl : (∫ h, (1 - allocationBadGap A h x M - 2 * allocationTagTail A h x d R) / M ∂ρ) =
      (1 - continuousBadGap A s x M - 2 * continuousTagTail A s x d R) / M := by
    have hsub := integral_sub ((integrable_const (1 : ℝ)).sub hb) (hq.const_mul 2)
    have hsub' := integral_sub (integrable_const (1 : ℝ)) hb
    simp only [Pi.sub_apply] at hsub hsub'
    rw [integral_div, hsub, hsub', integral_const_mul]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_allocationBadGap A s x M]
    rfl
  simp only [Pi.sub_apply] at h
  rw [hl] at h
  have hu : (∫ h, (∑ i, ∑ v, if d i v ≤ R then A.kernel.weight x v * finiteDifference
      (A.kernel.iterate h (clippedContrast i (ψ i) M)) x v else 0) ∂ρ) =
      ∑ i, ∑ v, if d i v ≤ R then A.kernel.weight x v * finiteDifference
        (A.kernel.semigroup (Fintype.card E) s (clippedObservable i (ψ i) M)) x v else 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hs i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun v _ => ht i v)]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : d i v ≤ R
    · simp only [hv, ite_true, integral_const_mul]
      rw [integral_clipped_derivative A s x i (ψ i) v M]
    · simp [hv]
  rwa [hu] at h

end GraphicalAllocation.Transport
