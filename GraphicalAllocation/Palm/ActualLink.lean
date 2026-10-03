import GraphicalAllocation.Palm.SelectedPath
import GraphicalAllocation.Process.OriginalTag

/-!
# Palm link for the original allocation and synchronous tag

Equation (3.4) is proved for the actual global kernels, first at every exact
allocation count and then under their independently Poissonized probability
laws. The finite signature construction is used only to establish a global
one-step identity; no horizon-dependent terminal-law hypothesis is assumed.
-/

noncomputable section
namespace GraphicalAllocation.Process.AllocationRule

open Rules Palm MeasureTheory
open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable (A : AllocationRule V E)

omit [DecidableEq E] in
/-- Every selection cell in the finite reachable family has the actual
rate-normalized allocation mass. -/
lemma horizonMarks_cellMass_of_bounds (x y : Profile V) (h : ℕ)
    (hy : ∀ v, x v ≤ y v ∧ y v ≤ x v + (h + 1)) (v : V) :
    cellMass (A.horizonMarks x h).weight
      (experimentSelector (A.horizonMarks x h) y) v = A.kernel.weight y v := by
  obtain ⟨i, hi⟩ := mem_profileFamily_of_bounds x y (h + 1) (by
    intro v
    simpa only [Nat.cast_add, Nat.cast_one] using hy v)
  rw [← hi]
  exact A.finiteMarks_selectionMass (profileFamily x (h + 1)) i v

omit [DecidableEq E] in
/-- One-step Palm intertwining of the original uniform-mark synchronous tag. -/
theorem palm_originalTag_step_normalized (f : Profile V × V → ℝ) (x : Profile V) :
    (∑ i, A.kernel.weight x i * A.originalTagKernel.step f (x, i)) =
      A.kernel.step (fun y => ∑ k, A.kernel.weight y k * f (y, k)) x := by
  let F := A.horizonMarks x 1
  have hcell (y : Profile V) (hy : ∀ v, x v ≤ y v ∧ y v ≤ x v + 2) (v : V) :
      cellMass F.weight (experimentSelector F y) v = A.kernel.weight y v := by
    exact A.horizonMarks_cellMass_of_bounds x y 1 (by simpa using hy) v
  have hx (v : V) := hcell x (by intro w; constructor <;> omega) v
  have hr (j v : V) := hcell (raise x j) (by
    intro w
    have hb := raise_coordinate_bounds x j w
    constructor <;> omega) v
  have htag (i : V) : A.originalTagKernel.step f (x, i) = F.tagged.step f (x, i) := by
    simpa only [FiniteKernel.iterate_succ, FiniteKernel.iterate_zero] using
      A.horizonMarks_tagged_eq x 1 i f
  calc
    _ = ∑ i, cellMass F.weight (experimentSelector F x) i * F.tagged.step f (x, i) := by
      simp only [hx, htag]
    _ = F.base.step (fun y => ∑ k, cellMass F.weight (experimentSelector F y) k * f (y, k)) x :=
      palm_tagged_step F f x
    _ = _ := by
      rw [FiniteMarks.base_step_eq_selectionMass]
      change (∑ j, cellMass F.weight (experimentSelector F x) j *
        ∑ k, cellMass F.weight (experimentSelector F (raise x j)) k * f (raise x j, k)) = _
      simp only [hx, hr, FiniteKernel.step, kernel_next]

omit [DecidableEq E] in
/-- Multiplying the one-step probability identity by the total clock rate gives
the unnormalized rates appearing in the paper. -/
theorem palm_originalTag_step (f : Profile V × V → ℝ) (x : Profile V) :
    (∑ i, A.rate x i * A.originalTagKernel.step f (x, i)) =
      A.kernel.step (fun y => ∑ k, A.rate y k * f (y, k)) x := by
  have hm : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
  have hc (y : Profile V) (v : V) :
      (Fintype.card E : ℝ) * A.kernel.weight y v = A.rate y v := by
    rw [kernel_weight]
    field_simp
  calc
    _ = (Fintype.card E : ℝ) *
        (∑ i, A.kernel.weight x i * A.originalTagKernel.step f (x, i)) := by
      simp only [Finset.mul_sum, ← mul_assoc, hc]
    _ = (Fintype.card E : ℝ) *
        A.kernel.step (fun y => ∑ k, A.kernel.weight y k * f (y, k)) x := by
      rw [A.palm_originalTag_step_normalized]
    _ = _ := by
      simp only [FiniteKernel.step, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm]
      congr 1
      rw [← mul_assoc, hc]

omit [DecidableEq E] in
/-- Equation (3.4) after every prescribed allocation count, for the actual
original-tag kernel and arbitrary real terminal tests. -/
theorem palm_originalTag_iterate (h : ℕ) (f : Profile V × V → ℝ) (x : Profile V) :
    (∑ i, A.rate x i * A.originalTagKernel.iterate h f (x, i)) =
      A.kernel.iterate h (fun y => ∑ k, A.rate y k * f (y, k)) x := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    simp only [FiniteKernel.iterate_succ]
    rw [A.palm_originalTag_step]
    unfold FiniteKernel.step
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [ih]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- A bounded joint test remains bounded after rate-weighted summation, because
all arrival rates are nonnegative and their sum is exactly the edge count. -/
lemma palm_rate_test_bounded (f : Profile V × V → ℝ) (C : ℝ)
    (hf : ∀ y, |f y| ≤ C) (x : Profile V) :
    |∑ i, A.rate x i * f (x, i)| ≤ (Fintype.card E : ℝ) * C := by
  calc
    _ ≤ ∑ i, |A.rate x i * f (x, i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, A.rate x i * |f (x, i)| := by
      simp only [abs_mul, abs_of_nonneg (A.rate_nonneg x _)]
    _ ≤ ∑ i, A.rate x i * C := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf (x, i)) (A.rate_nonneg x i)
    _ = _ := by rw [← Finset.sum_mul, A.sum_rate]

omit [DecidableEq E] in
/-- The exact-count Palm link written as expectations under the constructed
original-tag and base probability laws. -/
theorem palm_originalTag_eventLaw (h : ℕ) (f : Profile V × V → ℝ) (x : Profile V)
    (C : ℝ) (hf : ∀ y, |f y| ≤ C) :
    (∑ i, A.rate x i *
      ∫ y, f y ∂(A.originalTagKernel.eventLaw h (x, i)).toMeasure) =
      ∫ y, (∑ k, A.rate y k * f (y, k)) ∂(A.kernel.eventLaw h x).toMeasure := by
  simp_rw [A.originalTagKernel.integral_eventLaw h _ f C hf]
  rw [A.kernel.integral_eventLaw h x _ ((Fintype.card E : ℝ) * C)
    (A.palm_rate_test_bounded f C hf)]
  exact A.palm_originalTag_iterate h f x

omit [DecidableEq E] in
/-- Independent Poissonization preserves the original-tag Palm link. The same
clock intensity is used by the joint and base laws. -/
theorem palm_originalTag_poisson (intensity time : NNReal) (f : Profile V × V → ℝ)
    (x : Profile V) (C : ℝ) (hf : ∀ y, |f y| ≤ C) :
    (∑ i, A.rate x i *
      ∫ y, f y ∂(A.originalTagKernel.continuousLaw intensity time (x, i)).toMeasure) =
      ∫ y, (∑ k, A.rate y k * f (y, k))
        ∂(A.kernel.continuousLaw intensity time x).toMeasure := by
  have hi (i : V) : Integrable (fun h => A.originalTagKernel.iterate h f (x, i))
      (ProbabilityTheory.poissonMeasure (intensity * time)) := by
    refine ⟨(measurable_of_countable _).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C) ?_⟩
    filter_upwards [] with h
    simpa only [Real.norm_eq_abs] using A.originalTagKernel.iterate_bounded h hf (x, i)
  simp_rw [A.originalTagKernel.integral_continuousLaw intensity time _ f C hf]
  rw [A.kernel.integral_continuousLaw intensity time x _ ((Fintype.card E : ℝ) * C)
    (A.palm_rate_test_bounded f C hf)]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (A.rate x i))]
  apply integral_congr_ae
  filter_upwards [] with h
  exact A.palm_originalTag_iterate h f x

omit [DecidableEq E] in
/-- Paper Equation (3.4), literally at physical time: each edge has a unit-rate
clock, so the total intensity is the number of edges. The countable profile/tag
state space makes every real test measurable; boundedness gives integrability. -/
theorem palm_originalTag_physical (time : NNReal) (f : Profile V × V → ℝ)
    (x : Profile V) (C : ℝ) (hf : ∀ y, |f y| ≤ C) :
    (∑ i, A.rate x i *
      ∫ y, f y ∂(A.originalTagKernel.continuousLaw (Fintype.card E) time (x, i)).toMeasure) =
      ∫ y, (∑ k, A.rate y k * f (y, k))
        ∂(A.kernel.continuousLaw (Fintype.card E) time x).toMeasure :=
  A.palm_originalTag_poisson (Fintype.card E) time f x C hf

end GraphicalAllocation.Process.AllocationRule
