import GraphicalAllocation.Process.MarkedExperiment
import GraphicalAllocation.Palm.FiniteModel

/-!
# Actual allocation has an exact finite marked realization at every horizon

The finite signature records all selectors on a box containing every reachable
profile and every one-ball perturbation. Positive signatures are represented by
genuine original marks. Thus the resulting tagged experiment is exact, with
arbitrary real rule probabilities and no approximation.
-/

noncomputable section
namespace GraphicalAllocation.Process.AllocationRule

open scoped BigOperators
open Rules Palm

variable {V E I : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype I] [DecidableEq I]
variable (A : AllocationRule V E)

/-- Independent genuine events obtained from positive selector signatures. -/
def finiteMarks (family : I → Profile V) : FiniteMarks V (A.FiniteMark family) where
  weight := positiveAtomWeight (A.finiteMarkWeight family)
  nonneg a := (A.finiteEvent_weight_pos family a).le
  total := A.finiteEvent_weight_sum family
  event := A.finiteEvent family

omit [DecidableEq E] in
@[simp] theorem finiteMarks_selectionMass (family : I → Profile V) (i : I) (v : V) :
    (A.finiteMarks family).selectionMass (family i) v = A.kernel.weight (family i) v :=
  A.finiteEvent_selection_weight family i v

omit [DecidableEq E] in
/-- The marked transition equals the actual allocation transition on the family. -/
theorem finiteMarks_step_eq (family : I → Profile V) (i : I) (f : Profile V → ℝ) :
    A.kernel.step f (family i) = (A.finiteMarks family).base.step f (family i) := by
  rw [FiniteMarks.base_step_eq_selectionMass]
  unfold FiniteKernel.step
  simp only [A.finiteMarks_selectionMass, kernel_next]

omit [DecidableEq E] in
/-- Exact h-step equality throughout a finite reachable box. -/
theorem finiteMarks_box_iterate_eq (origin : Profile V) (budget h : ℕ)
    (y : Profile V) (f : Profile V → ℝ)
    (hy : h ≤ budget ∧ ∀ v, origin v ≤ y v ∧ y v ≤ origin v + (budget - h)) :
    A.kernel.iterate h f y =
      (A.finiteMarks (profileFamily origin budget)).base.iterate h f y := by
  apply FiniteMarks.iterate_eq_on_box _ A.kernel origin budget ?_ h y f hy
  intro z hz g
  obtain ⟨i, hi⟩ := mem_profileFamily_of_bounds origin z budget hz
  rw [← hi]
  exact A.finiteMarks_step_eq _ i g

/-- One finite marked experiment works simultaneously for the base and all
one-ball-perturbed profiles through the specified horizon. -/
abbrev horizonMarks (origin : Profile V) (h : ℕ) :=
  A.finiteMarks (profileFamily origin (h + 1))

omit [DecidableEq E] in
theorem horizonMarks_base_eq (origin : Profile V) (h : ℕ) (f : Profile V → ℝ) :
    A.kernel.iterate h f origin = (A.horizonMarks origin h).base.iterate h f origin := by
  apply A.finiteMarks_box_iterate_eq
  constructor
  · omega
  · intro v
    constructor <;> omega

omit [DecidableEq E] in
theorem horizonMarks_raised_eq (origin : Profile V) (h : ℕ) (z : V) (f : Profile V → ℝ) :
    A.kernel.iterate h f (raise origin z) =
      (A.horizonMarks origin h).base.iterate h f (raise origin z) := by
  apply A.finiteMarks_box_iterate_eq
  constructor
  · omega
  · intro v
    have hb := raise_coordinate_bounds origin z v
    constructor <;> omega

omit [DecidableEq E] in
/-- Equation (2.5), now instantiated to the genuine allocation kernel rather
than an assumed coupling or abstract test-response structure. -/
theorem derivative_eq_horizon_tag (origin : Profile V) (h : ℕ) (z : V)
    (f : Profile V → ℝ) :
    A.kernel.iterate h f (raise origin z) - A.kernel.iterate h f origin =
      (A.horizonMarks origin h).tagged.iterate h
        (fun y => Rules.finiteDifference f y.1 y.2) (origin, z) := by
  rw [A.horizonMarks_raised_eq, A.horizonMarks_base_eq]
  exact (A.horizonMarks origin h).iterate_finiteDifference h f origin z

end GraphicalAllocation.Process.AllocationRule
