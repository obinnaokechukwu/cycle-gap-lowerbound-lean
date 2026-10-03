import GraphicalAllocation.Diffusion.MarkedHilbert
import GraphicalAllocation.Diffusion.Poisson
import GraphicalAllocation.Process.FiniteAllocation

/-! # Lemma 7.1 for the actual allocation tag

The source-Palm initialization, genuine synchronous tag evolution, uniform
edge-fiber law, local geometry, selected-path averaging, and exact Poisson mean
are all instantiated here. The right-hand-side bound is never an assumption.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators NNReal
open MeasureTheory Rules Palm Process

variable {V E I : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype I] [DecidableEq I]

omit [DecidableEq E] in
lemma finiteMarks_first (A : AllocationRule V E) (family : I → Profile V)
    (a : A.FiniteMark family) :
    ((A.finiteMarks family).event a).first = A.tail a.val.1 := by
  change A.tail (A.finiteMarkRepresentative family a).1 = _
  rw [A.finiteMarkRepresentative_edge]

omit [DecidableEq E] in
lemma finiteMarks_second (A : AllocationRule V E) (family : I → Profile V)
    (a : A.FiniteMark family) :
    ((A.finiteMarks family).event a).second = A.head a.val.1 := by
  change A.head (A.finiteMarkRepresentative family a).1 = _
  rw [A.finiteMarkRepresentative_edge]

lemma finiteMarks_incident_mass (A : AllocationRule V E) (family : I → Profile V) (v : V) :
    (∑ a : A.FiniteMark family, if ((A.finiteMarks family).event a).first = v ∨
      ((A.finiteMarks family).event a).second = v then (A.finiteMarks family).weight a else 0) =
      (A.degree v : ℝ) / Fintype.card E := by
  simp_rw [finiteMarks_first, finiteMarks_second]
  have h := A.finiteMark_edge_set_mass family (A.incidentEdges v)
  rw [A.incidentEdges_card] at h
  simpa only [AllocationRule.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, AllocationRule.finiteMarks] using h

omit [DecidableEq E] in
lemma finiteMarks_initial_cellMass (A : AllocationRule V E) (family : I → Profile V)
    (i : I) (v : V) :
    cellMass (A.finiteMarks family).weight (experimentSelector (A.finiteMarks family) (family i)) v =
      A.kernel.weight (family i) v :=
  A.finiteMarks_selectionMass family i v

omit [DecidableEq E] in
lemma horizonMarks_initial_cellMass (A : AllocationRule V E) (x : Profile V) (h : ℕ) (v : V) :
    cellMass (A.horizonMarks x h).weight (experimentSelector (A.horizonMarks x h) x) v =
      A.kernel.weight x v := by
  obtain ⟨i, hi⟩ := mem_profileFamily_of_bounds x x (h + 1) (by intro v; constructor <;> omega)
  conv_lhs => arg 2; arg 2; rw [← hi]
  rw [finiteMarks_initial_cellMass, hi]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Literal second moment of the source-Palm-initialized actual allocation tag,
using the exact finite realization of the entire h-event coupled experiment. -/
def allocationHilbertMoment (A : AllocationRule V E) (x : Profile V) (h : ℕ) (f : V → H) : ℝ :=
  ∑ i, A.kernel.weight x i * (A.horizonMarks x h).tagged.iterate h
    (fun y => ‖f y.2 - f i‖ ^ 2) (x, i)

omit [InnerProductSpace ℝ H] [DecidableEq E] in
lemma allocationHilbertMoment_nonneg (A : AllocationRule V E) (x : Profile V) (h : ℕ) (f : V → H) :
    0 ≤ allocationHilbertMoment A x h f := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (A.kernel.nonneg x i)
    ((A.horizonMarks x h).tagged.iterate_nonneg h (fun y => sq_nonneg _) (x, i))

/-- Event-time form of Lemma 7.1, for every actual endpoint-local monotone rule,
starting profile, Hilbert-valued edge-Lipschitz map, and exact allocation count. -/
theorem allocation_hilbert_displacement_events (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (h : ℕ) :
    allocationHilbertMoment A x h f ≤
      2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * h / Fintype.card E + 2 * η ^ 2 := by
  have hb := marked_hilbert_displacement_le A (A.horizonMarks x h)
    (A.finiteEvent_weight_pos _) (fun a => a.val.1)
    (finiteMarks_first A _) (finiteMarks_second A _) Δ hΔ (Fintype.card E)
    (by exact_mod_cast Fintype.card_pos)
    (by
      intro v
      rw [finiteMarks_incident_mass]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hΔ v) (Nat.cast_nonneg _)) f η hedge x h
  simp_rw [horizonMarks_initial_cellMass] at hb
  unfold allocationHilbertMoment
  convert hb using 1
  ring

/-- Physical-time form of Lemma 7.1. The count law is the actual independent
Poisson clock superposition with mean m*s. -/
theorem allocation_hilbert_displacement_physical (A : AllocationRule V E)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (f : V → H) (η : ℝ) (hedge : ∀ e, ‖f (A.tail e) - f (A.head e)‖ ≤ η)
    (x : Profile V) (s : ℝ≥0) :
    (∫ h, allocationHilbertMoment A x h f
      ∂ProbabilityTheory.poissonMeasure ((Fintype.card E : ℝ≥0) * s)) ≤
      2 * η ^ 2 * (Δ : ℝ) * (Δ + 1) * s + 2 * η ^ 2 := by
  exact (poisson_event_to_physical (Fintype.card E) Fintype.card_pos s
    (fun h => allocationHilbertMoment A x h f) (2 * η ^ 2 * (Δ : ℝ) * (Δ + 1)) (2 * η ^ 2)
    (fun h => allocationHilbertMoment_nonneg A x h f)
    (fun h => allocation_hilbert_displacement_events A Δ hΔ f η hedge x h)).2

end GraphicalAllocation.Diffusion
