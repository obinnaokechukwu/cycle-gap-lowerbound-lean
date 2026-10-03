import GraphicalAllocation.Palm.Infinite.Trajectory
import GraphicalAllocation.Diffusion.Neighborhood

/-! # The infinite auxiliary process on the original marked edge space

For an arbitrary fixed infinite sequence of selected base vertices, this file
constructs a probability law on all mark trajectories at once. The ambient
implementation uses `E × ℝ`; `openMarkProcess` is literally valued in
`E × (0,1)`. The two versions agree almost surely at every coordinate, so this
is an exact realization of the original uniform marked probability space.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory
open GraphicalAllocation.Rules GraphicalAllocation.Process

namespace GraphicalAllocation.Palm.Infinite

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Base profile after each event along a prescribed infinite selected path. -/
def selectedProfile (x : Profile V) (j : ℕ → V) : ℕ → Profile V
  | 0 => x
  | n + 1 => raise (selectedProfile x j n) (j n)

omit [Fintype V] [DecidableEq V] [MeasurableSingletonClass V] [Nonempty E] [DecidableEq E] in
lemma allocationSelector_measurable (A : AllocationRule V E) (x : Profile V) :
    Measurable (allocationSelector A.tail A.head A.probability x) := by
  rw [allocationSelector_eq]
  exact thresholdMarkSelector_measurable _ _ _

/-- The paper's exact continuous local cell-projection transition at event `n`.
Its active set is the actual closed neighborhood of the selected vertex. -/
def allocationMarkKernel (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (n : ℕ) : Kernel (E × ℝ) (E × ℝ) :=
  localKernel markedMeasure
    (allocationSelector A.tail A.head A.probability (selectedProfile x j (n + 1)))
    (allocationSelector_measurable A _) (A.closedNeighborhood (j n))

instance (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) (n : ℕ) :
    IsMarkovKernel (allocationMarkKernel A x j n) := by
  unfold allocationMarkKernel
  infer_instance

omit [DecidableEq E] [Fintype V] in
lemma allocationMarkKernel_preserves (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    allocationMarkKernel A x j n ∘ₘ markedMeasure = markedMeasure :=
  localKernel_preserves _ _ _ _

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- This is the stability hypothesis used in the finite-dimensional tag-law
proof, now for the actual chronological continuous selectors. -/
lemma allocationPath_outside (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) (a : E × ℝ)
    (ha : allocationSelector A.tail A.head A.probability
      (selectedProfile x j (n + 1)) a ∉ A.closedNeighborhood (j n)) :
    allocationSelector A.tail A.head A.probability (selectedProfile x j n) a =
      allocationSelector A.tail A.head A.probability (selectedProfile x j (n + 1)) a :=
  allocationSelector_unchanged_outside _ _ A.distinct _ A.probability_antitone _ _ _
    (fun e he => A.endpoints_mem_closedNeighborhood (j n) e he) a ha

/-- A single infinite-horizon mark-path law. -/
def allocationPathLaw (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    Measure (ℕ → E × ℝ) := pathMeasure markedMeasure (allocationMarkKernel A x j)

instance (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    IsProbabilityMeasure (allocationPathLaw A x j) := by
  unfold allocationPathLaw
  infer_instance

omit [DecidableEq E] [Fintype V] in
lemma allocationPathLaw_marginal (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    (allocationPathLaw A x j).map (fun ω => ω n) = markedMeasure :=
  pathMeasure_marginal _ _ (allocationMarkKernel_preserves A x j) n

omit [DecidableEq E] [Fintype V] in
lemma allocationPathLaw_supported (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) :
    ∀ᵐ ω ∂allocationPathLaw A x j, ∀ n, (ω n).2 ∈ Ioo (0 : ℝ) 1 :=
  pathMeasure_supported _ _ (allocationMarkKernel_preserves A x j)
    (univ ×ˢ Ioo (0 : ℝ) 1) (MeasurableSet.univ.prod measurableSet_Ioo)
    markedMeasure_supported |>.mono (fun _ h n => (h n).2)

omit [Fintype V] [DecidableEq E] in
/-- The precise continuous finite-dimensional restrictions of the single
infinite process, for every horizon simultaneously. -/
lemma allocationPathLaw_finite (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    (allocationPathLaw A x j).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => E × ℝ)
        (historyKernel (allocationMarkKernel A x j)) 0 n ∘ₘ
        (markedMeasure.map (MeasurableEquiv.piUnique _).symm) :=
  pathMeasure_finite _ _ n

/-- Literal mark type used by the paper. -/
abbrev OpenMark (E : Type*) := E × {u : ℝ // u ∈ Ioo (0 : ℝ) 1}

/-- Total measurable retraction onto the original mark space. Its arbitrary
value outside the unit interval is never used under the process law. -/
def toOpenMark (a : E × ℝ) : OpenMark E :=
  (a.1, ⟨if a.2 ∈ Ioo (0 : ℝ) 1 then a.2 else 1 / 2, by
    split_ifs with h
    · exact h
    · norm_num⟩)

omit [Fintype E] [Nonempty E] [DecidableEq E] [MeasurableSingletonClass E] in
lemma toOpenMark_measurable : Measurable (toOpenMark (E := E)) := by
  apply measurable_fst.prodMk
  apply Measurable.subtype_mk
  exact Measurable.ite (measurable_snd measurableSet_Ioo) measurable_snd measurable_const

/-- The literal `E × (0,1)`-valued random variable at every event index. -/
def openMarkProcess (n : ℕ) (ω : ℕ → E × ℝ) : OpenMark E := toOpenMark (ω n)

omit [Fintype E] [Nonempty E] [DecidableEq E] [MeasurableSingletonClass E] in
lemma openMarkProcess_measurable (n : ℕ) :
    Measurable (openMarkProcess (E := E) n) :=
  toOpenMark_measurable.comp (measurable_pi_apply n)

/-- Original marked law expressed on the literal open-interval type. -/
def openMarkedMeasure : Measure (OpenMark E) := markedMeasure.map toOpenMark

instance : IsProbabilityMeasure (openMarkedMeasure (E := E)) := by
  unfold openMarkedMeasure
  exact (Measure.isProbabilityMeasure_map_iff toOpenMark_measurable.aemeasurable).mpr inferInstance

omit [DecidableEq E] [Fintype V] in
/-- Every actual open-interval mark has the same original uniform law. -/
lemma openMarkProcess_law (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    (allocationPathLaw A x j).map (openMarkProcess n) = openMarkedMeasure := by
  rw [show openMarkProcess (E := E) n = toOpenMark ∘ (fun ω => ω n) from rfl,
    ← Measure.map_map toOpenMark_measurable (measurable_pi_apply n),
    allocationPathLaw_marginal]
  rfl

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Embedding the literal open marked law into the ambient space recovers
exactly the original edge-uniform times Lebesgue-uniform measure. -/
lemma openMarkedMeasure_embed :
    (openMarkedMeasure (E := E)).map (fun a => (a.1, (a.2 : ℝ))) = markedMeasure := by
  rw [openMarkedMeasure, Measure.map_map (by fun_prop) toOpenMark_measurable]
  calc
    _ = (markedMeasure (E := E)).map id := by
      apply Measure.map_congr
      have hs : ∀ᵐ a ∂markedMeasure (E := E), a ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        (mem_ae_iff_prob_eq_one (MeasurableSet.univ.prod measurableSet_Ioo)).mpr
          markedMeasure_supported
      filter_upwards [hs] with a ha
      simp [toOpenMark, ha.2]
    _ = markedMeasure := Measure.map_id

omit [DecidableEq E] [Fintype V] in
/-- The literal open-interval process and ambient process agree for all time
indices on one common probability-one set. -/
lemma openMarkProcess_embed_ae (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    ∀ᵐ ω ∂allocationPathLaw A x j,
      ∀ n, ((openMarkProcess n ω).1, ((openMarkProcess n ω).2 : ℝ)) = ω n := by
  filter_upwards [allocationPathLaw_supported A x j] with ω hω n
  simp [openMarkProcess, toOpenMark, hω n]

omit [DecidableEq E] [Fintype V] in
/-- Equation (3.3) at every event index for the infinite continuous auxiliary
process, using the original rate identity (3.1). -/
lemma allocationPathLaw_selected_marginal (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) (v : V) :
    (allocationPathLaw A x j).real {ω |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) (ω n) = v} =
      A.rate (selectedProfile x j n) v / Fintype.card E := by
  have hs := (allocationSelector_measurable A (selectedProfile x j n))
    (measurableSet_singleton v)
  rw [← A.selectionCell_measure]
  rw [← allocationPathLaw_marginal A x j n]
  simp only [measureReal_def]
  rw [Measure.map_apply (measurable_pi_apply n) hs]
  rfl

end GraphicalAllocation.Palm.Infinite
