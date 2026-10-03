import GraphicalAllocation.Palm.Infinite.TagLaw
import Mathlib.Probability.ProductMeasure

/-! # Synchronous tags driven by independent conditioned original marks

The deterministic tag recursion is constructed separately on an independent
initial tag and a countable product of original hidden marks. Its entire path
law is proved equal to the chronological conditional tag kernel process.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory BigOperators
namespace GraphicalAllocation.Palm.Infinite
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]

/-- Recursion driven by an initial tag and an independent mark at each update. -/
def drivenTagProcess (f : ℕ → V → Ω → V) (s : V × (ℕ → Ω)) : ℕ → V
  | 0 => s.1
  | n + 1 => f n (drivenTagProcess f s n) (s.2 n)

omit [DecidableEq V] in
lemma drivenTagProcess_measurable (f : ℕ → V → Ω → V)
    (hf : ∀ n i, Measurable (f n i)) : Measurable (drivenTagProcess f) := by
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hh : Measurable (fun s : V × Ω => f n s.1 s.2) :=
      measurable_from_prod_countable_right (hf n)
    exact hh.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

omit [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V]
  [DecidableEq V] in
lemma drivenTagProcess_cylinder (f : ℕ → V → Ω → V) (z : ℕ → V) (n : ℕ) :
    drivenTagProcess f ⁻¹' tagCylinder (fun _ => id) z n =
      {z 0} ×ˢ Set.pi (Finset.range n) (fun r => {a | f r (z r) a = z (r + 1)}) := by
  ext s
  change (∀ r, r ≤ n → drivenTagProcess f s r = z r) ↔
    s.1 = z 0 ∧ ∀ r ∈ Finset.range n, f r (z r) (s.2 r) = z (r + 1)
  simp only [Finset.mem_range]
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_le _), ?_⟩
    intro r hr
    rw [← h r (by omega)]
    exact h (r + 1) (by omega)
  · rintro ⟨hzero, hstep⟩ r hr
    induction r with
    | zero => exact hzero
    | succ r ih =>
      rw [drivenTagProcess, ih (by omega)]
      exact hstep r (by omega)

omit [DecidableEq V] in
/-- Cylinder probabilities from independent driving marks factor chronologically. -/
lemma independent_drivenTag_cylinder (ν : Measure V) (η : ℕ → Measure Ω)
    [∀ n, IsProbabilityMeasure (η n)] (f : ℕ → V → Ω → V)
    (hf : ∀ n i, Measurable (f n i)) (z : ℕ → V) (n : ℕ) :
    ((ν.prod (Measure.infinitePi η)).map (drivenTagProcess f))
      (tagCylinder (fun _ => id) z n) =
      ν {z 0} * ∏ r ∈ Finset.range n, η r {a | f r (z r) a = z (r + 1)} := by
  rw [Measure.map_apply (drivenTagProcess_measurable f hf)
    (tagCylinder_measurable _ (fun _ => measurable_id) z n),
    drivenTagProcess_cylinder, Measure.prod_prod]
  congr 1
  exact Measure.infinitePi_pi η (fun r _ => hf r _ (measurableSet_singleton _))

omit [DecidableEq V] in
/-- Equality on all point-valued tag cylinders determines a finite-state path law. -/
lemma measure_eq_of_tag_cylinder (ν ξ : Measure (ℕ → V)) [IsProbabilityMeasure ξ]
    (h : ∀ z n, ν (tagCylinder (fun _ => id) z n) =
      ξ (tagCylinder (fun _ => id) z n)) : ν = ξ := by
  apply measure_eq_of_frestrictLe
  intro n
  apply Measure.ext_of_singleton
  intro y
  let z : ℕ → V := fun r => if hr : r ≤ n then y ⟨r, Finset.mem_Iic.mpr hr⟩
    else y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have hz : ∀ r (hr : r ≤ n), z r = y ⟨r, Finset.mem_Iic.mpr hr⟩ := by
    intro r hr
    simp [z, hr]
  have he : (frestrictLe n : (ℕ → V) → (Finset.Iic n → V)) ⁻¹' {y} =
      tagCylinder (fun _ => id) z n := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, tagCylinder, mem_ofPred_eq, id_eq]
    constructor
    · intro hh r hr
      rw [hz r hr]
      exact congrFun hh ⟨r, Finset.mem_Iic.mpr hr⟩
    · intro hh
      funext r
      exact (hh r (Finset.mem_Iic.mp r.2)).trans (hz r (Finset.mem_Iic.mp r.2))
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y),
    Measure.map_apply (by fun_prop) (measurableSet_singleton y), he]
  exact h z n

omit [DecidableEq V] in
/-- An independently driven deterministic recursion has exactly its pushforward
transition-kernel path law. No process-law equality is assumed. -/
theorem independent_drivenTag_law (ν : Measure V) [IsProbabilityMeasure ν]
    (η : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (η n)]
    (f : ℕ → V → Ω → V) (hf : ∀ n i, Measurable (f n i))
    (L : ℕ → Kernel V V) [∀ n, IsMarkovKernel (L n)]
    (hL : ∀ n i, L n i = (η n).map (f n i)) :
    (ν.prod (Measure.infinitePi η)).map (drivenTagProcess f) = pathMeasure ν L := by
  apply measure_eq_of_tag_cylinder
  intro z n
  rw [independent_drivenTag_cylinder ν η f hf z n, markov_tag_cylinder]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  rw [hL, Measure.map_apply (hf r _) (measurableSet_singleton _)]
  rfl

section Allocation
open Rules Process
variable {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The actual discrepancy recursion along a prescribed base path, using the
original synchronous event and a separate initial tag. -/
def conditionalOriginalTagProcess (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    V × (ℕ → E × ℝ) → ℕ → V :=
  drivenTagProcess (fun n i a => (A.event a.1 a.2).tag (selectedProfile x j n) i)

omit [DecidableEq E] [Nonempty E] in
lemma conditionalOriginalTagProcess_measurable (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) : Measurable (conditionalOriginalTagProcess A x j) :=
  drivenTagProcess_measurable _ (fun n i => original_event_tag_measurable A (selectedProfile x j n) i)

omit [DecidableEq E] in
/-- Independent original event marks conditioned at their actual selected cells
produce exactly the conditional discrepancy path law. This is an equality of
entire infinite processes, obtained from deterministic recursion and products. -/
theorem independent_conditioned_original_tag_law (A : AllocationRule V E)
    (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    ((markedMeasure.map (allocationSelector A.tail A.head A.probability x)).prod
      (Measure.infinitePi (fun n => conditionalSelectionMeasure markedMeasure
        (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n)))).map
      (conditionalOriginalTagProcess A x j) = conditionalDiscrepancyPathLaw A x j hj := by
  let : IsProbabilityMeasure
      (markedMeasure.map (allocationSelector A.tail A.head A.probability x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (allocationSelector_measurable A x).aemeasurable).mpr inferInstance
  let : ∀ n, IsProbabilityMeasure (conditionalSelectionMeasure markedMeasure
      (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n)) :=
    fun n => ⟨conditionalSelectionMeasure_univ markedMeasure _ _ (hj n)⟩
  apply independent_drivenTag_law
  · exact fun n i => original_event_tag_measurable A _ i
  · intro n i
    rfl

omit [DecidableEq E] in
/-- Literal Palm auxiliary marks and independently driven original synchronous
tags have exactly the same full law conditional on the prescribed base path. -/
theorem open_marks_eq_independent_conditioned_tags (A : AllocationRule V E)
    (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    (allocationPathLaw A x j).map (openAllocationTagProcess A x j) =
      ((markedMeasure.map (allocationSelector A.tail A.head A.probability x)).prod
        (Measure.infinitePi (fun n => conditionalSelectionMeasure markedMeasure
          (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (j n)))).map
        (conditionalOriginalTagProcess A x j) := by
  rw [openAllocationTagProcess_law A x j hj, independent_conditioned_original_tag_law A x j hj]

end Allocation
end GraphicalAllocation.Palm.Infinite
