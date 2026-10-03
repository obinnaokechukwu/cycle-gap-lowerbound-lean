import GraphicalAllocation.Palm.Infinite.CylinderRecursion
import GraphicalAllocation.Palm.Infinite.OriginalTransition
import GraphicalAllocation.Palm.Infinite.AllocationPath

/-! # Full conditional tag law of the infinite marked Palm process

Every finite cylinder of tags read from the literal infinite mark trajectory is
identified, retaining every intermediate observation. The transition factors
are exactly the original synchronous discrepancy transitions conditional on the
selected base vertices; no marginal-only representation is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory BigOperators
namespace GraphicalAllocation.Palm.Infinite
variable {Ω V : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Chronological joint probability of all tag observations through time `n`. -/
def tagCylinderWeight (p : ℕ → Ω → V) (z : ℕ → V) : ℕ → ℝ≥0∞
  | 0 => μ {a | p 0 a = z 0}
  | n + 1 => tagCylinderWeight p z n *
      continuousTagWeight μ (p n) (p (n + 1)) (z n) (z (n + 1))

omit [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V] [IsProbabilityMeasure μ] in
lemma tagCylinderWeight_supported (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ)
    (h : μ {a | p n a = z n} = 0) : tagCylinderWeight μ p z n = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    by_cases ho : μ {a | p n a = z n} = 0
    · simp [tagCylinderWeight, ih ho]
    · have hn : μ {a | p n a = z n ∧ p (n + 1) a = z (n + 1)} = 0 :=
        measure_mono_null (fun _ ha => ha.2) h
      simp [tagCylinderWeight, continuousTagWeight, ho, hn]

omit [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V] [IsProbabilityMeasure μ] in
/-- Explicit chronological product form of the joint tag cylinder weights. -/
lemma tagCylinderWeight_product (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ) :
    tagCylinderWeight μ p z n = μ {a | p 0 a = z 0} *
      ∏ r ∈ Finset.range n, continuousTagWeight μ (p r) (p (r + 1)) (z r) (z (r + 1)) := by
  induction n with
  | zero => simp [tagCylinderWeight]
  | succ n ih => rw [tagCylinderWeight, ih, Finset.prod_range_succ, mul_assoc]

/-- The conditional-uniform invariant holds even after specifying the entire
finite history of observed tags, rather than only the final tag. -/
theorem tagLastLaw_eq_cellRestriction (p : ℕ → Ω → V)
    (hp : ∀ n, Measurable (p n)) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (z : ℕ → V) (n : ℕ) :
    tagLastLaw μ (fun r => localKernel μ (p (r + 1)) (hp (r + 1)) (S r)) p z n =
      (tagCylinderWeight μ p z n / μ {a | p n a = z n}) •
        μ.restrict {a | p n a = z n} := by
  induction n with
  | zero =>
    rw [tagLastLaw_zero μ _ p hp z, tagCylinderWeight]
    by_cases h : μ {a | p 0 a = z 0} = 0
    · rw [Measure.restrict_eq_zero.mpr h, smul_zero]
    · rw [ENNReal.div_self h (measure_ne_top μ _), one_smul]
  | succ n ih =>
    rw [tagLastLaw_succ μ _ p hp z n, ih, Measure.comp_smul,
      Measure.restrict_smul, oldCell_localKernel μ (p n) (p (n + 1))
        (hp n) (hp (n + 1)) (S n) (houtside n), smul_smul]
    by_cases h : μ {a | p n a = z n} = 0
    · simp [tagCylinderWeight, tagCylinderWeight_supported μ p z n h]
    · simp only [tagCylinderWeight, continuousTagWeight, h, ite_false, div_eq_mul_inv]
      congr 1
      ac_rfl

/-- Every finite-dimensional tag cylinder of the single infinite mark process
has exactly the chronological overlap-chain probability. -/
theorem pathMeasure_tag_cylinder (p : ℕ → Ω → V)
    (hp : ∀ n, Measurable (p n)) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (z : ℕ → V) (n : ℕ) :
    pathMeasure μ (fun r => localKernel μ (p (r + 1)) (hp (r + 1)) (S r))
      (tagCylinder p z n) = tagCylinderWeight μ p z n := by
  rw [← tagLastLaw_mass, tagLastLaw_eq_cellRestriction μ p hp S houtside,
    Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  by_cases h : μ {a | p n a = z n} = 0
  · simp [h, tagCylinderWeight_supported μ p z n h]
  · exact ENNReal.div_mul_cancel h (measure_ne_top μ _)

/-- Equality of every finite joint law against any discrete Markov chain having
the independently specified overlap rows. -/
theorem pathMeasure_tag_finite (p : ℕ → Ω → V)
    (hp : ∀ n, Measurable (p n)) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (L : ℕ → Kernel V V) [∀ n, IsMarkovKernel (L n)]
    (hL : ∀ n i k, L n i {k} = continuousTagWeight μ (p n) (p (n + 1)) i k)
    (n : ℕ) :
    (pathMeasure μ (fun r => localKernel μ (p (r + 1)) (hp (r + 1)) (S r))).map
      (fun ω => fun r : Finset.Iic n => p r (ω r)) =
    (pathMeasure (μ.map (p 0)) L).map (frestrictLe n) := by
  let : IsProbabilityMeasure (μ.map (p 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hp 0).aemeasurable).mpr inferInstance
  apply Measure.ext_of_singleton
  intro y
  let z : ℕ → V := fun r => if hr : r ≤ n then y ⟨r, Finset.mem_Iic.mpr hr⟩
    else y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩
  have hz : ∀ r (hr : r ≤ n), z r = y ⟨r, Finset.mem_Iic.mpr hr⟩ := by
    intro r hr
    simp [z, hr]
  have hleft : (fun ω : ℕ → Ω => fun r : Finset.Iic n => p r (ω r)) ⁻¹' {y} =
      tagCylinder p z n := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, tagCylinder, mem_ofPred_eq]
    constructor
    · intro h r hr
      rw [hz r hr]
      exact congrFun h ⟨r, Finset.mem_Iic.mpr hr⟩
    · intro h
      funext r
      exact (h r (Finset.mem_Iic.mp r.2)).trans (hz r (Finset.mem_Iic.mp r.2))
  have hright : (frestrictLe n : (ℕ → V) → (Finset.Iic n → V)) ⁻¹' {y} = tagCylinder (fun _ => id) z n := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, tagCylinder, mem_ofPred_eq, id_eq]
    constructor
    · intro h r hr
      rw [hz r hr]
      exact congrFun h ⟨r, Finset.mem_Iic.mpr hr⟩
    · intro h
      funext r
      exact (h r (Finset.mem_Iic.mp r.2)).trans (hz r (Finset.mem_Iic.mp r.2))
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y),
    Measure.map_apply (by fun_prop) (measurableSet_singleton y), hleft, hright,
    pathMeasure_tag_cylinder μ p hp S houtside, tagCylinderWeight_product,
    markov_tag_cylinder]
  rw [Measure.map_apply (hp 0) (measurableSet_singleton (z 0))]
  simp_rw [hL]
  rfl

/-- Initial finite restrictions determine a probability law on countable paths. -/
lemma measure_eq_of_frestrictLe {W : Type*} [MeasurableSpace W]
    (ν ξ : Measure (ℕ → W)) [IsProbabilityMeasure ξ]
    (h : ∀ n, ν.map (frestrictLe n) = ξ.map (frestrictLe n)) : ν = ξ := by
  let family : (I : Finset ℕ) → Measure (I → W) := fun I => ξ.map I.restrict
  have hf : IsProjectiveMeasureFamily (α := fun _ : ℕ => W) family := by
    intro I J hJI
    dsimp [family]
    have hr : Measurable (Finset.restrict₂ (π := fun _ : ℕ => W) hJI) :=
      Finset.measurable_restrict₂ hJI
    have hi : Measurable (I.restrict : (ℕ → W) → (I → W)) :=
      .of_eval (fun _ => measurable_pi_apply _)
    rw [Measure.map_map hr hi]
    rfl
  have hξ : IsProjectiveLimit ξ family := fun _ => rfl
  have hν : IsProjectiveLimit ν family :=
    (isProjectiveLimit_nat_iff hf ν).mpr h
  let : ∀ I, IsFiniteMeasure (family I) := fun I => by
    dsimp [family]
    infer_instance
  exact hν.unique hξ

/-- The complete infinite tag law, including all joint cylinder events. -/
theorem pathMeasure_tag_law (p : ℕ → Ω → V)
    (hp : ∀ n, Measurable (p n)) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (L : ℕ → Kernel V V) [∀ n, IsMarkovKernel (L n)]
    (hL : ∀ n i k, L n i {k} = continuousTagWeight μ (p n) (p (n + 1)) i k) :
    (pathMeasure μ (fun r => localKernel μ (p (r + 1)) (hp (r + 1)) (S r))).map
      (fun ω r => p r (ω r)) = pathMeasure (μ.map (p 0)) L := by
  let : IsProbabilityMeasure (μ.map (p 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hp 0).aemeasurable).mpr inferInstance
  apply measure_eq_of_frestrictLe
  intro n
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact pathMeasure_tag_finite μ p hp S houtside L hL n

section Allocation
open Rules Process
variable {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Read the tag from the original continuous mark at each chronological profile. -/
def allocationTagProcess (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (ω : ℕ → E × ℝ) (n : ℕ) : V :=
  allocationSelector A.tail A.head A.probability (selectedProfile x j n) (ω n)

omit [MeasurableSingletonClass V] [Fintype V] [Nonempty E] [DecidableEq E] in
lemma allocationTagProcess_measurable (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) : Measurable (allocationTagProcess A x j) :=
  .of_eval (fun n =>
    (allocationSelector_measurable A (selectedProfile x j n)).comp (measurable_pi_apply n))

/-- Independent original hidden marks, each conditioned on the next observed
base selection, drive the actual synchronous discrepancy through this law. -/
def conditionalDiscrepancyPathLaw (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    Measure (ℕ → V) :=
  pathMeasure (markedMeasure.map (allocationSelector A.tail A.head A.probability x))
    (fun n => conditionalOriginalTagKernel A (selectedProfile x j n) (j n) (hj n))

instance conditionalDiscrepancyPathLaw_isProbability (A : AllocationRule V E)
    (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    IsProbabilityMeasure (conditionalDiscrepancyPathLaw A x j hj) := by
  let : IsProbabilityMeasure
      (markedMeasure.map (allocationSelector A.tail A.head A.probability x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (allocationSelector_measurable A x).aemeasurable).mpr inferInstance
  unfold conditionalDiscrepancyPathLaw
  infer_instance

omit [DecidableEq E] in
/-- Full infinite-path equality with the genuine conditioned synchronous tag,
proved from all finite cylinders, not merely from individual time marginals. -/
theorem allocationPathLaw_tag_law (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    (allocationPathLaw A x j).map (allocationTagProcess A x j) =
      conditionalDiscrepancyPathLaw A x j hj := by
  exact pathMeasure_tag_law markedMeasure
    (fun n => allocationSelector A.tail A.head A.probability (selectedProfile x j n))
    (fun n => allocationSelector_measurable A _) (fun n => A.closedNeighborhood (j n))
    (allocationPath_outside A x j)
    (fun n => conditionalOriginalTagKernel A (selectedProfile x j n) (j n) (hj n))
    (fun n i k => conditionalOriginalTagKernel_singleton A _ _ (hj n) i k)

omit [DecidableEq E] in
/-- Every complete finite tag history has the chronological overlap-product
probability, without any feasibility assumption on the prescribed base path. -/
theorem allocationPathLaw_tag_cylinder (A : AllocationRule V E) (x : Profile V)
    (j z : ℕ → V) (n : ℕ) :
    allocationPathLaw A x j {ω | ∀ r, r ≤ n → allocationTagProcess A x j ω r = z r} =
      (markedMeasure (E := E)) {a | allocationSelector A.tail A.head A.probability x a = z 0} *
      ∏ r ∈ Finset.range n, continuousTagWeight markedMeasure
        (allocationSelector A.tail A.head A.probability (selectedProfile x j r))
        (allocationSelector A.tail A.head A.probability (selectedProfile x j (r + 1)))
        (z r) (z (r + 1)) := by
  exact (pathMeasure_tag_cylinder markedMeasure
    (fun n => allocationSelector A.tail A.head A.probability (selectedProfile x j n))
    (fun n => allocationSelector_measurable A _) (fun n => A.closedNeighborhood (j n))
    (allocationPath_outside A x j) z n).trans (tagCylinderWeight_product _ _ _ _)

/-- The literal open-interval auxiliary marks induce the same entire tag path
as their ambient realization, on a common probability-one set. -/
def openAllocationTagProcess (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (ω : ℕ → E × ℝ) (n : ℕ) : V :=
  allocationSelector A.tail A.head A.probability (selectedProfile x j n)
    ((openMarkProcess n ω).1, ((openMarkProcess n ω).2 : ℝ))

omit [DecidableEq E] [Fintype V] in
lemma openAllocationTagProcess_ae (A : AllocationRule V E) (x : Profile V) (j : ℕ → V) :
    openAllocationTagProcess A x j =ᵐ[allocationPathLaw A x j] allocationTagProcess A x j := by
  filter_upwards [openMarkProcess_embed_ae A x j] with ω hω
  funext n
  exact congrArg (allocationSelector A.tail A.head A.probability (selectedProfile x j n)) (hω n)

omit [DecidableEq E] in
/-- Proposition 3.1's literal `E × (0,1)` process has the complete conditional
synchronous-discrepancy path law. All time coordinates and joint events agree. -/
theorem openAllocationTagProcess_law (A : AllocationRule V E) (x : Profile V) (j : ℕ → V)
    (hj : ∀ n, (markedMeasure (E := E)) {a |
      allocationSelector A.tail A.head A.probability (selectedProfile x j n) a = j n} ≠ 0) :
    (allocationPathLaw A x j).map (openAllocationTagProcess A x j) =
      conditionalDiscrepancyPathLaw A x j hj := by
  rw [Measure.map_congr (openAllocationTagProcess_ae A x j)]
  exact allocationPathLaw_tag_law A x j hj

end Allocation
end GraphicalAllocation.Palm.Infinite
