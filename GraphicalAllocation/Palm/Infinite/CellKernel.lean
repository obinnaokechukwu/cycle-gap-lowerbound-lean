import GraphicalAllocation.Palm.Allocation
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Continuous local cell-resampling kernels

The information retained by one update is the new selection cell inside the
active union, and the entire original mark outside it. Disintegration over this
explicit information gives a Markov kernel on the original continuous mark
space, rather than on a finite approximation. Its integral operator is exactly
conditional expectation. Null fibers have the harmless version chosen by
Mathlib's regular conditional distribution.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace GraphicalAllocation.Palm.Infinite

variable {Ω V : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]

/-- Inside the active union remember the cell; outside remember the exact mark. -/
def localCode (σ : Ω → V) (S : Finset V) (a : Ω) : Bool × V × Ω :=
  if σ a ∈ S then (true, σ a, Classical.choice inferInstance) else (false, σ a, a)

omit [StandardBorelSpace Ω] [Fintype V] in
lemma localCode_measurable {σ : Ω → V} (hσ : Measurable σ) (S : Finset V) :
    Measurable (localCode σ S) := by
  apply Measurable.ite
  · exact hσ (S.measurableSet)
  · exact measurable_const.prodMk (hσ.prodMk measurable_const)
  · exact measurable_const.prodMk (hσ.prodMk measurable_id)

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V] in
lemma localCode_active_fiber (σ : Ω → V) (S : Finset V) (v : V) (hv : v ∈ S) :
    localCode σ S ⁻¹' {(true, v, Classical.choice inferInstance)} = {a | σ a = v} := by
  ext a
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, localCode]
  split_ifs with h
  · simp
  · simp only [Prod.mk.injEq, Bool.false_eq_true, false_and, false_iff]
    intro heq
    exact h (heq ▸ hv)

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V] in
lemma localCode_inactive_fiber (σ : Ω → V) (S : Finset V) (a : Ω) (ha : σ a ∉ S) :
    localCode σ S ⁻¹' {(false, σ a, a)} = {a} := by
  ext b
  simp only [mem_preimage, mem_singleton_iff, localCode]
  split_ifs with h
  · simp only [Prod.mk.injEq, Bool.true_eq_false, false_and, false_iff]
    intro heq
    exact ha (heq ▸ h)
  · simp only [Prod.mk.injEq, true_and]
    exact ⟨And.right, fun h => ⟨congrArg σ h, h⟩⟩

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The genuine continuous conditional-cell projection, with identity fibers
outside the active union. -/
def localKernel (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) : Kernel Ω Ω :=
  (condDistrib id (localCode σ S) μ).comap (localCode σ S) (localCode_measurable hσ S)

instance localKernel_isMarkov (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    IsMarkovKernel (localKernel μ σ hσ S) := by
  unfold localKernel
  infer_instance

omit [Fintype V] in
@[simp] lemma localKernel_apply (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) (a : Ω) :
    localKernel μ σ hσ S a = condDistrib id (localCode σ S) μ (localCode σ S a) := rfl

omit [Fintype V] in
/-- Pulling the conditioning kernel back along its conditioning variable leaves
the starting measure invariant. -/
lemma localKernel_preserves (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    localKernel μ σ hσ S ∘ₘ μ = μ := by
  have hc := localCode_measurable hσ S
  have hcomp : localKernel μ σ hσ S ∘ₘ μ =
      condDistrib id (localCode σ S) μ ∘ₘ (μ.map (localCode σ S)) := by
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _),
      Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hs) hc]
    rfl
  rw [hcomp, condDistrib_comp_map hc.aemeasurable aemeasurable_id, Measure.map_id]

omit [Fintype V] in
lemma localKernel_invariant (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    (localKernel μ σ hσ S).Invariant μ := localKernel_preserves μ σ hσ S

omit [Fintype V] in
/-- Exact conditional-expectation identity for every integrable observable. -/
lemma localKernel_condExp (σ : Ω → V) (hσ : Measurable σ) (S : Finset V)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap (localCode σ S) inferInstance] =ᵐ[μ]
      fun a => ∫ b, f b ∂localKernel μ σ hσ S a := by
  exact condExp_ae_eq_integral_condDistrib_id (localCode_measurable hσ S) hf

omit [Fintype V] in
/-- Thus on L² the genuine continuous kernel is the orthogonal conditional
expectation projection. This identifies the integral operator, not merely a
formal operator with an assumed representation. -/
lemma localKernel_eq_condExpL2 (σ : Ω → V) (hσ : Measurable σ) (S : Finset V)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (condExpL2 ℝ ℝ (localCode_measurable hσ S).comap_le hf.toLp : Ω → ℝ) =ᵐ[μ]
      fun a => ∫ b, f b ∂localKernel μ σ hσ S a :=
  (hf.condExpL2_ae_eq_condExp (localCode_measurable hσ S).comap_le).trans
    (localKernel_condExp μ σ hσ S (memLp_one_iff_integrable.mp
      (hf.mono_exponent (by norm_num))))

omit [Fintype V] in
/-- On every positive active cell this is literally normalized restriction of
`μ` to that cell. In particular the uniform edge/real-mark instance is the
resampling operation in the paper, not an abstract assumed transition. -/
lemma localKernel_active_cell (σ : Ω → V) (hσ : Measurable σ) (S : Finset V)
    (a : Ω) (ha : σ a ∈ S) (hpos : μ {b | σ b = σ a} ≠ 0)
    (t : Set Ω) (ht : MeasurableSet t) :
    localKernel μ σ hσ S a t =
      (μ {b | σ b = σ a})⁻¹ * μ (t ∩ {b | σ b = σ a}) := by
  have hc := localCode_measurable hσ S
  have hfiber := localCode_active_fiber σ S (σ a) ha
  have hm : μ.map (localCode σ S) {(true, σ a, Classical.choice inferInstance)} = μ {b | σ b = σ a} := by
    rw [Measure.map_apply hc (measurableSet_singleton _), hfiber]
  rw [localKernel_apply, localCode, ite_eq_left ha,
    condDistrib_apply_of_ne_zero hc measurable_id _ (hm ▸ hpos), hm,
    Measure.map_apply (hc.prodMk measurable_id) ((measurableSet_singleton _).prod ht)]
  congr 2
  ext b
  simp only [mem_preimage, mem_prod, mem_singleton_iff, id_eq, mem_inter_iff, mem_ofPred_eq]
  have hh : localCode σ S b = (true, σ a, Classical.choice inferInstance) ↔ σ b = σ a := by
    exact Set.ext_iff.mp hfiber b
  rw [hh, and_comm]

/-- The kernel retains exactly the local information used to construct it. -/
lemma localKernel_map_code (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    ∀ᵐ a ∂μ, (localKernel μ σ hσ S a).map (localCode σ S) =
      Measure.dirac (localCode σ S a) := by
  have hc := localCode_measurable hσ S
  let : Nonempty V := ⟨σ (Classical.choice inferInstance)⟩
  have h₁ := condDistrib_comp (μ := μ) (Y := id) hc.aemeasurable aemeasurable_id hc
  have h₂ := condDistrib_self (μ := μ) hc.aemeasurable
  have h : ∀ᵐ c ∂μ.map (localCode σ S),
      ((condDistrib id (localCode σ S) μ).map (localCode σ S)) c = Kernel.id c := by
    filter_upwards [h₁, h₂] with c h₁c h₂c
    exact h₁c.symm.trans h₂c
  filter_upwards [ae_of_ae_map hc.aemeasurable h] with a ha
  simpa [Kernel.map_apply _ hc, Kernel.id_apply] using ha

/-- Outside the active union the transition is the identity, up to the null-set
freedom inherent in conditional probabilities. -/
lemma localKernel_inactive (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    ∀ᵐ a ∂μ, σ a ∉ S → localKernel μ σ hσ S a = Measure.dirac a := by
  have hc := localCode_measurable hσ S
  filter_upwards [localKernel_map_code μ σ hσ S] with a ha
  intro hactive
  have ha' := congrArg (fun ν : Measure (Bool × V × Ω) => ν {localCode σ S a}) ha
  rw [Measure.map_apply hc (measurableSet_singleton _), Measure.dirac_apply_of_mem
    (Set.mem_singleton _)] at ha'
  have hsingle : localKernel μ σ hσ S a {a} = 1 := by
    simpa only [localCode, ite_eq_right hactive, localCode_inactive_fiber σ S a hactive] using ha'
  have hae : ∀ᵐ b ∂localKernel μ σ hσ S a, b = a :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton a)).mpr hsingle
  calc
    localKernel μ σ hσ S a = (localKernel μ σ hσ S a).map id := Measure.map_id.symm
    _ = (localKernel μ σ hσ S a).map (fun _ => a) := Measure.map_congr hae
    _ = Measure.dirac a := by simp

end GraphicalAllocation.Palm.Infinite
