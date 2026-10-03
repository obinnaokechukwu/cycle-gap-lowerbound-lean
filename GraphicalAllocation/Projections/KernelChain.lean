import GraphicalAllocation.Projections.Product
import GraphicalAllocation.Palm.Infinite.Trajectory
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space

/-! # Projection chains on arbitrary probability spaces

The Markov transitions are genuine Mathlib kernels on an arbitrary measurable
space. Their action on Hilbert-valued L² observables is explicitly identified
with symmetric projection operators. The endpoint probability is constructed
from chronological kernel composition, and its displacement identity is
proved by integration before applying the abstract operator inequality.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace GraphicalAllocation.Projections

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Chronological composition of actual Markov kernels. -/
def kernelProduct (K : ℕ → Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | n + 1 => K n ∘ₖ kernelProduct K n

instance (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (kernelProduct K n) := by
  induction n with
  | zero => unfold kernelProduct; infer_instance
  | succ n ih => unfold kernelProduct; infer_instance

lemma kernelProduct_preserves (μ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    (hK : ∀ n, K n ∘ₘ μ = μ) (n : ℕ) : kernelProduct K n ∘ₘ μ = μ := by
  induction n with
  | zero => exact Measure.id_comp
  | succ n ih => rw [kernelProduct, ← Measure.comp_assoc, ih, hK n]

/-- Function operators occur in reverse composition order to chronological
measure transitions. -/
def backwardOperator {L : Type*} [AddCommMonoid L] [Module ℝ L]
    (Q : ℕ → L →ₗ[ℝ] L) : ℕ → L →ₗ[ℝ] L
  | 0 => LinearMap.id
  | n + 1 => (backwardOperator Q n).comp (Q n)

lemma backwardOperator_adjoint {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (Q : ℕ → L →ₗ[ℝ] L) (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (n : ℕ) (f g : L) :
    inner ℝ f (backwardOperator Q n g) = inner ℝ (linearOrbit Q f n) g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
      change inner ℝ f (backwardOperator Q n (Q n g)) =
        inner ℝ (Q n (linearOrbit Q f n)) g
      rw [ih]
      exact ((hQ n).isSymmetric _ _).symm

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The statement that a kernel acts as a specified operator on L²: this is an
actual integral representation for every observable, not a displacement or
correlation assumption. -/
def RepresentsOnL2 (K : Kernel Ω Ω) (Q : Lp H 2 μ →ₗ[ℝ] Lp H 2 μ) : Prop :=
  ∀ f : Lp H 2 μ, (fun a => ∫ b, f b ∂K a) =ᵐ[μ] Q f

lemma backwardOperator_represents (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)]
    (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n)) (n : ℕ) :
    RepresentsOnL2 μ (kernelProduct K n) (backwardOperator Q n) := by
  intro f
  induction n generalizing f with
  | zero =>
      apply Filter.Eventually.of_forall
      intro a
      exact Kernel.integral_deterministic' measurable_id (Lp.stronglyMeasurable f)
  | succ n ih =>
      have hf : Integrable f (kernelProduct K (n + 1) ∘ₘ μ) := by
        rw [kernelProduct_preserves μ K hK]
        exact (Lp.memLp f).integrable (by norm_num)
      have hint := Measure.ae_integrable_of_integrable_comp hf
      have hrep' : ∀ᵐ a ∂μ,
          (fun b => ∫ c, f c ∂K n b) =ᵐ[kernelProduct K n a] Q n f := by
        apply Measure.ae_ae_of_ae_comp
        rw [kernelProduct_preserves μ K hK]
        exact hrep n f
      filter_upwards [hint, hrep', ih (Q n f)] with a ha hb hc
      change (∫ b, f b ∂(K n ∘ₖ kernelProduct K n) a) = backwardOperator Q n (Q n f) a
      rw [Kernel.integral_comp ha, integral_congr_ae hb]
      exact hc

/-- The actual initial/final joint law of the chronological chain. -/
def kernelEndpointLaw (K : ℕ → Kernel Ω Ω) (n : ℕ) : Measure (Ω × Ω) :=
  μ ⊗ₘ kernelProduct K n

instance (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsProbabilityMeasure (kernelEndpointLaw μ K n) := by
  unfold kernelEndpointLaw
  infer_instance

/-- Both coordinates of the endpoint joint have the reference marginal. -/
lemma kernelEndpointLaw_fst (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    MeasurePreserving Prod.fst (kernelEndpointLaw μ K n) μ :=
  ⟨measurable_fst, Measure.fst_compProd _ _⟩

lemma kernelEndpointLaw_snd (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)]
    (hK : ∀ n, K n ∘ₘ μ = μ) (n : ℕ) :
    MeasurePreserving Prod.snd (kernelEndpointLaw μ K n) μ :=
  ⟨measurable_snd, (Measure.snd_compProd _ _).trans (kernelProduct_preserves μ K hK n)⟩

omit [CompleteSpace H] in
lemma kernelEndpointLaw_integrable_inner (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (n : ℕ) (f g : Lp H 2 μ) :
    Integrable (fun z : Ω × Ω => inner ℝ (f z.1) (g z.2)) (kernelEndpointLaw μ K n) := by
  let f' := Lp.compMeasurePreserving Prod.fst (kernelEndpointLaw_fst μ K n) f
  let g' := Lp.compMeasurePreserving Prod.snd (kernelEndpointLaw_snd μ K hK n) g
  apply (L2.integrable_inner (𝕜 := ℝ) f' g').congr
  filter_upwards [Lp.coeFn_compMeasurePreserving f (kernelEndpointLaw_fst μ K n),
    Lp.coeFn_compMeasurePreserving g (kernelEndpointLaw_snd μ K hK n)] with z hf hg
  simp only [f', g', hf, hg, Function.comp_apply]

/-- Directly calculate the endpoint inner product from the actual iterated
kernel. All Fubini/integrability obligations follow from L² and the two proved
marginals. -/
lemma kernelEndpointLaw_pairing (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (n : ℕ) (f g : Lp H 2 μ) :
    (∫ z, inner ℝ (f z.1) (g z.2) ∂kernelEndpointLaw μ K n) =
      inner ℝ (linearOrbit Q f n) g := by
  rw [← backwardOperator_adjoint Q hQ n f g, L2.inner_def]
  rw [kernelEndpointLaw, Measure.integral_compProd
    (kernelEndpointLaw_integrable_inner μ K hK n f g)]
  have hg : Integrable g (kernelProduct K n ∘ₘ μ) := by
    rw [kernelProduct_preserves μ K hK]
    exact (Lp.memLp g).integrable (by norm_num)
  apply integral_congr_ae
  filter_upwards [Measure.ae_integrable_of_integrable_comp hg,
    backwardOperator_represents μ K hK Q hrep n g] with a ha hb
  rw [integral_inner ha, hb]

lemma kernelEndpointLaw_lift_inner (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (n : ℕ) (f g : Lp H 2 μ) :
    inner ℝ
      (Lp.compMeasurePreserving Prod.fst (kernelEndpointLaw_fst μ K n) f)
      (Lp.compMeasurePreserving Prod.snd (kernelEndpointLaw_snd μ K hK n) g) =
      inner ℝ (linearOrbit Q f n) g := by
  rw [L2.inner_def, ← kernelEndpointLaw_pairing μ K hK Q hQ hrep n f g]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (kernelEndpointLaw_fst μ K n),
    Lp.coeFn_compMeasurePreserving g (kernelEndpointLaw_snd μ K hK n)] with z hf hg
  simp only [hf, hg, Function.comp_apply]

/-- The stationary endpoint displacement identity on an arbitrary marked
probability space and for arbitrary Hilbert-valued L² functions. -/
lemma kernelEndpointLaw_displacement_eq (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (n : ℕ) (f : Lp H 2 μ) :
    (∫ z, ‖f z.2 - f z.1‖ ^ 2 ∂kernelEndpointLaw μ K n) =
      2 * inner ℝ f (f - linearOrbit Q f n) := by
  let f₀ := Lp.compMeasurePreserving Prod.fst (kernelEndpointLaw_fst μ K n) f
  let fₙ := Lp.compMeasurePreserving Prod.snd (kernelEndpointLaw_snd μ K hK n) f
  have hnorm : (∫ z, ‖f z.2 - f z.1‖ ^ 2 ∂kernelEndpointLaw μ K n) = ‖fₙ - f₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub fₙ f₀,
      Lp.coeFn_compMeasurePreserving f (kernelEndpointLaw_fst μ K n),
      Lp.coeFn_compMeasurePreserving f (kernelEndpointLaw_snd μ K hK n)] with z hz h₀ hₙ
    rw [hz]
    change ‖f z.2 - f z.1‖ ^ 2 = inner ℝ (fₙ z - f₀ z) (fₙ z - f₀ z)
    simp only [f₀, fₙ, h₀, hₙ, Function.comp_apply, real_inner_self_eq_norm_sq]
  rw [hnorm, norm_sub_sq_real, real_inner_comm f₀ fₙ,
    kernelEndpointLaw_lift_inner μ K hK Q hQ hrep n f f]
  simp only [f₀, fₙ, Lp.norm_compMeasurePreserving, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm (linearOrbit Q f n) f]
  ring

/-- Equation (4.2) for arbitrary invariant probability kernels whose actual
L² action is an orthogonal projection, and arbitrary Hilbert-valued L²
observables. No finiteness, atomicity, or commutativity is assumed. -/
theorem kernel_chain_displacement_le (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (f : Lp H 2 μ) (n : ℕ) :
    (∫ z, ‖f z.2 - f z.1‖ ^ 2 ∂kernelEndpointLaw μ K n) ≤
      4 * ∑ j ∈ Finset.range n, ‖f - Q j f‖ ^ 2 := by
  rw [kernelEndpointLaw_displacement_eq μ K hK Q hQ hrep n f]
  have h := linear_product_re_inner_le Q hQ f n
  simp only [RCLike.re_to_real] at h
  linarith

private lemma comp_comap_measure {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ν : Measure A) (κ : Kernel B C) {f : A → B} (hf : Measurable f) :
    κ.comap f hf ∘ₘ ν = κ ∘ₘ ν.map f := by
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

private lemma map_compProd_first {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) [IsProbabilityMeasure ν] (κ : Kernel B B) [IsMarkovKernel κ]
    (g r : A → B) (hg : Measurable g) (hr : Measurable r) :
    (ν ⊗ₘ κ.comap r hr).map (Prod.map g id) =
      (Kernel.id ∥ₖ κ) ∘ₘ (ν.map (fun a => (g a, r a))) := by
  have heq : (Kernel.id ×ₖ κ.comap r hr).map (Prod.map g id) =
      (Kernel.id ∥ₖ κ).comap (fun a => (g a, r a)) (hg.prodMk hr) := by
    rw [← Kernel.map_prod_map _ _ hg measurable_id, Kernel.id_map hg, Kernel.map_id]
    ext a : 1
    simp [Kernel.prod_apply, Kernel.parallelComp_apply, Kernel.id_apply, Kernel.deterministic_apply]
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (hg.prodMap measurable_id),
    heq, comp_comap_measure]

open GraphicalAllocation.Palm.Infinite Preorder in
/-- The endpoint law used above is exactly the endpoint pushforward of the
single Ionescu--Tulcea trajectory measure. -/
lemma pathMeasure_endpoint_law (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (pathMeasure μ K).map (fun ω => (ω 0, ω n)) = kernelEndpointLaw μ K n := by
  induction n with
  | zero =>
      rw [kernelEndpointLaw, kernelProduct, Measure.compProd_id]
      have h := congrArg (fun ν : Measure Ω => ν.map Function.diag) (pathMeasure_initial μ K)
      rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
      exact h
  | succ n ih =>
      let first : (Finset.Iic n → Ω) → Ω := fun h => h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩
      let last : (Finset.Iic n → Ω) → Ω := fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      have hfirst : Measurable first := by fun_prop
      have hlast : Measurable last := by fun_prop
      have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => Ω) (μ₀ := μ) (κ := historyKernel K) (a := n)
      change (pathMeasure μ K).map (frestrictLe n) ⊗ₘ historyKernel K n =
        (pathMeasure μ K).map (fun ω => (frestrictLe n ω, ω (n + 1))) at h
      have hm := congrArg (fun ν : Measure ((Finset.Iic n → Ω) × Ω) =>
        ν.map (Prod.map first id)) h
      change (((pathMeasure μ K).map (frestrictLe n)) ⊗ₘ (K n).comap last hlast).map
        (Prod.map first id) = _ at hm
      rw [map_compProd_first _ _ first last hfirst hlast,
        Measure.map_map (hfirst.prodMk hlast) (by fun_prop),
        Measure.map_map (hfirst.prodMap measurable_id) (by fun_prop)] at hm
      have hm' : (Kernel.id ∥ₖ K n) ∘ₘ (pathMeasure μ K).map (fun ω => (ω 0, ω n)) =
          (pathMeasure μ K).map (fun ω => (ω 0, ω (n + 1))) := hm
      rw [← hm', ih, kernelEndpointLaw, Measure.parallelComp_comp_compProd]
      rfl

open GraphicalAllocation.Palm.Infinite in
/-- The same general projection-chain inequality stated literally as an
expectation along the infinite Markov process. -/
theorem path_chain_displacement_le (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (f : Lp H 2 μ) (n : ℕ) :
    (∫ ω, ‖f (ω n) - f (ω 0)‖ ^ 2 ∂pathMeasure μ K) ≤
      4 * ∑ j ∈ Finset.range n, ‖f - Q j f‖ ^ 2 := by
  have heq : (∫ ω, ‖f (ω n) - f (ω 0)‖ ^ 2 ∂pathMeasure μ K) =
      ∫ z, ‖f z.2 - f z.1‖ ^ 2 ∂kernelEndpointLaw μ K n := by
    rw [← pathMeasure_endpoint_law μ K n]
    apply (integral_map (μ := pathMeasure μ K)
      (φ := fun (ω : ℕ → Ω) => (ω 0, ω n))
      (f := fun (z : Ω × Ω) => ‖f z.2 - f z.1‖ ^ 2) (by fun_prop) _).symm
    exact (((Lp.stronglyMeasurable f).comp_measurable measurable_snd).sub
      ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)).norm.pow 2 |>.aestronglyMeasurable
  rw [heq]
  exact kernel_chain_displacement_le μ K hK Q hQ hrep f n

open GraphicalAllocation.Palm.Infinite in
/-- Unbundled-function version, so the observable in the expectation is exactly
the supplied function rather than a chosen L² representative. -/
theorem path_chain_displacement_le_of_memLp (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ μ = μ)
    (Q : ℕ → Lp H 2 μ →ₗ[ℝ] Lp H 2 μ)
    (hQ : ∀ n, (Q n).IsSymmetricProjection)
    (hrep : ∀ n, RepresentsOnL2 μ (K n) (Q n))
    (f : Ω → H) (hf : MemLp f 2 μ) (n : ℕ) :
    (∫ ω, ‖f (ω n) - f (ω 0)‖ ^ 2 ∂pathMeasure μ K) ≤
      4 * ∑ j ∈ Finset.range n, ‖hf.toLp f - Q j (hf.toLp f)‖ ^ 2 := by
  have hcoord (k : ℕ) : ∀ᵐ ω ∂pathMeasure μ K, hf.toLp f (ω k) = f (ω k) := by
    apply ae_of_ae_map (μ := pathMeasure μ K) (f := fun (ω : ℕ → Ω) => ω k)
      (p := fun a => hf.toLp f a = f a) (measurable_pi_apply k).aemeasurable
    rw [pathMeasure_marginal μ K hK k]
    exact hf.coeFn_toLp
  have heq : (∫ ω, ‖f (ω n) - f (ω 0)‖ ^ 2 ∂pathMeasure μ K) =
      ∫ ω, ‖hf.toLp f (ω n) - hf.toLp f (ω 0)‖ ^ 2 ∂pathMeasure μ K := by
    apply integral_congr_ae
    filter_upwards [hcoord n, hcoord 0] with ω hn h₀
    rw [hn, h₀]
  rw [heq]
  exact path_chain_displacement_le μ K hK Q hQ hrep (hf.toLp f) n

section LocalCellInstantiation

open GraphicalAllocation.Palm.Infinite
variable [StandardBorelSpace Ω] [Nonempty Ω]
variable {V : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The canonical orthogonal projection onto the genuine local-cell sigma
algebra, now acting on arbitrary Hilbert-valued L² observables. -/
def localL2Projection (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    Lp H 2 μ →ₗ[ℝ] Lp H 2 μ :=
  haveI : Fact ((MeasurableSpace.comap (localCode σ S) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω)) := ⟨(localCode_measurable hσ S).comap_le⟩
  (lpMeas H ℝ (MeasurableSpace.comap (localCode σ S) inferInstance) 2 μ).starProjection.toLinearMap

omit [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [Fintype V] in
lemma localL2Projection_isSymmetricProjection (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    (localL2Projection (H := H) μ σ hσ S).IsSymmetricProjection := by
  let : Fact ((MeasurableSpace.comap (localCode σ S) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω)) := ⟨(localCode_measurable hσ S).comap_le⟩
  unfold localL2Projection
  exact Submodule.isSymmetricProjection_starProjection _

omit [Fintype V] in
/-- The local transition's L² operator representation is proved from regular
conditional distribution, not added as an allocation hypothesis. -/
lemma localL2Projection_represents (σ : Ω → V) (hσ : Measurable σ) (S : Finset V) :
    RepresentsOnL2 μ (localKernel μ σ hσ S) (localL2Projection (H := H) μ σ hσ S) := by
  intro f
  have hc := localCode_measurable hσ S
  have h₁ := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) hc.comap_le
  rw [Lp.toLp_coeFn] at h₁
  have h₂ := condExp_ae_eq_integral_condDistrib_id hc
    ((Lp.memLp f).integrable (by norm_num))
  exact (h₁.trans h₂).symm

omit [Fintype V] in
/-- The fully instantiated continuous-cell chain estimate. In particular this
applies directly to the original uniform edge/real-mark Palm construction. -/
theorem local_continuous_chain_displacement_le (σ : ℕ → Ω → V)
    (hσ : ∀ n, Measurable (σ n)) (S : ℕ → Finset V)
    (f : Ω → H) (hf : MemLp f 2 μ) (n : ℕ) :
    (∫ ω, ‖f (ω n) - f (ω 0)‖ ^ 2
      ∂pathMeasure μ (fun j => localKernel μ (σ j) (hσ j) (S j))) ≤
      4 * ∑ j ∈ Finset.range n,
        ‖hf.toLp f - localL2Projection μ (σ j) (hσ j) (S j) (hf.toLp f)‖ ^ 2 :=
  path_chain_displacement_le_of_memLp μ _
    (fun j => localKernel_preserves μ (σ j) (hσ j) (S j)) _
    (fun j => localL2Projection_isSymmetricProjection μ (σ j) (hσ j) (S j))
    (fun j => localL2Projection_represents μ (σ j) (hσ j) (S j)) f hf n

end LocalCellInstantiation

end GraphicalAllocation.Projections
