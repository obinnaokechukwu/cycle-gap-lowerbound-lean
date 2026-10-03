import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.CondDistrib

/-! # Identifying conditioning on an entire infinite observed path

Equality of all sufficiently long finite observed-prefix joint laws determines
one joint law with the entire infinite observation. Consequently, finite-prefix
calculations identify the regular conditional distribution given that entire
path, rather than only a conditional distribution given a fixed prefix.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory

namespace GraphicalAllocation.Palm.Infinite

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

private lemma pathMeasure_eq_of_finite_prefix {A : Type*} [MeasurableSpace A]
    (ν ξ : Measure (ℕ → A)) [IsFiniteMeasure ξ]
    (h : ∀ n, ν.map (frestrictLe n) = ξ.map (frestrictLe n)) : ν = ξ := by
  let family : (I : Finset ℕ) → Measure (I → A) := fun I => ξ.map I.restrict
  have hf : IsProjectiveMeasureFamily (α := fun _ : ℕ => A) family := by
    intro I J hJI
    dsimp [family]
    have hr : Measurable (Finset.restrict₂ (π := fun _ : ℕ => A) hJI) :=
      Finset.measurable_restrict₂ hJI
    have hi : Measurable (I.restrict : (ℕ → A) → (I → A)) :=
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

/-- Finite observed-prefix joint laws determine a joint law of a whole path
and a single hidden observable. No countability assumption on the hidden
observable, and no finiteness assumption on the observed state space, is needed. -/
lemma measure_eq_of_joint_frestrictLe
    (ν ξ : Measure ((ℕ → V) × W)) [IsProbabilityMeasure ξ]
    (h : ∀ n, ν.map (fun yz => (frestrictLe n yz.1, yz.2)) =
      ξ.map (fun yz => (frestrictLe n yz.1, yz.2))) : ν = ξ := by
  let encode : ((ℕ → V) × W) → (ℕ → V × W) := fun yz n => (yz.1 n, yz.2)
  let decode : (ℕ → V × W) → ((ℕ → V) × W) := fun z => (fun n => (z n).1, (z 0).2)
  have he : Measurable encode := by fun_prop
  have hd : Measurable decode := by fun_prop
  have heq : ν.map encode = ξ.map encode := by
    apply pathMeasure_eq_of_finite_prefix
    intro n
    let encodeFin : ((Finset.Iic n → V) × W) → (Finset.Iic n → V × W) :=
      fun yz r => (yz.1 r, yz.2)
    have hf : Measurable encodeFin := by fun_prop
    have hh := congrArg (fun ρ => Measure.map encodeFin ρ) (h n)
    rw [Measure.map_map hf (by fun_prop), Measure.map_map hf (by fun_prop)] at hh
    rw [Measure.map_map (by fun_prop) he, Measure.map_map (by fun_prop) he]
    exact hh
  have hh := congrArg (fun ρ => Measure.map decode ρ) heq
  rw [Measure.map_map hd he, Measure.map_map hd he] at hh
  change ν.map id = ξ.map id at hh
  simpa only [Measure.map_id] using hh

/-- It suffices to identify the joint laws for prefixes longer than any fixed
threshold. Shorter prefixes follow by taking a further marginal. -/
lemma measure_eq_of_joint_frestrictLe_from
    (ν ξ : Measure ((ℕ → V) × W)) [IsProbabilityMeasure ξ] (horizon : ℕ)
    (h : ∀ n, horizon ≤ n →
      ν.map (fun yz => (frestrictLe n yz.1, yz.2)) =
      ξ.map (fun yz => (frestrictLe n yz.1, yz.2))) : ν = ξ := by
  apply measure_eq_of_joint_frestrictLe
  intro n
  let m := max horizon n
  have hnm : Finset.Iic n ⊆ Finset.Iic m :=
    Finset.Iic_subset_Iic.mpr (le_max_right horizon n)
  let truncate : ((Finset.Iic m → V) × W) → ((Finset.Iic n → V) × W) :=
    fun yz => (Finset.restrict₂ (π := fun _ : ℕ => V) hnm yz.1, yz.2)
  have ht : Measurable truncate := by
    exact (Finset.measurable_restrict₂ (X := fun _ : ℕ => V) hnm |>.comp measurable_fst).prodMk measurable_snd
  have hh := congrArg (fun ρ => Measure.map truncate ρ) (h m (le_max_left horizon n))
  rw [Measure.map_map ht (by fun_prop), Measure.map_map ht (by fun_prop)] at hh
  exact hh

/-- On a product with countable measurable left coordinates, singleton
rectangles determine the entire measure. The right coordinate need not be
countable. -/
lemma measure_eq_of_left_singleton_products {A B : Type*}
    [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]
    [MeasurableSpace B] (ν ξ : Measure (A × B))
    (h : ∀ a S, MeasurableSet S → ν ({a} ×ˢ S) = ξ ({a} ×ˢ S)) : ν = ξ := by
  apply Measure.ext
  intro S hS
  have hu : (⋃ a : A, ({a} ×ˢ (Prod.mk a ⁻¹' S))) = S := by
    ext p
    simp
  have hd : Pairwise (fun a b : A =>
      Disjoint ({a} ×ˢ (Prod.mk a ⁻¹' S)) ({b} ×ˢ (Prod.mk b ⁻¹' S))) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro p hp hq
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hp hq
    exact hab (hp.1.symm.trans hq.1)
  have hm : ∀ a : A, MeasurableSet ({a} ×ˢ (Prod.mk a ⁻¹' S)) :=
    fun a => (measurableSet_singleton a).prod (hS.preimage measurable_prodMk_left)
  rw [← hu, measure_iUnion hd hm, measure_iUnion hd hm]
  congr 1
  funext a
  exact h a _ (hS.preimage measurable_prodMk_left)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A scalar factorization on each countable observed fiber identifies the
joint pushforward against a kernel that is constant on those fibers. -/
lemma jointLaw_eq_compProd_map_of_fiber_factorization
    {A B : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]
    [MeasurableSpace B] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → B) (X : Ω → W) (hY : Measurable Y) (hX : Measurable X)
    (q : B → A) (hq : Measurable q) (hq_surj : Function.Surjective q)
    (κ : Kernel B W) [IsMarkovKernel κ]
    (hconst : ∀ y z, q y = q z → κ y = κ z)
    (hfactor : ∀ y S, MeasurableSet S →
      P {ω | q (Y ω) = q y ∧ X ω ∈ S} =
        P {ω | q (Y ω) = q y} * κ y S) :
    P.map (fun ω => (q (Y ω), X ω)) =
      ((P.map Y) ⊗ₘ κ).map (fun yz => (q yz.1, yz.2)) := by
  apply measure_eq_of_left_singleton_products
  intro a S hS
  obtain ⟨y, rfl⟩ := hq_surj a
  have hf : MeasurableSet {z | q z = q y} :=
    (measurableSet_singleton (q y)).preimage hq
  rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton (q y)).prod hS),
    Measure.map_apply (by fun_prop) ((measurableSet_singleton (q y)).prod hS)]
  change P {ω | q (Y ω) = q y ∧ X ω ∈ S} =
    (P.map Y ⊗ₘ κ) ({z | q z = q y} ×ˢ S)
  rw [hfactor y S hS, Measure.compProd_apply_prod hf hS]
  have hc : (∫⁻ z in {z | q z = q y}, κ z S ∂P.map Y) =
      ∫⁻ _z in {z | q z = q y}, κ y S ∂P.map Y := by
    apply setLIntegral_congr_fun hf
    intro z hz
    exact congrArg (fun μ : Measure W => μ S) (hconst z y hz)
  rw [hc, lintegral_const, Measure.restrict_apply_univ, Measure.map_apply hY hf]
  exact mul_comm _ _

/-- A measurable probability kernel satisfying every sufficiently long finite
observed-prefix joint identity is the conditional law given the entire infinite
observed path. This is the finite-to-infinite conditioning step: the hypothesis
contains only finite observed prefixes, whereas the conclusion conditions on
all coordinates at once. -/
theorem condDistrib_ae_eq_of_joint_frestrictLe
    [StandardBorelSpace W] [Nonempty W]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → (ℕ → V)) (X : Ω → W) (hY : Measurable Y) (hX : Measurable X)
    (κ : Kernel (ℕ → V) W) [IsMarkovKernel κ] (horizon : ℕ)
    (h : ∀ n, horizon ≤ n →
      P.map (fun ω => (frestrictLe n (Y ω), X ω)) =
        ((P.map Y) ⊗ₘ κ).map (fun yz => (frestrictLe n yz.1, yz.2))) :
    condDistrib X Y P =ᵐ[P.map Y] κ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY hX
  apply measure_eq_of_joint_frestrictLe_from _ _ horizon
  intro n hn
  rw [Measure.map_map (by fun_prop) (hY.prodMk hX)]
  exact h n hn

/-- A directly usable whole-path conditioning theorem from finite cylinder
factorizations. The candidate kernel only reads the first `horizon + 1`
observations, but the conclusion conditions on the entire infinite path.
The factorization must hold for every later observed prefix; this explicitly
rules out bias from any finite amount of future observation. -/
theorem condDistrib_ae_eq_of_prefix_fiber_factorization
    [Countable V] [MeasurableSingletonClass V]
    [StandardBorelSpace W] [Nonempty W]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → (ℕ → V)) (X : Ω → W) (hY : Measurable Y) (hX : Measurable X)
    (κ : Kernel (ℕ → V) W) [IsMarkovKernel κ] (horizon : ℕ)
    (hconst : ∀ y z, frestrictLe horizon y = frestrictLe horizon z → κ y = κ z)
    (hfactor : ∀ n, horizon ≤ n → ∀ y S, MeasurableSet S →
      P {ω | frestrictLe n (Y ω) = frestrictLe n y ∧ X ω ∈ S} =
        P {ω | frestrictLe n (Y ω) = frestrictLe n y} * κ y S) :
    condDistrib X Y P =ᵐ[P.map Y] κ := by
  apply condDistrib_ae_eq_of_joint_frestrictLe P Y X hY hX κ horizon
  intro n hn
  apply jointLaw_eq_compProd_map_of_fiber_factorization P Y X hY hX
    (frestrictLe n) (by fun_prop)
  · intro u
    let y : ℕ → V := fun m => if hm : m ≤ n then u ⟨m, Finset.mem_Iic.mpr hm⟩
      else u ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩
    refine ⟨y, ?_⟩
    funext r
    change y r = u r
    simp only [y, Finset.mem_Iic.mp r.2, dite_true]
  · intro y z hyz
    apply hconst
    funext r
    exact congrFun hyz ⟨r, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp r.2).trans hn)⟩
  · exact hfactor n hn

end GraphicalAllocation.Palm.Infinite
