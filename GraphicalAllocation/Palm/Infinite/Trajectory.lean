import GraphicalAllocation.Palm.Infinite.CellKernel

/-! # Literal infinite-horizon Markov trajectories

Ionescu--Tulcea constructs a single countably infinite path law. Its cylinder
laws are the actual finite compositions, and its regular conditional transition
is the prescribed kernel. Common invariance gives every coordinate the same
law, not only each finite-dimensional approximation separately.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory

namespace GraphicalAllocation.Palm.Infinite

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Turn a Markov transition into a history-dependent transition by reading the
last coordinate of the history. -/
def historyKernel (K : ℕ → Kernel Ω Ω) (n : ℕ) :
    Kernel (Π _i : Finset.Iic n, Ω) Ω :=
  (K n).comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (historyKernel K n) := by
  unfold historyKernel
  infer_instance

/-- One genuine probability measure on the space of all infinite trajectories. -/
def pathMeasure (μ : Measure Ω) (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] :
    Measure (ℕ → Ω) := Kernel.trajMeasure μ (historyKernel K)

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] : IsProbabilityMeasure (pathMeasure μ K) := by
  unfold pathMeasure
  infer_instance

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ℕ → Kernel Ω Ω)
  [∀ n, IsMarkovKernel (K n)]

omit [IsProbabilityMeasure μ] in
/-- Exact equality of every finite-dimensional law with the finite chronological
kernel composition. This is the Ionescu--Tulcea extension property. -/
lemma pathMeasure_finite (n : ℕ) :
    (pathMeasure μ K).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => Ω) (historyKernel K) 0 n ∘ₘ
        (μ.map (MeasurableEquiv.piUnique _).symm) := by
  rw [pathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe]

omit [IsProbabilityMeasure μ] in
lemma pathMeasure_initial : (pathMeasure μ K).map (fun x => x 0) = μ := by
  have h := pathMeasure_finite μ K 0
  have hmap := congrArg (fun ν : Measure (Π i : Finset.Iic 0, Ω) =>
    ν.map (fun x => x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) h
  rw [Measure.map_map (by fun_prop) (by fun_prop), Kernel.partialTraj_self,
    Measure.id_comp, Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  simpa [Function.comp_def, MeasurableEquiv.piUnique] using hmap

/-- The next-coordinate marginal is obtained by applying the genuine transition
to the previous-coordinate marginal. -/
lemma pathMeasure_succ (n : ℕ) :
    (pathMeasure μ K).map (fun x => x (n + 1)) =
      K n ∘ₘ ((pathMeasure μ K).map (fun x => x n)) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Ω) (μ₀ := μ) (κ := historyKernel K) (a := n)
  have hs := congrArg Measure.snd h
  rw [Measure.snd_compProd, Measure.snd_map_prodMk (by fun_prop) (by fun_prop)] at hs
  change historyKernel K n ∘ₘ ((pathMeasure μ K).map (frestrictLe n)) =
    (pathMeasure μ K).map (fun x => x (n + 1)) at hs
  rw [← hs]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (by fun_prop),
    lintegral_map (Kernel.measurable_coe _ hs) (by fun_prop)]
  rfl

/-- A common invariant starting law is the law of every coordinate of the
single infinite process. -/
lemma pathMeasure_marginal (hK : ∀ n, K n ∘ₘ μ = μ) (n : ℕ) :
    (pathMeasure μ K).map (fun x => x n) = μ := by
  induction n with
  | zero => exact pathMeasure_initial μ K
  | succ n ih => rw [pathMeasure_succ μ K n, ih, hK n]

/-- Regular conditional transitions given the entire preceding finite history. -/
lemma pathMeasure_condDistrib [StandardBorelSpace Ω] [Nonempty Ω] (n : ℕ) :
    condDistrib (fun x => x (n + 1)) (frestrictLe n) (pathMeasure μ K)
      =ᵐ[(pathMeasure μ K).map (frestrictLe n)] historyKernel K n :=
  Kernel.condDistrib_trajMeasure (X := fun _ => Ω)

/-- If the common invariant measure is supported by `s`, the infinite path
stays in `s` at every time almost surely. Countability handles all coordinates
simultaneously. -/
lemma pathMeasure_supported (hK : ∀ n, K n ∘ₘ μ = μ)
    (s : Set Ω) (hs : MeasurableSet s) (hμ : μ s = 1) :
    ∀ᵐ x ∂pathMeasure μ K, ∀ n, x n ∈ s := by
  rw [ae_all_iff]
  intro n
  apply ae_of_ae_map (measurable_pi_apply n).aemeasurable
  rw [pathMeasure_marginal μ K hK n]
  exact (mem_ae_iff_prob_eq_one hs).mpr hμ

end GraphicalAllocation.Palm.Infinite
