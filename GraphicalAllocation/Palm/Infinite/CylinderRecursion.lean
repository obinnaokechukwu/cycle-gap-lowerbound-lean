import GraphicalAllocation.Palm.Infinite.ContinuousCells
import GraphicalAllocation.Palm.Infinite.Trajectory

/-! # Restricted chronological path laws

The last-coordinate measure of a finite cylinder is computed by chronological
kernel composition, while retaining all tag observations in the cylinder.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory
namespace GraphicalAllocation.Palm.Infinite
variable {Ω V : Type*} [MeasurableSpace Ω]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
  (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)]

lemma pathMeasure_restrict_history_succ (n : ℕ)
    (H : Set (Π _i : Finset.Iic n, Ω)) (hH : MeasurableSet H) :
    ((pathMeasure μ K).restrict (frestrictLe n ⁻¹' H)).map (fun ω => ω (n + 1)) =
      K n ∘ₘ (((pathMeasure μ K).restrict (frestrictLe n ⁻¹' H)).map (fun ω => ω n)) := by
  ext t ht
  rw [Measure.map_apply (measurable_pi_apply _) ht,
    Measure.restrict_apply ((measurable_pi_apply _) ht),
    Measure.bind_apply ht (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ ht) (measurable_pi_apply n)]
  have hj := congrArg (fun ν : Measure ((Π i : Finset.Iic n, Ω) × Ω) => ν (H ×ˢ t))
    (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Ω) (μ₀ := μ) (κ := historyKernel K) (a := n))
  rw [Measure.compProd_apply_prod hH ht, Measure.map_apply (by fun_prop) (hH.prod ht),
    setLIntegral_map hH (Kernel.measurable_coe _ ht) (by fun_prop)] at hj
  change (∫⁻ ω in frestrictLe n ⁻¹' H, K n (ω n) t ∂pathMeasure μ K) = _ at hj
  rw [hj]
  change (pathMeasure μ K) _ = (pathMeasure μ K) _
  congr 1
  ext ω
  simp [and_comm]

/-- Finite tag cylinder, including its initial observation. -/
def tagCylinder (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ) : Set (ℕ → Ω) :=
  {ω | ∀ r, r ≤ n → p r (ω r) = z r}

omit [Fintype V] [DecidableEq V] in
lemma tagCylinder_measurable (p : ℕ → Ω → V) (hp : ∀ n, Measurable (p n))
    (z : ℕ → V) (n : ℕ) : MeasurableSet (tagCylinder p z n) := by
  simp only [tagCylinder, ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro _
  exact (hp r |>.comp (measurable_pi_apply r)) (measurableSet_singleton (z r))

omit [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V]
  [DecidableEq V] in
lemma tagCylinder_as_history (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ) :
    tagCylinder p z n = frestrictLe n ⁻¹' {u | ∀ r : Finset.Iic n, p r (u r) = z r} := by
  ext ω
  exact ⟨fun h r => h r (Finset.mem_Iic.mp r.2),
    fun h r hr => h ⟨r, Finset.mem_Iic.mpr hr⟩⟩

/-- The final mark, with all earlier tag observations retained. -/
def tagLastLaw (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ) : Measure Ω :=
  ((pathMeasure μ K).restrict (tagCylinder p z n)).map (fun ω => ω n)

omit [Fintype V] [DecidableEq V] [IsProbabilityMeasure μ] in
lemma tagLastLaw_zero (p : ℕ → Ω → V) (hp : ∀ n, Measurable (p n)) (z : ℕ → V) :
    tagLastLaw μ K p z 0 = μ.restrict {a | p 0 a = z 0} := by
  have hc : MeasurableSet {a | p 0 a = z 0} := hp 0 (measurableSet_singleton _)
  have he : tagCylinder p z 0 = (fun ω => ω 0) ⁻¹' {a | p 0 a = z 0} := by
    ext ω
    simp [tagCylinder]
  rw [tagLastLaw, he, ← Measure.restrict_map (measurable_pi_apply 0) hc,
    pathMeasure_initial]

omit [Fintype V] [DecidableEq V] in
lemma tagLastLaw_succ (p : ℕ → Ω → V) (hp : ∀ n, Measurable (p n))
    (z : ℕ → V) (n : ℕ) :
    tagLastLaw μ K p z (n + 1) =
      (K n ∘ₘ tagLastLaw μ K p z n).restrict {b | p (n + 1) b = z (n + 1)} := by
  have hc : MeasurableSet {a | p (n + 1) a = z (n + 1)} :=
    hp (n + 1) (measurableSet_singleton _)
  have hH : MeasurableSet {u : Π i : Finset.Iic n, Ω |
      ∀ r : Finset.Iic n, p r (u r) = z r} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    exact (hp r |>.comp (measurable_pi_apply r)) (measurableSet_singleton _)
  have hs := pathMeasure_restrict_history_succ μ K n _ hH
  rw [← tagCylinder_as_history] at hs
  change _ = K n ∘ₘ tagLastLaw μ K p z n at hs
  rw [← hs, Measure.restrict_map (measurable_pi_apply _) hc,
    Measure.restrict_restrict ((measurable_pi_apply _) hc)]
  unfold tagLastLaw
  congr 2
  ext ω
  simp only [tagCylinder, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    exact ⟨h (n + 1) le_rfl, fun r hr => h r (by omega)⟩
  · rintro ⟨hlast, hprev⟩ r hr
    by_cases h : r ≤ n
    · exact hprev r h
    · have : r = n + 1 := by omega
      simpa [this] using hlast

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V] [DecidableEq V]
  [IsProbabilityMeasure μ] in
lemma tagLastLaw_mass (p : ℕ → Ω → V) (z : ℕ → V) (n : ℕ) :
    tagLastLaw μ K p z n univ = pathMeasure μ K (tagCylinder p z n) := by
  rw [tagLastLaw, Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ]
  simp

section Discrete
variable (ν : Measure V) [IsProbabilityMeasure ν]
  (L : ℕ → Kernel V V) [∀ n, IsMarkovKernel (L n)]

omit [Fintype V] [DecidableEq V] in
lemma markov_tagLastLaw (z : ℕ → V) (n : ℕ) :
    tagLastLaw ν L (fun _ => id) z n =
      (ν {z 0} * ∏ r ∈ Finset.range n, L r (z r) {z (r + 1)}) • Measure.dirac (z n) := by
  induction n with
  | zero =>
    rw [tagLastLaw_zero ν L _ (fun _ => measurable_id)]
    simp only [id_eq, Finset.range_zero, Finset.prod_empty, mul_one,
      Set.ofPred_eq_eq_singleton, Measure.restrict_singleton]
  | succ n ih =>
    rw [tagLastLaw_succ ν L _ (fun _ => measurable_id), ih, Measure.comp_smul]
    rw [Measure.dirac_bind (L n).measurable]
    simp only [id_eq, Set.ofPred_eq_eq_singleton]
    rw [Measure.restrict_smul, Measure.restrict_singleton, smul_smul,
      Finset.prod_range_succ, mul_assoc]

omit [Fintype V] [DecidableEq V] in
/-- The usual full-cylinder formula for a chronological discrete-state Markov chain. -/
lemma markov_tag_cylinder (z : ℕ → V) (n : ℕ) :
    pathMeasure ν L (tagCylinder (fun _ => id) z n) =
      ν {z 0} * ∏ r ∈ Finset.range n, L r (z r) {z (r + 1)} := by
  rw [← tagLastLaw_mass, markov_tagLastLaw, Measure.smul_apply]
  simp

end Discrete
end GraphicalAllocation.Palm.Infinite
