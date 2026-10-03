import GraphicalAllocation.Applications.Graphs.TorusModel

/-! # One fixed family of tests for the full torus lag integral -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry Diffusion MeasureTheory SimpleGraph
open scoped ENNReal NNReal

/-- Actual transport on the torus, with one half-period permutation and variable
protected radii. The terminal test family is never changed with the lag. -/
theorem torus_transport_bound (n k : ℕ)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3)))
    (μ : PMF (Profile (Fin (n + 3) × Fin (k + 3)))) (t : ℝ≥0)
    (ht : (n + 3 : ℝ) ^ 2 ≤ t) (hlarge : 16 * torusKappa ≤ n + 3)
    (M : ℝ) (hM : 1 ≤ M)
    (hp : (A.kernel.continuousLawFrom μ
      (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure
      {x | M - 1 < gap x} ≤ (1 / 8 : ℝ≥0∞)) :
    (2 * ∫ s in (0:ℝ)..torusHorizon torusKappa (n + 3),
      1 / torusVolume (k + 3) torusKappa s) / 4 ≤ M ^ 2 := by
  let : MeasurableSpace (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet := ⊤
  have hKpos : (0 : ℝ) < k + 3 := by positivity
  have hLpos : (0 : ℝ) < n + 3 := by positivity
  have hT := torusHorizon_nonneg torusKappa_pos hlarge
  have hTt := (torus_horizon_le_square hLpos.le).trans ht
  have hp' : continuousBadGapFrom A μ.toMeasure t M ≤ 1 / 8 := by
    rw [continuousBadGapFrom_eq_probability, measureReal_def]
    simpa using ENNReal.toReal_mono (by norm_num : (1 / 8 : ℝ≥0∞) ≠ ⊤) hp
  have hq : ∀ s ∈ Set.Icc 0 (torusHorizon torusKappa (n + 3)), ∀ x,
      continuousTagTail A (Real.toNNReal s) x (torusDistance n k) (torusRadius torusKappa s) ≤ 1 / 8 := by
    intro s hs x
    have hR := torusRadius_pos torusKappa_pos hs.1
    have he := allocation_embedding_tail_physical A 4 (torus_allocation_degree n k A hA)
      (torusEmbedding n k) 1 (torus_allocation_edge_lipschitz n k A hA)
      (torusDistance n k) (by positivity : (0:ℝ) < Real.pi / Real.sqrt 2)
      (torusEmbedding_distortion n k) x (Real.toNNReal s) hR
    change continuousTagTail A (Real.toNNReal s) x (torusDistance n k) _ ≤ _ at he
    rw [Real.coe_toNNReal s hs.1] at he
    have hm := div_le_div_of_nonneg_right (torus_diffusion_budget hs.1)
      (sq_nonneg (torusRadius torusKappa s))
    have htail := torusRadius_tail_bound (by positivity : 0 ≤ 21 * Real.pi ^ 2)
      torusKappa_pos torusKappa_sq hs.1
    exact he.trans (hm.trans (htail.trans (by norm_num)))
  have htr := continuous_transport_volume_simple A μ.toMeasure (torusDistance n k)
    (torusDistance_diag n k) (torusDistance_symm n k) (torusDistance_triangle n k)
    (productHalfShift n (Fin (k + 3))) hM t hT hTt
    (torusRadius torusKappa) (torusVolume (k + 3) torusKappa)
    (fun s hs => torusRadius_pos torusKappa_pos hs.1)
    (fun s hs => torusVolume_pos hKpos torusKappa_pos hs.1)
    (fun s hs => torus_half_separated n k (by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        torusRadius_le_eighth one_le_torusKappa hlarge hs.1 hs.2))
    (fun s hs => torus_variable_ball_card n k hs.1) hq hp'
    (torusVolume_reciprocal_integrable hKpos torusKappa_pos hT)
  have hratio : (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet : ℝ) /
      (4 * Fintype.card (Fin (n + 3) × Fin (k + 3))) = 1 / 2 := by
    calc
      _ = ((Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet : ℝ) /
          Fintype.card (Fin (n + 3) × Fin (k + 3))) / 4 := by ring
      _ = 1 / 2 := by rw [torus_edge_vertex_ratio]; norm_num
  rw [hratio] at htr
  convert htr using 1
  ring

end GraphicalAllocation.Applications.Graphs
