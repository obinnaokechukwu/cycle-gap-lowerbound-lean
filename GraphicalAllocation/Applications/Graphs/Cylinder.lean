import GraphicalAllocation.Applications.Graphs.Model
import GraphicalAllocation.Applications.Graphs.Embedding
import GraphicalAllocation.Process.Normalized.Law

/-! # Cycles of finite width: actual-law Theorem 7.2

The cross-section is any finite nonempty simple graph; it need not be connected.
All endpoint-local antitone edge probabilities and all independent initial laws
are admitted. The expectation is an ENNReal lintegral, without a moment assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]

/-- The finite-width cylinder lower bound with the paper's explicit constant. -/
theorem cylinder_lower_bound (H : SimpleGraph W) (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × W) (cycleGraph (n + 3) □ H).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ H))
    (μ : PMF (Profile (Fin (n + 3) × W))) (t : ℝ≥0) (ht : (n + 3 : ℝ) ^ 2 ≤ t) :
    let a := cylinderConstant (2 + H.maxDegree) * Real.sqrt ((n + 3 : ℝ) / Fintype.card W)
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom μ (Fintype.card (cycleGraph (n + 3) □ H).edgeSet) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ
      (Fintype.card (cycleGraph (n + 3) □ H).edgeSet) t).toMeasure {x | a ≤ gap x} := by
  dsimp only
  let : MeasurableSpace (Fin (n + 3) × W) := ⊤
  let : MeasurableSpace (cycleGraph (n + 3) □ H).edgeSet := ⊤
  have hΔ : (2 : ℝ) ≤ 2 + H.maxDegree := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hw : (1 : ℝ) ≤ Fintype.card W := by exact_mod_cast Fintype.card_pos (α := W)
  have hLpos : (0 : ℝ) < n + 3 := by positivity
  have hpTime := cylinder_phase_time H n t ht
  have hphase := A.continuous_phase_third μ
    (Fintype.card (cycleGraph (n + 3) □ H).edgeSet) t
    (by exact_mod_cast Fintype.card_pos (α := (cycleGraph (n + 3) □ H).edgeSet)) hpTime
  by_cases hlarge : 120 ≤ n + 3
  · let R : ℕ := (n + 3) / 6
    let B : ℝ := Fintype.card W * (2 * (R : ℝ) + 1)
    have hpar := cylinder_radius_bounds hlarge
    have hR : (n + 3 : ℝ) / 7 ≤ (R : ℝ) := by simpa [R] using hpar.1
    have hRpos : (0 : ℝ) < R := (div_pos hLpos (by norm_num)).trans_le hR
    have hBpos : 0 < B := by dsimp [B]; positivity
    have hBcap : B ≤ Fintype.card W * (n + 3 : ℝ) / 2 := by
      dsimp [B]
      have h := mul_le_mul_of_nonneg_left hpar.2.2.1 (show (0:ℝ) ≤ Fintype.card W by positivity)
      simpa [R, mul_div_assoc] using h
    have hδ : 0 < (2 + H.maxDegree : ℝ) * ((2 + H.maxDegree : ℝ) + 1) := by positivity
    have hR8 : 8 * (Real.pi / 2) ≤ (R : ℝ) := by
      have hh := hpar.2.1
      dsimp [R]
      linarith
    have hRL : (R : ℝ) ≤ n + 3 := by
      exact_mod_cast (show (n + 3) / 6 ≤ n + 3 from Nat.div_le_self _ _)
    have hT := (cylinder_horizon_le_square hLpos.le hRpos.le hRL hΔ).trans ht
    have hmain := allocation_embedding_lower_bound A (2 + H.maxDegree)
      (cylinder_allocation_degree H n A hA) (fun x => cycleEmbedding n x.1)
      (cylinder_allocation_edge_lipschitz H n A hA) (cylinderDistance n)
      (cylinderDistance_self n) (cylinderDistance_comm n) (cylinderDistance_triangle n)
      (by positivity : (0:ℝ) < Real.pi / 2) (cylinderEmbedding_distortion n)
      hR8 hBpos (productHalfShift n W) (cylinder_half_separated n R hpar.2.2.2)
      (cylinder_ball_card n R) μ t (by simpa using hT) hpTime
    have hm : (0:ℝ) < Fintype.card (cycleGraph (n + 3) □ H).edgeSet := by
      exact_mod_cast Fintype.card_pos (α := (cycleGraph (n + 3) □ H).edgeSet)
    have hN : (0:ℝ) < Fintype.card (Fin (n + 3) × W) := by exact_mod_cast Fintype.card_pos
    have hcomp := cylinder_scale_comparison hLpos (by linarith : (0:ℝ) < Fintype.card W)
      hΔ hR hBpos hBcap (cylinder_edge_vertex_ratio H n)
    rw [embedding_scale_identity (by positivity : (0:ℝ) < Real.pi / 2) hδ hRpos.le hm.le hN hBpos] at hcomp
    apply gap_target_mono _ gap hcomp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hmain
  · apply small_gap_target _ gap (measurable_of_countable gap) gap_nonneg hphase
    apply cylinder_small_scale hLpos.le _ hw hΔ
    exact_mod_cast (show n + 3 < 120 by omega)

/-- The same constant under every invariant normalized cylinder law. -/
theorem cylinder_invariant_lower_bound (H : SimpleGraph W) (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × W) (cycleGraph (n + 3) □ H).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ H))
    (anchor : Fin (n + 3) × W) (π : PMF (NormalizedProfile anchor))
    (hπ : A.InvariantNormalizedLaw anchor π) :
    let a := cylinderConstant (2 + H.maxDegree) * Real.sqrt ((n + 3 : ℝ) / Fintype.card W)
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x.val) ∂π.toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ π.toMeasure {x | a ≤ gap x.val} := by
  let t : ℝ≥0 := ⟨(n + 3 : ℝ) ^ 2, sq_nonneg _⟩
  have h := cylinder_lower_bound H n A hA (π.map Subtype.val) t le_rfl
  exact A.invariant_gap_lower_bound anchor π hπ t _ _ _ h.1 h.2

end GraphicalAllocation.Applications.Graphs
