import GraphicalAllocation.Applications.Graphs.Cylinder
import GraphicalAllocation.Applications.Graphs.Torus

/-! # Square tori and the explicit small-scale exponential thresholds -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

lemma one_third_lt_exp_neg_one : (1 / 3 : ℝ) < Real.exp (-1) := by
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (Real.exp_pos 1) Real.exp_one_lt_three

lemma cylinder_small_scale_below_exp {L w Δ : ℝ} (hL : 0 ≤ L) (hLupper : L < 120)
    (hw : 1 ≤ w) (hΔ : 2 ≤ Δ) :
    cylinderConstant Δ * Real.sqrt (L / w) < Real.exp (-1) :=
  (cylinder_small_scale hL hLupper hw hΔ).trans_lt one_third_lt_exp_neg_one

lemma torus_small_scale_below_exp {Z : ℝ} (hZ : 0 ≤ Z)
    (hZupper : Z ≤ 32 * (1 + torusKappa)) :
    torusConstant * Real.sqrt Z < Real.exp (-1) :=
  (torus_small_scale hZ hZupper).trans_lt one_third_lt_exp_neg_one

/-- In particular square tori have the claimed sqrt(log L) lower scale. -/
theorem square_torus_lower_bound (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × Fin (n + 3))
      (cycleGraph (n + 3) □ cycleGraph (n + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (n + 3)))
    (μ : PMF (Profile (Fin (n + 3) × Fin (n + 3)))) (t : ℝ≥0) (ht : (n + 3 : ℝ) ^ 2 ≤ t) :
    let a := torusConstant * Real.sqrt (Real.log (n + 3))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom μ
        (Fintype.card (cycleGraph (n + 3) □ cycleGraph (n + 3)).edgeSet) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ
      (Fintype.card (cycleGraph (n + 3) □ cycleGraph (n + 3)).edgeSet) t).toMeasure
      {x | a ≤ gap x} := by
  have h := torus_lower_bound n n le_rfl A hA μ t ht
  apply gap_target_mono _ gap _ h
  apply mul_le_mul_of_nonneg_left _ torusConstant_pos.le
  apply Real.sqrt_le_sqrt
  have hp : (0:ℝ) < n + 3 := by positivity
  rw [div_self hp.ne']
  linarith

/-- The square-torus specialization also holds for every invariant normalized law. -/
theorem square_torus_invariant_lower_bound (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × Fin (n + 3))
      (cycleGraph (n + 3) □ cycleGraph (n + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (n + 3)))
    (anchor : Fin (n + 3) × Fin (n + 3)) (π : PMF (NormalizedProfile anchor))
    (hπ : A.InvariantNormalizedLaw anchor π) :
    let a := torusConstant * Real.sqrt (Real.log (n + 3))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x.val) ∂π.toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ π.toMeasure {x | a ≤ gap x.val} := by
  let t : ℝ≥0 := ⟨(n + 3 : ℝ) ^ 2, sq_nonneg _⟩
  have h := square_torus_lower_bound n A hA (π.map Subtype.val) t le_rfl
  exact A.invariant_gap_lower_bound anchor π hπ t _ _ _ h.1 h.2

end GraphicalAllocation.Applications.Graphs
