import GraphicalAllocation.Applications.CycleArithmetic
import GraphicalAllocation.Geometry.CycleEdges
import GraphicalAllocation.Transport.Weighted
import GraphicalAllocation.Transport.Quantile
import GraphicalAllocation.Process.Phase

/-!
# Actual cycle metric and law interfaces for the lower-bound applications

The vertex and edge index types are both `Fin (n+3)`. This is exactly the paper's
range of all cycle sizes at least three. The rule remains arbitrary, subject only
to its cyclic orientation and the model's edgewise antitone probabilities.
-/

noncomputable section
namespace GraphicalAllocation.Applications
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

/-- The real-valued genuine graph distance of the cycle. -/
def cycleMetric (n : ℕ) (i j : Fin (n + 3)) : ℝ :=
  (cycleGraph (n + 3)).dist i j

@[simp] lemma cycleMetric_diag (n : ℕ) (i : Fin (n + 3)) : cycleMetric n i i = 0 := by
  simp [cycleMetric]

lemma cycleMetric_symm (n : ℕ) (i j : Fin (n + 3)) :
    cycleMetric n i j = cycleMetric n j i := by
  simp only [cycleMetric, SimpleGraph.dist_comm]

lemma cycleMetric_triangle (n : ℕ) (i j k : Fin (n + 3)) :
    cycleMetric n i k ≤ cycleMetric n i j + cycleMetric n j k := by
  unfold cycleMetric
  exact_mod_cast (cycleGraph_connected (n := n + 2)).dist_triangle (u := i) (v := j) (w := k)

lemma cycleMetric_ball_card (n R : ℕ) (i : Fin (n + 3)) :
    ((closedBall (cycleMetric n) R i).card : ℝ) ≤ 2 * R + 1 := by
  have heq : closedBall (cycleMetric n) R i = graphBall (cycleGraph (n + 3)) i R := by
    ext j
    simp only [closedBall, graphBall, Finset.mem_filter, Finset.mem_univ, true_and, cycleMetric]
    rw [← ((cycleGraph_connected (n := n + 2)).preconnected i j).coe_dist_eq_edist]
    norm_cast
    simp
  rw [heq]
  exact_mod_cast cycle_graphBall_card_le n i R

lemma cycleMetric_half_separated (n R : ℕ) (hR : 2 * R ≤ (n + 3) / 2) :
    ∀ i, 2 * (R : ℝ) ≤ cycleMetric n i (cycleHalfShift n i) := by
  intro i
  unfold cycleMetric
  exact_mod_cast cycleHalfShift_separated n R hR i

lemma cycle_continuous_separation (n r : ℕ) (hr : r ≤ (n + 3) / 2) :
    ∀ i, 2 * (r / 3 : ℕ) ≤ cycleMetric n i (cycleHalfShift n i) := by
  exact cycleMetric_half_separated n (r / 3) (by omega)

lemma cycle_discrete_separation (n R : ℕ) (hR : (R : ℝ) ≤ (n + 3 : ℕ) / 512) :
    ∀ i, 2 * (R : ℝ) ≤ cycleMetric n i (cycleHalfShift n i) := by
  have h : 512 * R ≤ n + 3 := by
    have h' : (512 : ℝ) * R ≤ (n + 3 : ℕ) := by linarith
    exact_mod_cast h'
  exact cycleMetric_half_separated n R (by omega)

/-- The cycle's one-step nonflatness event holds uniformly for every initial law. -/
theorem cycle_discrete_phase (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k : ℕ) (hk : 1 ≤ k) :
    (1 / 3 : ℝ≥0∞) ≤ (A.kernel.eventLawFrom μ k).toMeasure {x | 1 ≤ gap x} := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := A.discrete_nonflat_probability μ 2
    (fun v => by rw [cycle_allocation_degree n A hA]; norm_num) k'
  have hn : (3 : ℝ) ≤ (n + 3 : ℕ) := by exact_mod_cast (show 3 ≤ n + 3 by omega)
  have hthird : (1 / 3 : ℝ) ≤ 1 - 2 / (n + 3 : ℕ) := by
    have hd : 2 / (n + 3 : ℕ) ≤ (2 : ℝ) / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
    linarith
  simp only [Fintype.card_fin] at h
  have he := ENNReal.ofReal_le_ofReal (hthird.trans h)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using he

/-- Every small target is handled directly by the genuine one-unit phase event. -/
theorem small_gap_target {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    (hg : Measurable g) (hgn : ∀ x, 0 ≤ g x)
    (hphase : (1 / 3 : ℝ≥0∞) ≤ μ {x | 1 ≤ g x}) {a : ℝ} (ha : a ≤ 1 / 3) :
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ ∧
      (1 / 8 : ℝ≥0∞) ≤ μ {x | a ≤ g x} := by
  constructor
  · calc
      ENNReal.ofReal a ≤ ENNReal.ofReal (1 / 3) := ENNReal.ofReal_le_ofReal ha
      _ = 1 / 3 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      _ ≤ _ := phase_le_extended_expectation μ g hg hgn hphase
  · exact (show (1 / 8 : ℝ≥0∞) ≤ 1 / 3 by norm_num).trans
      (hphase.trans (measure_mono (fun x hx => by
        change a ≤ g x
        change 1 ≤ g x at hx
        linarith)))

/-- Both conclusions are monotone in the lower-bound threshold. -/
theorem gap_target_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hb : ENNReal.ofReal b ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ ∧
      (1 / 8 : ℝ≥0∞) ≤ μ {x | b ≤ g x}) :
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ ∧
      (1 / 8 : ℝ≥0∞) ≤ μ {x | a ≤ g x} :=
  ⟨(ENNReal.ofReal_le_ofReal hab).trans hb.1,
    hb.2.trans (measure_mono (fun _x hx => hab.trans hx))⟩

end GraphicalAllocation.Applications
