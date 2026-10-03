import GraphicalAllocation.Smoothed.Drift
import GraphicalAllocation.Smoothed.CycleConstants
import GraphicalAllocation.Geometry.CycleEdges
import GraphicalAllocation.Process.Law

/-!
# The identical smoothed process in both cycle edge presentations

The six reconstruction stages identify a universal kernel equality, the finite
cycle vertex and edge types, the two actual allocation rules, rate equality
through neighbor sums, the orientation-complement proof, and finally finite
sum and cardinality bookkeeping. Equality of laws follows from equality of
constructed kernels, with no assumed law-identification hypothesis.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators Fin.CommRing NNReal
open Process Rules Geometry SimpleGraph

lemma cycle_regular (n : ℕ) : (cycleGraph (n + 3)).IsRegularOfDegree 2 :=
  fun _ => cycleGraph_degree_three_le

lemma cycle_edge_card (n : ℕ) : Fintype.card (cycleGraph (n + 3)).edgeSet = n + 3 := by
  have h := graph_regular_degree_sum (cycleGraph (n + 3)) (cycle_regular n)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h
  have he : (Fintype.card (cycleGraph (n + 3)).edgeSet : ℝ) = n + 3 := by linarith
  exact_mod_cast he

instance cycle_edges_nonempty (n : ℕ) : Nonempty (cycleGraph (n + 3)).edgeSet := by
  apply Fintype.card_pos_iff.mp
  rw [cycle_edge_card]
  omega

/-- The paper's cutoff on the literal cyclic edge indexing. -/
def cycleRule (n : ℕ) : AllocationRule (Fin (n + 3)) (Fin (n + 3)) :=
  rule (cycleOrientation n) (242 * Real.log (n + 3))
    (cycle_cutoff_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

@[simp] lemma cycleRule_orientation (n : ℕ) :
    (cycleRule n).toOrientedGraph = cycleOrientation n := rfl

lemma cycle_rule_rate (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (x : Profile (Fin (n + 3))) (v : Fin (n + 3)) :
    (rule (cycleOrientation n) θ hθ).rate x v =
      probability θ ((x v : ℝ) - x (v - 1)) +
        probability θ ((x v : ℝ) - x (v + 1)) := by
  have he (e : Fin (n + 3)) : (v = e + 1) ↔ e = v - 1 := by
    rw [eq_sub_iff_add_eq, eq_comm]
  simp only [AllocationRule.rate, AllocationRule.edgeRate,
    AllocationRule.edgeProbability, rule, cycleOrientation, Int.cast_sub, he,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_eq]
  have hm : v - 1 + 1 = v := by ring
  rw [hm, show (x (v - 1) : ℝ) - x v = -((x v : ℝ) - x (v - 1)) by ring,
    probability_neg]
  ring

lemma cycle_rule_rate_eq_graph (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (x : Profile (Fin (n + 3))) (v : Fin (n + 3)) :
    (rule (cycleOrientation n) θ hθ).rate x v =
      (graphRule (cycleGraph (n + 3)) θ hθ).rate x v := by
  rw [cycle_rule_rate, graph_rate_eq_neighbor_sum, cycleGraph_neighborFinset]
  have hne : v - 1 ≠ v + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
    exact ne_of_beq_false rfl
  rw [Finset.sum_pair hne]

/-- Equality includes both the normalized weights and actual profile updates. -/
lemma cycle_rule_kernel_eq_graph (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    (rule (cycleOrientation n) θ hθ).kernel =
      (graphRule (cycleGraph (n + 3)) θ hθ).kernel := by
  unfold AllocationRule.kernel
  congr 1
  funext x v
  rw [cycle_rule_rate_eq_graph, cycle_edge_card, Fintype.card_fin]

/-- Relabeling the edge clocks preserves the full event-count law. -/
lemma cycle_rule_eventLaw_eq_graph (n k : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (x : Profile (Fin (n + 3))) :
    (rule (cycleOrientation n) θ hθ).kernel.eventLaw k x =
      (graphRule (cycleGraph (n + 3)) θ hθ).kernel.eventLaw k x := by
  rw [cycle_rule_kernel_eq_graph]

/-- Equality also preserves physical time: there are exactly `n+3` edge clocks. -/
lemma cycle_rule_continuousLaw_eq_graph (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (time : ℝ≥0) (x : Profile (Fin (n + 3))) :
    (rule (cycleOrientation n) θ hθ).kernel.continuousLaw (n + 3) time x =
      (graphRule (cycleGraph (n + 3)) θ hθ).kernel.continuousLaw
        (Fintype.card (cycleGraph (n + 3)).edgeSet) time x := by
  rw [cycle_rule_kernel_eq_graph, cycle_edge_card]
  simp only [Nat.cast_add, Nat.cast_ofNat]

lemma cycleRule_kernel (n : ℕ) :
    (cycleRule n).kernel =
      (graphRule (cycleGraph (n + 3)) (cutoff (n + 3) 2 10)
        (cutoff_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
          (by norm_num) (by norm_num))).kernel := by
  simpa only [cycle_cutoff, cycleRule] using
    (cycle_rule_kernel_eq_graph n
      (cycle_cutoff_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))

end GraphicalAllocation.Smoothed
