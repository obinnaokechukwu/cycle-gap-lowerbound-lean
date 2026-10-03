import GraphicalAllocation.Applications.Graphs.Setup

/-! # Allocation-model bookkeeping for canonical Cartesian cylinders -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]

/-- The cylinders have actual edges regardless of connectivity of the cross-section. -/
instance cylinderEdgeNonempty (H : SimpleGraph W) (n : ℕ) :
    Nonempty (cycleGraph (n + 3) □ H).edgeSet := by
  apply Fintype.card_pos_iff.mp
  rw [canonical_edge_count, cylinder_edge_count]
  have : 0 < Fintype.card W := Fintype.card_pos
  positivity

omit [Nonempty W] in
lemma cylinder_allocation_degree (H : SimpleGraph W) (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × W) (cycleGraph (n + 3) □ H).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ H)) (v : Fin (n + 3) × W) :
    A.degree v ≤ 2 + H.maxDegree := by
  rw [allocation_degree_eq_graph_degree _ A hA]
  have hc := cylinder_degree H n v
  simp only [← SimpleGraph.ncard_neighborSet] at hc ⊢
  rw [hc]
  exact Nat.add_le_add_left (by simpa only [← SimpleGraph.ncard_neighborSet] using H.degree_le_maxDegree v.2) 2

lemma cylinder_edge_vertex_ratio (H : SimpleGraph W) (n : ℕ) :
    1 ≤ (Fintype.card (cycleGraph (n + 3) □ H).edgeSet : ℝ) /
      Fintype.card (Fin (n + 3) × W) := by
  have hN : (0 : ℝ) < Fintype.card (Fin (n + 3) × W) := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hN).mpr
  rw [canonical_edge_count, cylinder_edge_count]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
  nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ Fintype.card W), (Nat.cast_nonneg H.edgeFinset.card : (0:ℝ) ≤ H.edgeFinset.card)]

lemma cylinder_phase_time (H : SimpleGraph W) (n : ℕ) (t : ℝ≥0)
    (ht : (n + 3 : ℝ) ^ 2 ≤ t) :
    1 / (Fintype.card (cycleGraph (n + 3) □ H).edgeSet : ℝ) ≤ t := by
  have hm : (1 : ℝ) ≤ Fintype.card (cycleGraph (n + 3) □ H).edgeSet := by
    exact_mod_cast Fintype.card_pos (α := (cycleGraph (n + 3) □ H).edgeSet)
  exact (one_div_le_one_div_of_le (by norm_num) hm).trans (by simpa using (show (1:ℝ) ≤ t by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))

lemma canonical_endpoints_adj {V : Type*} (G : SimpleGraph V)
    (A : AllocationRule V G.edgeSet) (hA : A.toOrientedGraph = canonicalOrientation G)
    (e : G.edgeSet) : G.Adj (A.tail e) (A.head e) := by
  have ht := congrArg OrientedGraph.tail hA
  have hh := congrArg OrientedGraph.head hA
  rw [ht, hh]
  apply G.mem_edgeSet.mp
  simpa only [canonicalOrientation, Sym2.mk, Prod.mk.eta, Quot.out_eq] using e.property

omit [Fintype W] [DecidableEq W] [Nonempty W] in
lemma cylinder_allocation_edge_lipschitz (H : SimpleGraph W) (n : ℕ)
    (A : AllocationRule (Fin (n + 3) × W) (cycleGraph (n + 3) □ H).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ H)) :
    ∀ e, ‖cycleEmbedding n (A.tail e).1 - cycleEmbedding n (A.head e).1‖ ≤ 1 := by
  intro e
  exact cylinderEmbedding_edge H n (canonical_endpoints_adj _ A hA e).symm

end GraphicalAllocation.Applications.Graphs
