import GraphicalAllocation.Applications.Graphs.Model
import GraphicalAllocation.Applications.Graphs.TorusSetup

/-! # Exact-count and metric-volume bridges for rectangular tori -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry Diffusion MeasureTheory SimpleGraph
open scoped ENNReal NNReal

lemma torus_graphBall_card (n k R : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    (graphBall (cycleGraph (n + 3) □ cycleGraph (k + 3)) x R).card ≤
      (2 * R + 1) * min (k + 3) (2 * R + 1) := by
  apply (card_product_graphBall_le _ _ x R).trans
  apply Nat.mul_le_mul (cycle_graphBall_card_le n x.1 R)
  exact le_min (by simpa using Finset.card_le_univ (graphBall (cycleGraph (k + 3)) x.2 R))
    (cycle_graphBall_card_le k x.2 R)

lemma torus_ball_card (n k R : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    ((closedBall (torusDistance n k) R x).card : ℝ) ≤
      (2 * R + 1) * min (k + 3 : ℝ) (2 * R + 1) := by
  have heq : closedBall (torusDistance n k) R x =
      graphBall (cycleGraph (n + 3) □ cycleGraph (k + 3)) x R := by
    ext y
    rw [mem_closedBall, mem_graphBall]
    unfold torusDistance
    rw [← (((cycleGraph_connected (n := n + 2)).boxProd
      (cycleGraph_connected (n := k + 2))).preconnected x y).coe_dist_eq_edist]
    norm_cast
  rw [heq]
  exact_mod_cast torus_graphBall_card n k R x

lemma torus_variable_ball_card (n k : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin (n + 3) × Fin (k + 3)) :
    ((closedBall (torusDistance n k) (torusRadius torusKappa s) x).card : ℝ) ≤
      torusVolume (k + 3) torusKappa s := by
  exact (torus_ball_card n k ⌈torusKappa * Real.sqrt (s + 1)⌉₊ x).trans
    (torusRadius_volume_bound (by positivity) one_le_torusKappa hs)

lemma torus_allocation_degree (n k : ℕ)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3))) :
    ∀ v, A.degree v ≤ 4 := by
  intro v
  rw [allocation_degree_eq_graph_degree _ A hA]
  have h := torus_degree n k v
  simp only [← SimpleGraph.ncard_neighborSet] at h ⊢
  exact h.le

lemma torus_edge_vertex_ratio (n k : ℕ) :
    (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet : ℝ) /
      Fintype.card (Fin (n + 3) × Fin (k + 3)) = 2 := by
  rw [canonical_edge_count, torus_edge_count]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hN : (Fintype.card (Fin (n + 3) × Fin (k + 3)) : ℝ) ≠ 0 := by positivity
  have hnp : (0:ℝ) < n + 3 := by positivity
  have hkp : (0:ℝ) < k + 3 := by positivity
  push_cast
  field_simp

lemma torus_allocation_edge_lipschitz (n k : ℕ)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3))) :
    ∀ e, ‖torusEmbedding n k (A.tail e) - torusEmbedding n k (A.head e)‖ ≤ 1 := by
  intro e
  exact (torusEmbedding_edge n k (canonical_endpoints_adj _ A hA e).symm).le

end GraphicalAllocation.Applications.Graphs
