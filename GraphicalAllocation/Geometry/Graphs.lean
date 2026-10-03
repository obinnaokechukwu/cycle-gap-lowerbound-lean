import GraphicalAllocation.Geometry.Hall
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! # Actual graph counts, product metric, and affected edge fibers -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Geometry

open scoped BigOperators
open SimpleGraph

/-- The affected fibers are edges incident to the closed neighborhood. -/
def affectedEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) : Finset (Sym2 V) :=
  (insert w (G.neighborFinset w)).biUnion (fun v => G.incidenceFinset v)

/-- Overlapping incident fibers are counted at most once. -/
theorem card_affectedEdges_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (w : V) :
    (affectedEdges G w).card ≤ Δ * (Δ + 1) := by
  have hc : (insert w (G.neighborFinset w)).card ≤ Δ + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree]
    exact Nat.add_le_add_right (hΔ w) 1
  calc
    _ ≤ ∑ v ∈ insert w (G.neighborFinset w), (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ v ∈ insert w (G.neighborFinset w), Δ := by
      apply Finset.sum_le_sum
      intro v hv
      simpa using hΔ v
    _ = (insert w (G.neighborFinset w)).card * Δ := by simp
    _ ≤ (Δ + 1) * Δ := Nat.mul_le_mul_right Δ hc
    _ = Δ * (Δ + 1) := Nat.mul_comm _ _

/-- Canonical cycles with at least three vertices have degree exactly two. -/
theorem cycle_degree (n : ℕ) (v : Fin (n + 3)) :
    (cycleGraph (n + 3)).degree v = 2 := cycleGraph_degree_three_le

/-- The number of unoriented edges of `C_n` is `n`, including `n=3`. -/
theorem cycle_edge_count (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  have h := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
  simp_rw [cycle_degree] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- Cylinder vertex count, with no connectedness assumption on the cross-section. -/
theorem cylinder_vertex_count {W : Type*} [Fintype W] (n : ℕ) :
    Fintype.card (Fin (n + 3) × W) = (n + 3) * Fintype.card W := by simp

/-- The exact local degree in a Cartesian cylinder. -/
theorem cylinder_degree {W : Type*} [Fintype W] (H : SimpleGraph W)
    (n : ℕ) (x : Fin (n + 3) × W) :
    (cycleGraph (n + 3) □ H).degree x = 2 + H.degree x.2 := by
  rw [degree_boxProd, cycle_degree]

/-- Exact edge count in a Cartesian cylinder. -/
theorem cylinder_edge_count {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (n : ℕ) :
    (cycleGraph (n + 3) □ H).edgeFinset.card =
      (n + 3) * Fintype.card W + (n + 3) * H.edgeFinset.card := by
  have h := (cycleGraph (n + 3) □ H).sum_degrees_eq_twice_card_edges
  have hh := H.sum_degrees_eq_twice_card_edges
  simp_rw [degree_boxProd, cycle_degree] at h
  rw [Fintype.sum_prod_type] at h
  simp_rw [Finset.sum_add_distrib] at h
  simp_rw [← H.ncard_neighborSet] at h hh
  rw [hh] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] at h ⊢
  nlinarith [h]

/-- Rectangular tori have degree four even if a side has length three. -/
theorem torus_degree (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    (cycleGraph (n + 3) □ cycleGraph (k + 3)).degree x = 4 := by
  rw [degree_boxProd, cycle_degree, cycle_degree]

/-- Thus the unoriented edge/vertex ratio of a rectangular torus is two. -/
theorem torus_edge_count (n k : ℕ) :
    (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeFinset.card =
      2 * ((n + 3) * (k + 3)) := by
  rw [cylinder_edge_count]
  have hc := cycle_edge_count k
  simp only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] at hc ⊢
  rw [hc]
  simp only [Fintype.card_fin]
  omega

/-- The canonical extended graph metric on a Cartesian product is the sum of
its coordinate metrics. This also explicitly handles disconnected factors. -/
theorem product_edist {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (x y : V × W) :
    (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2 :=
  edist_boxProd _ _

/-- A graph ball in a Cartesian product lies in the product of coordinate balls. -/
theorem product_graphBall_subset {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (x : V × W) (r : ℕ) :
    graphBall (G □ H) x r ⊆ graphBall G x.1 r ×ˢ graphBall H x.2 r := by
  classical
  intro y hy
  rw [Finset.mem_product, mem_graphBall, mem_graphBall]
  rw [mem_graphBall, product_edist] at hy
  exact ⟨le_trans le_self_add hy, le_trans le_add_self hy⟩

/-- Product-volume upper bound, before inserting the cyclic ball bounds. -/
theorem card_product_graphBall_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (x : V × W) (r : ℕ) :
    (graphBall (G □ H) x r).card ≤
      (graphBall G x.1 r).card * (graphBall H x.2 r).card := by
  classical
  exact (Finset.card_le_card (product_graphBall_subset G H x r)).trans_eq
    (Finset.card_product _ _)

end GraphicalAllocation.Geometry
