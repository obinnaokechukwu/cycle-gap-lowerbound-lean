import GraphicalAllocation.Geometry.Oriented
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Regular-graph counting for the universal lower bound

These facts concern the arrival graph alone. No allocation rule, locality, or
monotonicity assumption is involved. A maximal independent subset of any vertex
set covers that set by closed neighborhoods, giving the explicit greedy bound.
-/

noncomputable section
namespace GraphicalAllocation.Universal

open scoped BigOperators
open SimpleGraph Geometry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual edge indices incident to a vertex. -/
def incidentEdges (v : V) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => v ∈ (e : Sym2 V))

@[simp] theorem mem_incidentEdges (v : V) (e : G.edgeSet) :
    e ∈ incidentEdges G v ↔ v ∈ (e : Sym2 V) := by
  simp [incidentEdges]

/-- The number of incident arrival labels is the graph degree. -/
theorem card_incidentEdges (v : V) : (incidentEdges G v).card = G.degree v := by
  calc
    _ = Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} := by
      simp [incidentEdges, Fintype.card_subtype]
    _ = Fintype.card (G.incidenceSet v) := Fintype.card_congr (incidentEdgeEquiv G v)
    _ = G.degree v := G.card_incidenceSet_eq_degree v

/-- Nonadjacent distinct vertices have disjoint sets of incident edges. -/
theorem disjoint_incidentEdges {u v : V} (hne : u ≠ v) (hnot : ¬G.Adj u v) :
    Disjoint (incidentEdges G u) (incidentEdges G v) := by
  apply Finset.disjoint_left.mpr
  intro e hu hv
  have hu' : u ∈ (e : Sym2 V) := (mem_incidentEdges G u e).mp hu
  have hv' : v ∈ (e : Sym2 V) := (mem_incidentEdges G v e).mp hv
  have heq : (e : Sym2 V) = s(u, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hu', hv'⟩
  apply hnot
  apply G.mem_edgeSet.mp
  simpa [heq] using e.property

omit [DecidableEq V] in
/-- The exact regular-graph handshake identity in the actual edge type. -/
theorem regular_edge_count (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ) :
    Fintype.card V * Δ = 2 * Fintype.card G.edgeSet := by
  simpa [hΔ, canonical_edge_count G] using G.sum_degrees_eq_twice_card_edges

/-- Every vertex subset has an independent subset of size at least its size
 divided by one plus the degree bound. This is the denominator-free form. -/
theorem exists_independent_subset (S : Finset V) (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      S.card ≤ I.card * (Δ + 1) := by
  classical
  let candidates : Finset (Finset V) := S.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, SimpleGraph.IsIndepSet, Set.Pairwise]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image candidates Finset.card hnonempty
  have hsub : I ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hind : G.IsIndepSet (I : Set V) := (Finset.mem_filter.mp hI).2
  have hcover : S ⊆ I.biUnion (fun v => insert v (G.neighborFinset v)) := by
    intro v hv
    by_contra hvcover
    have hvI : v ∉ I := by
      intro hvI
      apply hvcover
      exact Finset.mem_biUnion.mpr ⟨v, hvI, Finset.mem_insert_self _ _⟩
    have hnot : ∀ w ∈ I, ¬ G.Adj w v := by
      intro w hw hadj
      apply hvcover
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_insert_of_mem
        (by simpa using hadj)⟩
    have hnew : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
      intro u hu w hw huw
      simp only [Finset.mem_coe, Finset.mem_insert] at hu hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact False.elim (huw rfl)
      · exact fun ha => hnot w hw ha.symm
      · exact hnot u hu
      · exact hind hu hw huw
    have hinsert : insert v I ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hv hsub, hnew⟩
    have hc := hmax (insert v I) hinsert
    rw [Finset.card_insert_of_notMem hvI] at hc
    omega
  refine ⟨I, hsub, hind, ?_⟩
  calc
    S.card ≤ (I.biUnion (fun v => insert v (G.neighborFinset v))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ v ∈ I, (insert v (G.neighborFinset v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ I, (Δ + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [Finset.card_insert_of_notMem (by simp)]
      exact Nat.add_le_add_right (hΔ v) 1
    _ = I.card * (Δ + 1) := by simp

end GraphicalAllocation.Universal
