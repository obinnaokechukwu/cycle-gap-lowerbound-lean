import GraphicalAllocation.Process.Allocation
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Bridging the actual allocation edges and canonical simple graphs

Every simple graph is given one orientation using a representative of each
unordered edge. Edge-specific monotone selectors can then be put directly on
this orientation; incidence degree and number of edge clocks are exactly the
canonical graph quantities.
-/

noncomputable section
namespace GraphicalAllocation.Geometry

open scoped BigOperators
open GraphicalAllocation.Process

variable {V : Type*}

/-- An orientation of a simple graph's actual unordered edge type. -/
def canonicalOrientation (G : SimpleGraph V) : OrientedGraph V G.edgeSet where
  tail e := e.val.out.1
  head e := e.val.out.2
  distinct e := by
    have he : G.Adj e.val.out.1 e.val.out.2 := by
      apply G.mem_edgeSet.mp
      simpa only [Sym2.mk, Prod.mk.eta, Quot.out_eq] using e.property
    exact he.ne
  unique e e' h := by
    apply Subtype.ext
    have he : s(e.val.out.1, e.val.out.2) = e.val := Quot.out_eq _
    have he' : s(e'.val.out.1, e'.val.out.2) = e'.val := Quot.out_eq _
    rw [← he, ← he']
    rcases h with h | h
    · rcases h with ⟨h₁, h₂⟩
      exact Sym2.eq_iff.mpr (Or.inl ⟨h₁, h₂⟩)
    · rcases h with ⟨h₁, h₂⟩
      exact Sym2.eq_iff.mpr (Or.inr ⟨h₁, h₂⟩)

/-- Incidence in the orientation is exactly membership of the unordered edge. -/
theorem canonical_incidence (G : SimpleGraph V) (e : G.edgeSet) (v : V) :
    v = (canonicalOrientation G).tail e ∨ v = (canonicalOrientation G).head e ↔
      v ∈ (e : Sym2 V) := by
  change (v = e.val.out.1 ∨ v = e.val.out.2) ↔ _
  conv_rhs => rw [← (Quot.out_eq e.val : s(e.val.out.1, e.val.out.2) = e.val)]
  exact Sym2.mem_iff.symm

/-- Choosing an orientation changes neither the clock count nor the edge count. -/
theorem canonical_edge_count [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : Fintype.card G.edgeSet = G.edgeFinset.card := by
  exact (Set.toFinset_card G.edgeSet).symm

/-- Incident oriented edges and the canonical graph incidence set are equivalent. -/
def incidentEdgeEquiv (G : SimpleGraph V) (v : V) :
    {e : G.edgeSet // v ∈ (e : Sym2 V)} ≃ G.incidenceSet v where
  toFun e := ⟨e.val.val, (G.edge_mem_incidenceSet_iff).mpr e.property⟩
  invFun e := ⟨⟨e.val, e.property.1⟩, e.property.2⟩
  left_inv _e := rfl
  right_inv _e := rfl

/-- The incidence degree used by the allocation model equals graph degree.
The rule's probabilities play no role, and may be arbitrary allowed antitone functions. -/
theorem allocation_degree_eq_graph_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : AllocationRule V G.edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation G) (v : V) :
    A.degree v = G.degree v := by
  classical
  unfold AllocationRule.degree
  have hinc (e : G.edgeSet) :
      (if v = A.tail e then 1 else 0) + (if v = A.head e then 1 else 0) =
        (if v ∈ (e : Sym2 V) then (1 : ℕ) else 0) := by
    have hneq := A.distinct e
    have hmem : (v = A.tail e ∨ v = A.head e) ↔ v ∈ (e : Sym2 V) := by
      rw [show A.tail = (canonicalOrientation G).tail from congrArg OrientedGraph.tail hA,
        show A.head = (canonicalOrientation G).head from congrArg OrientedGraph.head hA]
      exact canonical_incidence G e v
    by_cases ht : v = A.tail e <;> by_cases hh : v = A.head e <;>
      simp_all
  simp_rw [hinc]
  have hc : (∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then (1 : ℕ) else 0) =
      Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} := by simp [Fintype.card_subtype]
  rw [hc, Fintype.card_congr (incidentEdgeEquiv G v), G.card_incidenceSet_eq_degree]

end GraphicalAllocation.Geometry
