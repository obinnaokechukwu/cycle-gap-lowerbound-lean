import GraphicalAllocation.Process.Allocation
import Mathlib.Data.Finset.Card

/-! # Actual oriented-graph neighborhoods

A closed neighborhood is constructed from the model's own edge endpoints.
Its size bound does not require connectedness or a special orientation.
-/

namespace GraphicalAllocation.Process.AllocationRule
open scoped BigOperators
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The finite set of edge clocks incident to a vertex. -/
def incidentEdges (A : AllocationRule V E) (v : V) : Finset E :=
  Finset.univ.filter (fun e => A.tail e = v ∨ A.head e = v)

/-- The other endpoint of an edge known to be incident to v. -/
def opposite (A : AllocationRule V E) (v : V) (e : E) : V :=
  if A.tail e = v then A.head e else A.tail e

/-- The closed neighborhood, constructed directly from actual model edges. -/
def closedNeighborhood (A : AllocationRule V E) (v : V) : Finset V :=
  insert v ((A.incidentEdges v).image (A.opposite v))

omit [Fintype V] [DecidableEq E] in
lemma incidentEdges_card (A : AllocationRule V E) (v : V) :
    (A.incidentEdges v).card = A.degree v := by
  unfold incidentEdges AllocationRule.degree
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := A.distinct e
  by_cases ht : A.tail e = v <;> by_cases hh : A.head e = v <;> simp_all [eq_comm]

omit [Fintype V] [DecidableEq E] in
lemma closedNeighborhood_card_le (A : AllocationRule V E) (v : V) :
    (A.closedNeighborhood v).card ≤ A.degree v + 1 := by
  unfold closedNeighborhood
  calc
    _ ≤ ((A.incidentEdges v).image (A.opposite v)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (A.incidentEdges v).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ = _ := by rw [incidentEdges_card]

omit [Fintype V] [DecidableEq E] in
lemma endpoints_mem_closedNeighborhood (A : AllocationRule V E) (v : V) (e : E)
    (he : A.tail e = v ∨ A.head e = v) :
    A.tail e ∈ A.closedNeighborhood v ∧ A.head e ∈ A.closedNeighborhood v := by
  have hi : e ∈ A.incidentEdges v := by simp [incidentEdges, he]
  have ho : A.opposite v e ∈ A.closedNeighborhood v :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, hi, rfl⟩)
  have hv : v ∈ A.closedNeighborhood v := Finset.mem_insert_self _ _
  rcases he with ht | hh
  · simpa [opposite, ht] using And.intro hv ho
  · by_cases ht : A.tail e = v
    · simpa [ht, hh] using And.intro hv hv
    · simpa [opposite, ht, hh] using And.intro ho hv

end GraphicalAllocation.Process.AllocationRule
