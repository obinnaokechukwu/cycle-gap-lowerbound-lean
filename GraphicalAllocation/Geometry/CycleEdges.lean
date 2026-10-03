import GraphicalAllocation.Geometry.Oriented
import GraphicalAllocation.Geometry.CycleMetric
import Mathlib.Tactic

/-! # Cyclic orientations and the sharp four-fiber support bound -/

noncomputable section
namespace GraphicalAllocation.Geometry

open SimpleGraph GraphicalAllocation.Process
open scoped Fin.CommRing

/-- Orient every cycle edge from `e` to `e+1`. The edge index type has exactly
as many elements as the vertex type. -/
def cycleOrientation (n : ℕ) : OrientedGraph (Fin (n + 3)) (Fin (n + 3)) where
  tail e := e
  head e := e + 1
  distinct e := by
    intro h
    have h' : e + 1 = e + 0 := by simpa using h.symm
    have hz : (1 : Fin (n + 3)) = 0 := add_left_cancel h'
    have := congrArg Fin.val hz
    norm_num at this
  unique e e' h := by
    rcases h with ⟨h, _⟩ | ⟨h₁, h₂⟩
    · exact h
    · have hz : (2 : Fin (n + 3)) = 0 := by
        have : e = e + 2 := by
          calc
            e = e' + 1 := h₁
            _ = (e + 1) + 1 := congrArg (fun x => x + 1) h₂.symm
            _ = e + 2 := by ring
        exact add_left_cancel (a := e) (by simpa only [add_zero] using this.symm)
      have hv := congrArg Fin.val hz
      have hn : 2 < n + 3 := by omega
      simp [Nat.mod_eq_of_lt hn] at hv

/-- Every edge in this orientation is an actual canonical cycle edge. -/
theorem cycleOrientation_adj (n : ℕ) (e : Fin (n + 3)) :
    (cycleGraph (n + 3)).Adj ((cycleOrientation n).tail e) ((cycleOrientation n).head e) := by
  change (cycleGraph (n + 3)).Adj e (e + 1)
  rw [cycleGraph_adj]
  right
  abel

/-- Conversely, the cyclic orientation contains every canonical cycle edge. -/
theorem cycleOrientation_covers (n : ℕ) {u v : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj u v) :
    ∃ e, (u = (cycleOrientation n).tail e ∧ v = (cycleOrientation n).head e) ∨
      (u = (cycleOrientation n).head e ∧ v = (cycleOrientation n).tail e) := by
  rcases cycleGraph_adj.mp h with h | h
  · refine ⟨v, Or.inr ⟨?_, rfl⟩⟩
    change u = v + 1
    simpa [add_comm] using sub_eq_iff_eq_add.mp h
  · refine ⟨u, Or.inl ⟨rfl, ?_⟩⟩
    change v = u + 1
    simpa [add_comm] using sub_eq_iff_eq_add.mp h

/-- At an update at `w`, only these four cyclic edge fibers can be affected.
The finite set intentionally permits coincidences when the cycle is short. -/
def fourCycleFibers (n : ℕ) (w : Fin (n + 3)) : Finset (Fin (n + 3)) :=
  {w - 2, w - 1, w, w + 1}

/-- The support bound holds for `n=3,4` as well, without requiring distinct fibers. -/
theorem card_fourCycleFibers_le (n : ℕ) (w : Fin (n + 3)) :
    (fourCycleFibers n w).card ≤ 4 := by
  have h₁ := Finset.card_insert_le (w - 2) ({w - 1, w, w + 1} : Finset (Fin (n + 3)))
  have h₂ := Finset.card_insert_le (w - 1) ({w, w + 1} : Finset (Fin (n + 3)))
  have h₃ := Finset.card_insert_le w ({w + 1} : Finset (Fin (n + 3)))
  simp only [Finset.card_singleton] at h₃
  unfold fourCycleFibers
  omega

/-- Every fiber incident to the closed neighborhood is one of the four listed fibers. -/
theorem incident_closedNeighborhood_mem_fourCycleFibers (n : ℕ)
    (w v e : Fin (n + 3))
    (hv : v ∈ insert w ((cycleGraph (n + 3)).neighborFinset w))
    (he : v = (cycleOrientation n).tail e ∨ v = (cycleOrientation n).head e) :
    e ∈ fourCycleFibers n w := by
  have hv' : v = w ∨ v = w - 1 ∨ v = w + 1 := by
    simpa [cycleGraph_neighborFinset, eq_comm, or_assoc] using hv
  have he' : e = v ∨ e = v - 1 := by
    rcases he with h | h
    · exact Or.inl h.symm
    · right
      apply eq_sub_iff_add_eq.mpr
      exact h.symm
  have h₁ : w - 1 - 1 = w - 2 := by ring
  have h₂ : w + 1 - 1 = w := by ring
  rcases hv' with rfl | rfl | rfl <;> rcases he' with rfl | rfl <;>
    simp [fourCycleFibers, h₁, h₂]

/-- Every allowed allocation rule on the cyclic orientation has incidence degree two. -/
theorem cycle_allocation_degree (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n) (v : Fin (n + 3)) :
    A.degree v = 2 := by
  have ht (e : Fin (n + 3)) : A.tail e = e := congrFun (congrArg OrientedGraph.tail hA) e
  have hh (e : Fin (n + 3)) : A.head e = e + 1 := congrFun (congrArg OrientedGraph.head hA) e
  have he (e : Fin (n + 3)) : (v = e + 1) ↔ e = v - 1 := by
    rw [eq_sub_iff_add_eq, eq_comm]
  unfold AllocationRule.degree
  simp_rw [ht, hh, he]
  rw [Finset.sum_add_distrib]
  simp

/-- The same single permutation is used at every lag in cylinder/torus tests. -/
def cycleHalfShift (n : ℕ) : Equiv.Perm (Fin (n + 3)) :=
  Equiv.addRight (((n + 3) / 2 : ℕ) : Fin (n + 3))

@[simp] theorem cycleHalfShift_apply (n : ℕ) (u : Fin (n + 3)) :
    cycleHalfShift n u = u + (((n + 3) / 2 : ℕ) : Fin (n + 3)) := rfl

/-- Uniform separation of the fixed half-period permutation. -/
theorem cycleHalfShift_separated (n r : ℕ) (hr : 2 * r ≤ (n + 3) / 2)
    (u : Fin (n + 3)) :
    2 * r ≤ (cycleGraph (n + 3)).dist u (cycleHalfShift n u) := by
  rw [cycleHalfShift_apply, cycle_half_shift_dist]
  exact hr

end GraphicalAllocation.Geometry
