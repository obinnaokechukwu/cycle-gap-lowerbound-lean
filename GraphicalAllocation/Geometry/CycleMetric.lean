import GraphicalAllocation.Geometry.Cycle
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-! # The shortest-path metric of a cycle, computed by the canonical balanced residue -/

namespace GraphicalAllocation.Geometry
open SimpleGraph
open scoped Fin.CommRing

/-- Moving `k` steps forward yields a path of length at most `k`. -/
theorem cycle_dist_add_nat_le (n : ℕ) (u : Fin (n + 3)) (k : ℕ) :
    (cycleGraph (n + 3)).dist u (u + (k : Fin (n + 3))) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hadj : (cycleGraph (n + 3)).Adj (u + k) (u + (k + 1 : ℕ)) := by
      rw [cycleGraph_adj]
      right
      push_cast
      abel_nf
    have ht := (cycleGraph_connected (n := n + 2)).dist_triangle
      (u := u) (v := u + k) (w := u + (k + 1 : ℕ))
    rw [dist_eq_one_iff_adj.mpr hadj] at ht
    exact ht.trans (Nat.add_le_add_right ih 1)

/-- The corresponding estimate for an arbitrary signed integer displacement. -/
theorem cycle_dist_add_int_le (n : ℕ) (u : Fin (n + 3)) (k : ℤ) :
    (cycleGraph (n + 3)).dist u (u + (k : Fin (n + 3))) ≤ k.natAbs := by
  cases k with
  | ofNat k => simpa using cycle_dist_add_nat_le n u k
  | negSucc k =>
    have h := cycle_dist_add_nat_le n (u - (k + 1 : Fin (n + 3))) (k + 1)
    simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel] at h
    rw [SimpleGraph.dist_comm] at h
    simpa [Int.cast_negSucc, sub_eq_add_neg] using h

/-- Signed shortest representative of the difference of two cyclic vertices. -/
def cycleLift (n : ℕ) (u v : Fin (n + 3)) : ℤ :=
  (ZMod.finEquiv (n + 3) (v - u)).valMinAbs

@[simp] theorem cycleLift_cast (n : ℕ) (u v : Fin (n + 3)) :
    (cycleLift n u v : Fin (n + 3)) = v - u := by
  apply (ZMod.finEquiv (n + 3)).injective
  rw [map_intCast]
  exact ZMod.coe_valMinAbs _

/-- The canonical shortest integer representative bounds the graph distance. -/
theorem cycle_dist_le_lift (n : ℕ) (u v : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist u v ≤ (cycleLift n u v).natAbs := by
  convert cycle_dist_add_int_le n u (cycleLift n u v) using 1
  rw [cycleLift_cast]
  abel_nf

/-- Conversely, a shortest graph path cannot beat the balanced integer lift. -/
theorem cycle_lift_le_dist (n : ℕ) (u v : Fin (n + 3)) :
    (cycleLift n u v).natAbs ≤ (cycleGraph (n + 3)).dist u v := by
  obtain ⟨w, hw⟩ := (cycleGraph_connected (n := n + 2)).exists_walk_length_eq_dist u v
  obtain ⟨k, hk, hkv⟩ := cycle_walk_lift n w
  have hkcast : (k : ZMod (n + 3)) = ZMod.finEquiv (n + 3) (v - u) := by
    rw [hkv]
    simp [zsmul_eq_mul]
  have hmin : (cycleLift n u v).natAbs ≤ k.natAbs := by
    exact ZMod.natAbs_min_of_le_div_two (n + 3) _ _
      (by simpa only [cycleLift, ZMod.coe_valMinAbs] using hkcast.symm) (ZMod.natAbs_valMinAbs_le _)
  have hknat : k.natAbs ≤ w.length := by
    rw [← Int.natCast_natAbs] at hk
    exact_mod_cast hk
  exact hmin.trans (hw ▸ hknat)

/-- Exact shortest-path distance; no metric comparison is assumed. -/
theorem cycle_dist_eq_lift (n : ℕ) (u v : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist u v = (cycleLift n u v).natAbs :=
  le_antisymm (cycle_dist_le_lift n u v) (cycle_lift_le_dist n u v)

/-- Every cyclic distance is at most half the circumference. -/
theorem cycle_dist_le_half (n : ℕ) (u v : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist u v ≤ (n + 3) / 2 := by
  rw [cycle_dist_eq_lift]
  exact ZMod.natAbs_valMinAbs_le _

/-- The cyclic shortest-path metric is translation invariant. -/
theorem cycle_dist_translate (n : ℕ) (u v a : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist (u + a) (v + a) = (cycleGraph (n + 3)).dist u v := by
  simp only [cycle_dist_eq_lift, cycleLift]
  congr 3
  abel_nf

/-- Choosing either endpoint of two cyclic edges costs at most one in the
midpoint metric, not two: when both choices are the forward endpoint the
translation cancels exactly. -/
theorem cycle_endpoint_dist_le (n : ℕ) (a b u v : Fin (n + 3))
    (hu : u = a ∨ u = a + 1) (hv : v = b ∨ v = b + 1) :
    (cycleGraph (n + 3)).dist u v ≤ (cycleGraph (n + 3)).dist a b + 1 := by
  have hstep (x : Fin (n + 3)) : (cycleGraph (n + 3)).dist x (x + 1) = 1 := by
    apply dist_eq_one_iff_adj.mpr
    rw [cycleGraph_adj]
    right; abel
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
  · omega
  · have h := (cycleGraph_connected (n := n + 2)).dist_triangle
      (u := a) (v := b) (w := b + 1)
    rwa [hstep] at h
  · have h := (cycleGraph_connected (n := n + 2)).dist_triangle
      (u := a + 1) (v := a) (w := b)
    rw [SimpleGraph.dist_comm (u := a + 1) (v := a), hstep] at h
    simpa only [Nat.add_comm] using h
  · rw [cycle_dist_translate]
    omega

/-- The half-cycle shift is uniformly separated by the integer half-period. -/
theorem cycle_half_shift_dist (n : ℕ) (u : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist u (u + (((n + 3) / 2 : ℕ) : Fin (n + 3))) =
      (n + 3) / 2 := by
  rw [cycle_dist_eq_lift]
  unfold cycleLift
  have he : u + (((n + 3) / 2 : ℕ) : Fin (n + 3)) - u =
      (((n + 3) / 2 : ℕ) : Fin (n + 3)) := by abel
  rw [he, map_natCast, ZMod.valMinAbs_natCast_of_le_half (le_refl _)]
  omega

end GraphicalAllocation.Geometry
