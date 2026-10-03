import GraphicalAllocation.Geometry.Graphs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Cyclic graph balls and discrete cyclic displacement

Vertices and paths are those of Mathlib's `SimpleGraph.cycleGraph`. Integer
lifts are proved from paths, so the ball bound does not postulate a graph-metric
comparison. Integer intervals automatically handle overlapping/wrapping arcs.
-/

namespace GraphicalAllocation.Geometry

open SimpleGraph

/-- A path on a cycle lifts to an integer displacement no larger in absolute
value than the path's length. -/
theorem cycle_walk_lift (n : ℕ) {u v : Fin (n + 3)}
    (w : (cycleGraph (n + 3)).Walk u v) :
    ∃ k : ℤ, |k| ≤ w.length ∧ v = u + k • (1 : Fin (n + 3)) := by
  induction w with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons u v z h w ih =>
    obtain ⟨k, hk, hz⟩ := ih
    rcases cycleGraph_adj.mp h with huv | hvu
    · refine ⟨k - 1, ?_, ?_⟩
      · have habs := abs_sub k 1
        norm_num at habs
        simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
      · have hv : v = u - 1 := by
          rw [sub_eq_iff_eq_add] at huv
          apply eq_sub_iff_add_eq.mpr
          simpa [add_comm] using huv.symm
        rw [hz, hv, sub_smul, one_smul]
        abel
    · refine ⟨k + 1, ?_, ?_⟩
      · have habs := abs_add_le k 1
        norm_num at habs
        simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
      · have hv : v = u + 1 := by rw [sub_eq_iff_eq_add] at hvu; simpa [add_comm] using hvu
        rw [hz, hv, add_smul, one_smul]
        abel

/-- A cycle ball is contained in the image of the signed interval `[-r,r]`. -/
theorem cycle_graphBall_subset_image (n : ℕ) (u : Fin (n + 3)) (r : ℕ) :
    graphBall (cycleGraph (n + 3)) u r ⊆
      (Finset.Icc (-(r : ℤ)) (r : ℤ)).image (fun k => u + k • (1 : Fin (n + 3))) := by
  intro v hv
  rw [mem_graphBall] at hv
  have hne : (cycleGraph (n + 3)).edist u v ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hv
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hwr : w.length ≤ r := by exact_mod_cast (hw ▸ hv : (w.length : ℕ∞) ≤ r)
  obtain ⟨k, hk, hvk⟩ := cycle_walk_lift n w
  apply Finset.mem_image.mpr
  refine ⟨k, ?_, hvk.symm⟩
  rw [Finset.mem_Icc]
  have hkr : |k| ≤ (r : ℤ) := hk.trans (by exact_mod_cast hwr)
  exact abs_le.mp hkr

/-- The `2r+1` cyclic ball bound, including wrap-around and sides of size 3. -/
theorem cycle_graphBall_card_le (n : ℕ) (u : Fin (n + 3)) (r : ℕ) :
    (graphBall (cycleGraph (n + 3)) u r).card ≤ 2 * r + 1 := by
  calc
    _ ≤ ((Finset.Icc (-(r : ℤ)) (r : ℤ)).image
        (fun k => u + k • (1 : Fin (n + 3)))).card :=
      Finset.card_le_card (cycle_graphBall_subset_image n u r)
    _ ≤ (Finset.Icc (-(r : ℤ)) (r : ℤ)).card := Finset.card_image_le
    _ = 2 * r + 1 := by rw [Int.card_Icc]; omega

/-- Cyclic balls also saturate at the whole finite vertex set. -/
theorem cycle_graphBall_card_le_min (n : ℕ) (u : Fin (n + 3)) (r : ℕ) :
    (graphBall (cycleGraph (n + 3)) u r).card ≤ min (n + 3) (2 * r + 1) := by
  apply le_min
  · simpa using Finset.card_le_univ (graphBall (cycleGraph (n + 3)) u r)
  · exact cycle_graphBall_card_le n u r

/-- Equation (7.6), for the actual torus graph metric. -/
theorem torus_graphBall_card_le (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) (r : ℕ) :
    (graphBall (cycleGraph (n + 3) □ cycleGraph (k + 3)) x r).card ≤
      (2 * r + 1) * min (k + 3) (2 * r + 1) := by
  exact (card_product_graphBall_le _ _ x r).trans
    (Nat.mul_le_mul (cycle_graphBall_card_le n x.1 r)
      (cycle_graphBall_card_le_min k x.2 r))

end GraphicalAllocation.Geometry
