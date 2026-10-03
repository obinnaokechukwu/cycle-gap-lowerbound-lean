import GraphicalAllocation.Spectral.Radius
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The Green diagonal of a cycle

A quadratic potential solves the discrete Poisson equation directly.  This
avoids a Fourier-series prerequisite and covers the triangle without exceptions.
-/

noncomputable section
open scoped BigOperators Fin.CommRing
open Matrix SimpleGraph

namespace GraphicalAllocation.Spectral

/-- A pinned quadratic potential before subtracting its average. -/
def cyclePotential (n : ℕ) (w : Fin (n + 3)) : ℝ :=
  ((w.val : ℝ)^2 - (n + 3) * w.val) / (2 * (n + 3))

theorem cyclePotential_zero (n : ℕ) : cyclePotential n 0 = 0 := by
  simp [cyclePotential]

theorem cyclePotential_recurrence (n : ℕ) (w : Fin (n + 3)) :
    2 * cyclePotential n w -
      (cyclePotential n (w - 1) + cyclePotential n (w + 1)) =
      (if w = 0 then 1 else 0) - 1 / (n + 3 : ℝ) := by
  have hn : (n + 3 : ℝ) ≠ 0 := by positivity
  by_cases hw : w = 0
  · subst w
    simp [cyclePotential]
    field_simp
    ring
  · have hwpos : 1 ≤ w.val := by
      by_contra hh
      have hz : w.val = 0 := by omega
      exact hw (Fin.ext hz)
    have hm : ((w - 1).val : ℝ) = (w.val : ℝ) - 1 := by
      rw [Fin.val_sub_one_of_ne_zero hw, Nat.cast_sub hwpos, Nat.cast_one]
    by_cases hp : w.val + 1 < n + 3
    · have hv : ((w + 1).val : ℝ) = (w.val : ℝ) + 1 := by
        rw [Fin.val_add_one_of_lt' hp, Nat.cast_add, Nat.cast_one]
      simp only [cyclePotential, hm, hv, ite_eq_right hw]
      field_simp
      ring
    · have hlast : w.val = n + 2 := by omega
      have hv : (w + 1).val = 0 := by
        simp only [Fin.val_add, Fin.val_one, hlast]
        have he : n + 2 + 1 = n + 3 := by omega
        rw [he, Nat.mod_self]
      simp only [cyclePotential, hm, hv, hlast, ite_eq_right hw, Nat.cast_add, Nat.cast_ofNat]
      field_simp
      ring

theorem cycle_laplacian_apply (n : ℕ) (x : Fin (n + 3) → ℝ) (w : Fin (n + 3)) :
    laplacian (cycleGraph (n + 3)) x w = 2 * x w - (x (w - 1) + x (w + 1)) := by
  have hne : w - 1 ≠ w + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc w, left_eq_add]
    exact ne_of_beq_false rfl
  simp [SimpleGraph.lapMatrix_mulVec_apply, cycleGraph_degree_three_le,
    cycleGraph_neighborFinset, Finset.sum_pair hne]

/-- Translation of the pinned quadratic solves every centered point source. -/
theorem cyclePotential_poisson (n : ℕ) (v : Fin (n + 3)) :
    laplacian (cycleGraph (n + 3)) (fun w => cyclePotential n (w - v)) =
      center (Pi.single v 1) := by
  ext w
  rw [cycle_laplacian_apply]
  have hm : w - 1 - v = (w - v) - 1 := by ring
  have hp : w + 1 - v = (w - v) + 1 := by ring
  rw [hm, hp, cyclePotential_recurrence]
  simp [center_apply, sub_eq_zero, Pi.single_apply, eq_comm]

theorem cycle_green_formula (n : ℕ) (v : Fin (n + 3)) :
    green (cycleGraph (n + 3)) (cycleGraph_connected (n := n + 2)) (Pi.single v 1) =
      center (fun w => cyclePotential n (w - v)) := by
  apply green_unique _ _ (center_mem _)
  rw [laplacian_center, cyclePotential_poisson]

/-- A pointwise quadratic estimate sufficient for the paper's constant. -/
theorem neg_cyclePotential_le (n : ℕ) (w : Fin (n + 3)) :
    -cyclePotential n w ≤ (n + 3 : ℝ) / 4 := by
  have hn : 0 < (2 * (n + 3 : ℝ)) := by positivity
  rw [cyclePotential, ← neg_div, div_le_iff₀ hn]
  nlinarith [sq_nonneg ((w.val : ℝ) - (n + 3) / 2)]

/-- The cycle diagonal estimate, including every cycle with at least three vertices. -/
theorem cycle_greenDiagonal_le (n : ℕ) (v : Fin (n + 3)) :
    greenDiagonal (cycleGraph (n + 3)) (cycleGraph_connected (n := n + 2)) v ≤
      (n + 3 : ℝ) / 4 := by
  unfold greenDiagonal
  rw [cycle_green_formula, center_apply, sub_self, cyclePotential_zero, zero_sub]
  have hs : (∑ w : Fin (n + 3), -cyclePotential n (w - v)) ≤
      (n + 3 : ℝ) * ((n + 3 : ℝ) / 4) := by
    calc
      _ ≤ ∑ _w : Fin (n + 3), (n + 3 : ℝ) / 4 :=
        Finset.sum_le_sum (fun w _ => neg_cyclePotential_le n (w - v))
      _ = _ := by simp
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
  rw [← neg_div, div_le_iff₀ (by positivity : (0 : ℝ) < n + 3)]
  simpa [Finset.sum_neg_distrib, mul_comm] using hs

theorem cycle_greenRadius_le (n : ℕ) :
    greenRadius (cycleGraph (n + 3)) (cycleGraph_connected (n := n + 2)) ≤
      (n + 3 : ℝ) / 4 :=
  greenRadius_le _ _ (cycle_greenDiagonal_le n)

end GraphicalAllocation.Spectral
