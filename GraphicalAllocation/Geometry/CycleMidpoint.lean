import GraphicalAllocation.Geometry.Fourier
import GraphicalAllocation.Geometry.CycleEdges
import GraphicalAllocation.Geometry.Hilbert
import Mathlib.Tactic

/-! # Actual midpoint Fourier observable and the two-point cell radius -/

noncomputable section
namespace GraphicalAllocation.Geometry
open SimpleGraph
open scoped Fin.CommRing

/-- The Fourier coordinate of the midpoint of oriented edge `e=(e,e+1)`. -/
def cycleMidpointFourier (n : ℕ) (e : Fin (n + 3)) : ℂ :=
  Complex.exp ((Real.pi / (n + 3) : ℝ) * Complex.I) * cycleFourier n e

/-- A common half-edge rotation preserves every Fourier chord. -/
theorem cycleMidpointFourier_chord (n : ℕ) (a b : Fin (n + 3)) :
    ‖cycleMidpointFourier n b - cycleMidpointFourier n a‖ =
      ‖cycleFourier n b - cycleFourier n a‖ := by
  rw [cycleMidpointFourier, cycleMidpointFourier, ← mul_sub, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Midpoint Fourier values are unit vectors. -/
@[simp] theorem norm_cycleMidpointFourier (n : ℕ) (e : Fin (n + 3)) :
    ‖cycleMidpointFourier n e‖ = 1 := by
  rw [cycleMidpointFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_cycleFourier, one_mul]

/-- The center of the two possible Fourier midpoint values at vertex `v`. -/
def cycleCellCenter (n : ℕ) (v : Fin (n + 3)) : ℂ :=
  midpoint ℝ (cycleMidpointFourier n v) (cycleMidpointFourier n (v - 1))

/-- The two possible midpoint values in a selection cell are separated by
exactly `2 sin(π/N)`. -/
theorem cycle_cell_chord (n : ℕ) (v : Fin (n + 3)) :
    ‖cycleMidpointFourier n (v - 1) - cycleMidpointFourier n v‖ =
      2 * Real.sin (Real.pi / (n + 3)) := by
  rw [cycleMidpointFourier_chord]
  apply cycleFourier_edge
  rw [cycleGraph_adj]
  left; abel

/-- Every possible marked edge in a cell lies in a Hilbert ball of radius
`sin(π/N)`, uniformly over all endpoint selection rules and threshold marks. -/
theorem cycle_cell_radius (n : ℕ) (v e : Fin (n + 3))
    (he : v = (cycleOrientation n).tail e ∨ v = (cycleOrientation n).head e) :
    ‖cycleMidpointFourier n e - cycleCellCenter n v‖ =
      Real.sin (Real.pi / (n + 3)) := by
  have he' : e = v ∨ e = v - 1 := by
    rcases he with h | h
    · exact Or.inl h.symm
    · exact Or.inr (eq_sub_iff_add_eq.mpr h.symm)
  rcases he' with rfl | rfl
  · rw [norm_sub_rev, cycleCellCenter, norm_edgeMidpoint_sub_left, cycle_cell_chord]
    ring
  · rw [norm_sub_rev, cycleCellCenter, norm_edgeMidpoint_sub_right, norm_sub_rev,
      cycle_cell_chord]
    ring

/-- The cell conditional variance estimate in Proposition 4.3, allowing
arbitrary nonnegative atom weights and zero-weight atoms. -/
theorem cycle_cell_variance {ι : Type*} [Fintype ι] (n : ℕ)
    (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (edge : ι → Fin (n + 3)) (v : Fin (n + 3))
    (hcell : ∀ i, w i ≠ 0 →
      v = (cycleOrientation n).tail (edge i) ∨ v = (cycleOrientation n).head (edge i)) :
    (∑ i, w i * ‖cycleMidpointFourier n (edge i) -
      weightedMean w (fun j => cycleMidpointFourier n (edge j))‖ ^ 2) ≤
        Real.sin (Real.pi / (n + 3)) ^ 2 := by
  apply weighted_variance_le_radius_sq w hw₀ hw
    (fun i => cycleMidpointFourier n (edge i)) (cycleCellCenter n v) _ (cycle_sin_pos n).le
  intro i hi
  exact (cycle_cell_radius n v (edge i) (hcell i hi)).le

end GraphicalAllocation.Geometry
