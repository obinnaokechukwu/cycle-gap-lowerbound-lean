import GraphicalAllocation.Spectral.TorusGreen
import GraphicalAllocation.Spectral.TorusBounds
import GraphicalAllocation.Spectral.Radius

/-!
# The square-torus Green radius is at most `1 + log L`

The frequency estimate is applied to the diagonal of the actual graph inverse,
whose Fourier representation was established from its Poisson equation.
-/

noncomputable section
namespace GraphicalAllocation.Spectral

attribute [local instance] Classical.propDecidable

/-- The diagonal estimate in the Gaussian-free-field comparison remark, for every vertex of `C_L □ C_L`. -/
theorem torus_greenDiagonal_le_one_add_log (n : ℕ) (v : TorusVertex n) :
    greenDiagonal (torusGraph n) (torus_connected n) v ≤ 1 + Real.log (n + 3) := by
  exact (torus_greenDiagonal_le_frequency_sum n v).trans
    (by simpa only [foldedFrequency] using torus_folded_frequency_sum_le n)

/-- The exact bound `R_G ≤ 1 + log L` for the actual square-torus graph. -/
theorem torus_greenRadius_le_one_add_log (n : ℕ) :
    greenRadius (torusGraph n) (torus_connected n) ≤ 1 + Real.log (n + 3) :=
  greenRadius_le _ _ (torus_greenDiagonal_le_one_add_log n)

end GraphicalAllocation.Spectral
