import GraphicalAllocation.Spectral.Green

/-! # Matrix form of the graph Green operator for covariance constructions -/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- The actual matrix of the graph Laplacian pseudoinverse. -/
def greenMatrix : Matrix V V ℝ := LinearMap.toMatrix' (green G hG)

@[simp] theorem greenMatrix_apply (u v : V) :
    greenMatrix G hG u v = green G hG (Pi.single v 1) u := rfl

@[simp] theorem greenMatrix_mulVec (x : V → ℝ) :
    greenMatrix G hG *ᵥ x = green G hG x := LinearMap.toMatrix'_mulVec _ _

@[simp] theorem greenMatrix_diagonal (v : V) :
    greenMatrix G hG v v = greenDiagonal G hG v := rfl

theorem greenMatrix_isSymm : (greenMatrix G hG).IsSymm := by
  apply Matrix.IsSymm.ext
  intro u v
  simpa using green_self_adjoint G hG (Pi.single v 1) (Pi.single u 1)

theorem greenMatrix_isHermitian : (greenMatrix G hG).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (greenMatrix_isSymm G hG)

theorem greenMatrix_posSemidef : (greenMatrix G hG).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (greenMatrix_isHermitian G hG)
  intro x
  simpa only [star_trivial, greenMatrix_mulVec, energy] using energy_nonneg G hG x

theorem greenMatrix_mulVec_one : greenMatrix G hG *ᵥ (1 : V → ℝ) = 0 := by
  rw [greenMatrix_mulVec]
  exact green_constant G hG 1

theorem greenMatrix_column_sum (v : V) : ∑ u, greenMatrix G hG u v = 0 :=
  green_mem G hG (Pi.single v 1)

theorem greenMatrix_row_sum (v : V) : ∑ u, greenMatrix G hG v u = 0 := by
  have h := congrFun (greenMatrix_mulVec_one G hG) v
  simpa [Matrix.mulVec, dotProduct] using h

end GraphicalAllocation.Spectral
