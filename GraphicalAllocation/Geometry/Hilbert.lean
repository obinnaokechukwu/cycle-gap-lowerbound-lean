import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic

/-!
# Cell variance and edge midpoints

A cell has an arbitrary finite probability law, including zero-weight atoms.
The variance bound is derived from the mean-square minimizing property, rather
than assumed as part of a projection or allocation structure.
-/

noncomputable section

namespace GraphicalAllocation.Geometry

open scoped BigOperators

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Barycenter of a finite real-weighted law. -/
def weightedMean (w : ι → ℝ) (x : ι → H) : H := ∑ i, w i • x i

/-- Expansion of the second moment around any proposed center. -/
theorem weighted_square_expansion (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (x : ι → H) (c : H) :
    (∑ i, w i * ‖x i - c‖ ^ 2) =
      (∑ i, w i * ‖x i‖ ^ 2) - 2 * inner ℝ (weightedMean w x) c + ‖c‖ ^ 2 := by
  have hcross : (∑ i, w i * inner ℝ (x i) c) =
      inner ℝ (weightedMean w x) c := by
    simp [weightedMean, sum_inner, real_inner_smul_left]
  simp_rw [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hw, one_mul]
  have : (∑ i, w i * (2 * inner ℝ (x i) c)) =
      2 * inner ℝ (weightedMean w x) c := by
    rw [← hcross, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [this]

/-- The finite-law variance decomposition; nonnegative weights are not needed
for this algebraic identity, only unit total mass. -/
theorem weighted_variance_decomposition (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (x : ι → H) (c : H) :
    (∑ i, w i * ‖x i - c‖ ^ 2) =
      (∑ i, w i * ‖x i - weightedMean w x‖ ^ 2) +
        ‖weightedMean w x - c‖ ^ 2 := by
  rw [weighted_square_expansion w hw x c,
    weighted_square_expansion w hw x (weightedMean w x), norm_sub_sq_real,
    real_inner_self_eq_norm_sq]
  ring

/-- The conditional mean minimizes squared error. -/
theorem weighted_variance_le_center (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (x : ι → H) (c : H) :
    (∑ i, w i * ‖x i - weightedMean w x‖ ^ 2) ≤
      ∑ i, w i * ‖x i - c‖ ^ 2 := by
  rw [weighted_variance_decomposition w hw x c]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A probability law supported in a Hilbert ball of radius `r` has variance
at most `r²`. Zero-weight atoms need not lie in the ball. -/
theorem weighted_variance_le_radius_sq (w : ι → ℝ) (hpos : ∀ i, 0 ≤ w i)
    (hw : ∑ i, w i = 1) (x : ι → H) (c : H) (r : ℝ) (hr : 0 ≤ r)
    (hball : ∀ i, w i ≠ 0 → ‖x i - c‖ ≤ r) :
    (∑ i, w i * ‖x i - weightedMean w x‖ ^ 2) ≤ r ^ 2 := by
  calc
    _ ≤ ∑ i, w i * ‖x i - c‖ ^ 2 := weighted_variance_le_center w hw x c
    _ ≤ ∑ i, w i * r ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : w i = 0
      · simp [hz]
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hr).mpr (hball i hz)) (hpos i)
    _ = r ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]

/-- Algebraic edge midpoint. -/
abbrev edgeMidpoint (a b : H) : H := midpoint ℝ a b

@[simp] theorem norm_edgeMidpoint_sub_left (a b : H) :
    ‖edgeMidpoint a b - a‖ = ‖b - a‖ / 2 := by
  have : edgeMidpoint a b - a = (1 / 2 : ℝ) • (b - a) := by
    rw [edgeMidpoint, midpoint_eq_smul_add]
    norm_num
    module
  rw [this, norm_smul]
  norm_num
  ring

@[simp] theorem norm_edgeMidpoint_sub_right (a b : H) :
    ‖edgeMidpoint a b - b‖ = ‖a - b‖ / 2 := by
  rw [edgeMidpoint, midpoint_comm]
  exact norm_edgeMidpoint_sub_left b a

/-- Midpoints of edges incident to `v` lie within `η/2` of `F(v)`. -/
theorem midpoint_cell_variance (w : ι → ℝ) (hpos : ∀ i, 0 ≤ w i)
    (hw : ∑ i, w i = 1) (v : H) (endpoint : ι → H)
    (η : ℝ) (hη : 0 ≤ η)
    (hedge : ∀ i, w i ≠ 0 → ‖endpoint i - v‖ ≤ η) :
    (∑ i, w i * ‖edgeMidpoint v (endpoint i) -
      weightedMean w (fun i => edgeMidpoint v (endpoint i))‖ ^ 2) ≤ η ^ 2 / 4 := by
  have h := weighted_variance_le_radius_sq w hpos hw
    (fun i => edgeMidpoint v (endpoint i)) v (η / 2) (by positivity)
    (fun i hi => by
      rw [norm_edgeMidpoint_sub_left]
      exact div_le_div_of_nonneg_right (hedge i hi) (by norm_num))
  convert h using 1
  ring

end GraphicalAllocation.Geometry
