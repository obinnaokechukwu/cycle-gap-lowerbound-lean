import GraphicalAllocation.Spectral.TorusFourier

/-!
# Exact square-torus Green diagonal

The explicit mean-zero Fourier kernel is identified with the inverse of the
actual graph Laplacian by `green_unique`.  In particular its diagonal formula
is a theorem about the graph pseudoinverse, not an assumed spectral interface.
-/

noncomputable section
open scoped BigOperators Fin.CommRing
open SimpleGraph Matrix

namespace GraphicalAllocation.Spectral

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- The real part of a character translated to a specified source vertex. -/
def torusMode (n : ℕ) (a v : TorusVertex n) : TorusVertex n → ℝ :=
  fun x => (torusCharacter n a (x - v)).re

/-- Translations preserve the exact character eigenvector equation. -/
theorem torusMode_eigenvector (n : ℕ) (a v : TorusVertex n) :
    laplacian (torusGraph n) (torusMode n a v) =
      torusEigenvalue n a • torusMode n a v := by
  ext x
  calc
    laplacian (torusGraph n) (torusMode n a v) x =
        (((torusGraph n).lapMatrix ℂ *ᵥ torusCharacter n a) x *
          torusCharacter n a (-v)).re := by
      rw [laplacian_apply, torus_laplacian_apply, torus_laplacian_apply]
      simp only [torusMode, sub_eq_add_neg, torusCharacter_add]
      simp only [Complex.mul_re]
      norm_num
      ring
    _ = ((torusEigenvalue n a : ℂ) * torusCharacter n a x *
          torusCharacter n a (-v)).re := by rw [torusCharacter_eigenvector]
    _ = (torusEigenvalue n a • torusMode n a v) x := by
      rw [mul_assoc]
      simp [torusMode, sub_eq_add_neg, torusCharacter_add, Complex.mul_re]

/-- Nonconstant translated modes have zero mean. -/
theorem torusMode_mem_meanZero (n : ℕ) {a : TorusVertex n} (ha : a ≠ 0)
    (v : TorusVertex n) : torusMode n a v ∈ meanZero := by
  have hs : ∑ x, torusCharacter n a (x - v) = 0 := by
    simp only [sub_eq_add_neg, torusCharacter_add, ← Finset.sum_mul,
      sum_torusCharacter, ite_eq_right ha, zero_mul]
  have hr := congrArg Complex.re hs
  simpa [mem_meanZero, torusMode] using hr

/-- Finite Fourier construction of a Green column. -/
def torusGreenKernel (n : ℕ) (v : TorusVertex n) : TorusVertex n → ℝ :=
  ((n + 3 : ℝ)^2)⁻¹ • ∑ a ∈ (Finset.univ.erase (0 : TorusVertex n)),
    (torusEigenvalue n a)⁻¹ • torusMode n a v

theorem torusGreenKernel_mem (n : ℕ) (v : TorusVertex n) :
    torusGreenKernel n v ∈ meanZero := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  exact torusMode_mem_meanZero n (Finset.mem_erase.mp ha).1 v

/-- Character orthogonality reconstructs the centered point mass. -/
theorem torusMode_sum (n : ℕ) (v : TorusVertex n) :
    ∑ a ∈ Finset.univ.erase (0 : TorusVertex n), torusMode n a v =
      (n + 3 : ℝ)^2 • center (Pi.single v 1) := by
  ext x
  have hs := sum_torusCharacter n (x - v)
  simp_rw [torusCharacter_comm n (x - v)] at hs
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : TorusVertex n))] at hs
  have hr := congrArg Complex.re hs
  have hxv : x - v = 0 ↔ x = v := sub_eq_zero
  have hn : (n + 3 : ℝ) ≠ 0 := by positivity
  have hcast : (n + 3 : ℂ)^2 = (((n + 3 : ℝ)^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast] at hr
  simp only [torusCharacter_zero_frequency, Complex.add_re, Complex.one_re,
    Complex.re_sum, apply_ite, Complex.ofReal_re, Complex.zero_re, hxv] at hr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, torusMode, center_apply,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases hx : x = v
  · rw [ite_eq_left hx] at hr ⊢
    have hh : (n + 3 : ℝ)^2 * (1 - 1 / ((n + 3) * (n + 3))) = (n + 3)^2 - 1 := by
      field_simp
    rw [hh]
    linarith
  · rw [ite_eq_right hx] at hr ⊢
    have hh : (n + 3 : ℝ)^2 * (0 - 1 / ((n + 3) * (n + 3))) = -1 := by
      field_simp
      ring
    rw [hh]
    linarith

/-- The Fourier kernel solves the genuine graph Poisson equation. -/
theorem laplacian_torusGreenKernel (n : ℕ) (v : TorusVertex n) :
    laplacian (torusGraph n) (torusGreenKernel n v) = center (Pi.single v 1) := by
  simp only [torusGreenKernel, map_smul, map_sum, torusMode_eigenvector, smul_smul]
  have hc : (∑ a ∈ Finset.univ.erase (0 : TorusVertex n),
      ((torusEigenvalue n a)⁻¹ * torusEigenvalue n a) • torusMode n a v) =
        ∑ a ∈ Finset.univ.erase (0 : TorusVertex n), torusMode n a v := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [inv_mul_cancel₀ (ne_of_gt (torusEigenvalue_pos n (Finset.mem_erase.mp ha).1)),
      one_smul]
  rw [hc, torusMode_sum, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- The explicit kernel equals the actual connected-graph pseudoinverse. -/
theorem green_torus_eq_kernel (n : ℕ) (v : TorusVertex n) :
    green (torusGraph n) (torus_connected n) (Pi.single v 1) = torusGreenKernel n v :=
  green_unique _ _ (torusGreenKernel_mem n v) (laplacian_torusGreenKernel n v)

/-- Exact diagonal formula derived from the actual graph, uniform in the vertex. -/
theorem torus_greenDiagonal_formula (n : ℕ) (v : TorusVertex n) :
    greenDiagonal (torusGraph n) (torus_connected n) v =
      ((n + 3 : ℝ)^2)⁻¹ *
        ∑ a ∈ Finset.univ.erase (0 : TorusVertex n), (torusEigenvalue n a)⁻¹ := by
  rw [greenDiagonal, green_torus_eq_kernel]
  simp [torusGreenKernel, torusMode]

/-- Nonzero cyclic frequencies have strictly positive folded magnitude. -/
theorem folded_frequency_pos (n : ℕ) {a : Fin (n + 3)} (ha : a ≠ 0) :
    0 < ((min a.val (n + 3 - a.val) : ℕ) : ℝ) := by
  apply Nat.cast_pos.mpr
  apply lt_min
  · apply Nat.pos_of_ne_zero
    intro hz
    exact ha (Fin.ext (by simpa using hz))
  · omega

/-- The exact diagonal is bounded by the elementary folded-frequency sum. -/
theorem torus_greenDiagonal_le_frequency_sum (n : ℕ) (v : TorusVertex n) :
    greenDiagonal (torusGraph n) (torus_connected n) v ≤
      ∑ a ∈ Finset.univ.erase (0 : TorusVertex n),
        1 / (16 * (((min a.1.val (n + 3 - a.1.val) : ℕ) : ℝ)^2 +
          ((min a.2.val (n + 3 - a.2.val) : ℕ) : ℝ)^2)) := by
  rw [torus_greenDiagonal_formula, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have hs : 0 < ((min a.1.val (n + 3 - a.1.val) : ℕ) : ℝ)^2 +
      ((min a.2.val (n + 3 - a.2.val) : ℕ) : ℝ)^2 := by
    by_cases h₁ : a.1 = 0
    · have h₂ : a.2 ≠ 0 := by simpa [Prod.ext_iff, h₁] using hane
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (folded_frequency_pos n h₂))
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (folded_frequency_pos n h₁)) (sq_nonneg _)
  have hN : (n + 3 : ℝ) ≠ 0 := by positivity
  have heig := torusEigenvalue_lower n a
  have hi := inv_anti₀ (by positivity : 0 < 16 *
      (((min a.1.val (n + 3 - a.1.val) : ℕ) : ℝ)^2 +
        ((min a.2.val (n + 3 - a.2.val) : ℕ) : ℝ)^2) / (n + 3 : ℝ)^2) heig
  calc
    _ ≤ ((n + 3 : ℝ)^2)⁻¹ *
        (16 * (((min a.1.val (n + 3 - a.1.val) : ℕ) : ℝ)^2 +
          ((min a.2.val (n + 3 - a.2.val) : ℕ) : ℝ)^2) / (n + 3 : ℝ)^2)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp

end GraphicalAllocation.Spectral
