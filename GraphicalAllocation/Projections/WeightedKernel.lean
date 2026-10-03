import GraphicalAllocation.Projections.Product
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp

/-!
# Positive weighted kernels as genuine orthogonal projections

Conjugation by the square roots of the atom weights identifies weighted
functions with Mathlib's Euclidean space. Detailed balance and idempotence then
imply the canonical `LinearMap.IsSymmetricProjection` predicate.
-/

noncomputable section

open scoped BigOperators Matrix
open WithLp

namespace GraphicalAllocation.Projections

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Conjugate a weighted kernel by the diagonal matrix of square-root weights. -/
def conjugateMatrix (μ : A → ℝ) (q : Matrix A A ℝ) : Matrix A A ℝ :=
  fun a b => Real.sqrt (μ a) * q a b / Real.sqrt (μ b)

/-- The square-root-weight realization of a scalar function in Euclidean space. -/
def weightedVector (μ : A → ℝ) (f : A → ℝ) : EuclideanSpace ℝ A :=
  toLp 2 (fun a => Real.sqrt (μ a) * f a)

omit [Fintype A] [DecidableEq A] in
@[simp] theorem weightedVector_apply (μ : A → ℝ) (f : A → ℝ) (a : A) :
    weightedVector μ f a = Real.sqrt (μ a) * f a := rfl

omit [Fintype A] [DecidableEq A] in
lemma sqrt_weight_ne_zero {μ : A → ℝ} (hμ : ∀ a, 0 < μ a) (a : A) :
    Real.sqrt (μ a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hμ a))

omit [Fintype A] [DecidableEq A] in
/-- Detailed balance becomes ordinary symmetry after conjugation. -/
theorem conjugateMatrix_isHermitian {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : Matrix A A ℝ) (hbal : ∀ a b, μ a * q a b = μ b * q b a) :
    (conjugateMatrix μ q).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, conjugateMatrix]
  field_simp [sqrt_weight_ne_zero hμ a, sqrt_weight_ne_zero hμ b]
  have h := hbal b a
  rw [← Real.sq_sqrt (hμ a).le, ← Real.sq_sqrt (hμ b).le] at h
  nlinarith only [h]

omit [DecidableEq A] in
/-- Kernel idempotence survives the square-root conjugation. -/
theorem conjugateMatrix_idempotent {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : Matrix A A ℝ) (hidem : q * q = q) :
    conjugateMatrix μ q * conjugateMatrix μ q = conjugateMatrix μ q := by
  ext a b
  simp only [Matrix.mul_apply]
  calc
    _ = ∑ c, (Real.sqrt (μ a) / Real.sqrt (μ b)) * (q a c * q c b) := by
      apply Finset.sum_congr rfl
      intro c _
      unfold conjugateMatrix
      field_simp [sqrt_weight_ne_zero hμ a, sqrt_weight_ne_zero hμ b,
        sqrt_weight_ne_zero hμ c]
    _ = (Real.sqrt (μ a) / Real.sqrt (μ b)) * (q * q) a b := by
      rw [← Finset.mul_sum, Matrix.mul_apply]
    _ = _ := by rw [hidem]; unfold conjugateMatrix; ring

/-- A reversible idempotent finite kernel is an orthogonal projection in the
canonical Euclidean-space Hilbert structure. -/
theorem conjugateMatrix_isSymmetricProjection {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : Matrix A A ℝ) (hbal : ∀ a b, μ a * q a b = μ b * q b a)
    (hidem : q * q = q) :
    (conjugateMatrix μ q).toEuclideanLin.IsSymmetricProjection := by
  constructor
  · change (conjugateMatrix μ q).toEuclideanLin ∘ₗ
      (conjugateMatrix μ q).toEuclideanLin = _
    rw [← Matrix.toLpLin_mul_same, conjugateMatrix_idempotent hμ q hidem]
  · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (conjugateMatrix_isHermitian hμ q hbal)

/-- The conjugated operator performs exactly the original kernel average. -/
theorem conjugateMatrix_apply_weighted {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : Matrix A A ℝ) (f : A → ℝ) :
    (conjugateMatrix μ q).toEuclideanLin (weightedVector μ f) =
      weightedVector μ (q *ᵥ f) := by
  ext a
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, weightedVector,
    PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold conjugateMatrix
  field_simp [sqrt_weight_ne_zero hμ b]

omit [DecidableEq A] in
/-- The Euclidean inner product is the original weighted inner product. -/
theorem inner_weightedVector {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f g : A → ℝ) :
    inner ℝ (weightedVector μ f) (weightedVector μ g) = ∑ a, μ a * f a * g a := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedVector_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = (Real.sqrt (μ a)) ^ 2 * f a * g a := by ring
    _ = _ := by rw [Real.sq_sqrt (hμ a)]

omit [DecidableEq A] in
/-- The Euclidean norm is the original weighted second moment. -/
theorem norm_weightedVector_sq {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f : A → ℝ) :
    ‖weightedVector μ f‖ ^ 2 = ∑ a, μ a * (f a) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedVector_apply, mul_pow, Real.sq_sqrt (hμ a)]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem weightedVector_sub (μ : A → ℝ) (f g : A → ℝ) :
    weightedVector μ (f - g) = weightedVector μ f - weightedVector μ g := by
  ext a
  simp [weightedVector, mul_sub]

/-- Apply the kernels in displayed reverse-product order. -/
def kernelOrbit (q : ℕ → Matrix A A ℝ) (f : A → ℝ) : ℕ → A → ℝ
  | 0 => f
  | n + 1 => q n *ᵥ kernelOrbit q f n

/-- The conjugation intertwines every ordered product, not just one step. -/
theorem linearOrbit_weighted {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : ℕ → Matrix A A ℝ) (f : A → ℝ) (n : ℕ) :
    linearOrbit (fun j => (conjugateMatrix μ (q j)).toEuclideanLin)
      (weightedVector μ f) n = weightedVector μ (kernelOrbit q f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [linearOrbit, kernelOrbit]
      rw [ih, conjugateMatrix_apply_weighted hμ]

/-- The product estimate written entirely in the original atom weights. -/
theorem weighted_product_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : ℕ → Matrix A A ℝ)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a)
    (hidem : ∀ j, q j * q j = q j) (f : A → ℝ) (n : ℕ) :
    (∑ a, μ a * f a * (f a - kernelOrbit q f n a)) ≤
      2 * ∑ j ∈ Finset.range n, ∑ a, μ a * (f a - (q j *ᵥ f) a) ^ 2 := by
  have h := linear_product_re_inner_le
    (fun j => (conjugateMatrix μ (q j)).toEuclideanLin)
    (fun j => conjugateMatrix_isSymmetricProjection hμ (q j) (hbal j) (hidem j))
    (weightedVector μ f) n
  rw [linearOrbit_weighted hμ] at h
  simp_rw [conjugateMatrix_apply_weighted hμ, ← weightedVector_sub,
    inner_weightedVector (fun a => (hμ a).le),
    norm_weightedVector_sq (fun a => (hμ a).le)] at h
  exact h

end GraphicalAllocation.Projections
