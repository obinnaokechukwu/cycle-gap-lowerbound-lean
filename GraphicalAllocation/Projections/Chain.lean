import GraphicalAllocation.Projections.WeightedKernel
import GraphicalAllocation.Projections.Geometry

/-!
# Finite stationary projection chains

The forward Markov product and reverse function-operator product are kept
separate. Their weighted quadratic forms agree because each one-step kernel
satisfies detailed balance. Thus no illicit reordering of projections occurs.
-/

noncomputable section

open scoped BigOperators Matrix

namespace GraphicalAllocation.Projections

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Forward transition matrix, in chronological Markov-kernel order. -/
def forwardProduct (q : ℕ → Matrix A A ℝ) : ℕ → Matrix A A ℝ
  | 0 => 1
  | n + 1 => forwardProduct q n * q n

omit [DecidableEq A] in
/-- Reversible row-stochastic kernels preserve their reference weights. -/
theorem kernel_stationary (μ : A → ℝ) (q : Matrix A A ℝ)
    (hrow : ∀ a, ∑ b, q a b = 1)
    (hbal : ∀ a b, μ a * q a b = μ b * q b a) (b : A) :
    ∑ a, μ a * q a b = μ b := by
  simp_rw [hbal]
  rw [← Finset.mul_sum, hrow, mul_one]

/-- The forward product remains row-stochastic. -/
theorem forwardProduct_row_sum (q : ℕ → Matrix A A ℝ)
    (hrow : ∀ j a, ∑ b, q j a b = 1) (n : ℕ) (a : A) :
    ∑ b, forwardProduct q n a b = 1 := by
  induction n with
  | zero => simp [forwardProduct, Matrix.one_apply]
  | succ n ih =>
      simp only [forwardProduct, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow, mul_one]
      exact ih

/-- The forward product preserves the common reference weights. -/
theorem forwardProduct_stationary (μ : A → ℝ) (q : ℕ → Matrix A A ℝ)
    (hrow : ∀ j a, ∑ b, q j a b = 1)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a) (n : ℕ) (b : A) :
    ∑ a, μ a * forwardProduct q n a b = μ b := by
  induction n generalizing b with
  | zero => simp [forwardProduct, Matrix.one_apply]
  | succ n ih =>
      simp only [forwardProduct, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, ih]
      exact kernel_stationary μ (q n) (hrow n) (hbal n) b

/-- Nonnegative kernels yield a nonnegative forward product. -/
theorem forwardProduct_nonneg (q : ℕ → Matrix A A ℝ)
    (hq : ∀ j a b, 0 ≤ q j a b) (n : ℕ) (a b : A) :
    0 ≤ forwardProduct q n a b := by
  induction n generalizing a b with
  | zero => simp [forwardProduct, Matrix.one_apply]; positivity
  | succ n ih =>
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih a c) (hq n c b)

/-- Detailed balance is precisely weighted self-adjointness. -/
theorem weighted_kernel_adjoint {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : Matrix A A ℝ) (hbal : ∀ a b, μ a * q a b = μ b * q b a)
    (f g : A → ℝ) :
    (∑ a, μ a * f a * (q *ᵥ g) a) =
      ∑ a, μ a * (q *ᵥ f) a * g a := by
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (conjugateMatrix_isHermitian hμ q hbal)) (weightedVector μ f) (weightedVector μ g)
  simp_rw [conjugateMatrix_apply_weighted hμ,
    inner_weightedVector (fun a => (hμ a).le)] at hs
  exact hs.symm

/-- The forward and reverse products are adjoints, including their order. -/
theorem forward_reverse_inner {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : ℕ → Matrix A A ℝ)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a)
    (f g : A → ℝ) (n : ℕ) :
    (∑ a, μ a * f a * (forwardProduct q n *ᵥ g) a) =
      ∑ a, μ a * kernelOrbit q f n a * g a := by
  induction n generalizing g with
  | zero => simp [forwardProduct, kernelOrbit]
  | succ n ih =>
      rw [forwardProduct, ← Matrix.mulVec_mulVec, ih]
      exact weighted_kernel_adjoint hμ (q n) (hbal n) (kernelOrbit q f n) g

/-- The endpoint joint weight of the finite Markov chain. For normalized `μ`
and nonnegative row-stochastic kernels this is its genuine joint probability. -/
def endpointJoint (μ : A → ℝ) (q : ℕ → Matrix A A ℝ) (n : ℕ) (a b : A) : ℝ :=
  μ a * forwardProduct q n a b

/-- Equation (4.2) for finite scalar-valued stationary projection chains.
The forward endpoint distribution is explicitly constructed from the kernels. -/
theorem stationary_chain_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : ℕ → Matrix A A ℝ)
    (hrow : ∀ j a, ∑ b, q j a b = 1)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a)
    (hidem : ∀ j, q j * q j = q j) (f : A → ℝ) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ q n a b * (f b - f a) ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a * (f a - (q j *ᵥ f) a) ^ 2 := by
  have hjrow (a : A) : ∑ b, endpointJoint μ q n a b = μ a := by
    simp only [endpointJoint, ← Finset.mul_sum, forwardProduct_row_sum q hrow, mul_one]
  have hjcol (b : A) : ∑ a, endpointJoint μ q n a b = μ b :=
    forwardProduct_stationary μ q hrow hbal n b
  have he := stationary_coupling_square (𝕜 := ℝ) μ (endpointJoint μ q n) hjrow hjcol f
  simp only [Real.norm_eq_abs, sq_abs, RCLike.inner_apply, conj_trivial,
    RCLike.re_to_real] at he
  have hcross : (∑ a, ∑ b, endpointJoint μ q n a b * (f b * f a)) =
      ∑ a, μ a * f a * kernelOrbit q f n a := by
    calc
      _ = ∑ a, μ a * f a * (forwardProduct q n *ᵥ f) a := by
        simp only [endpointJoint, Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ a, μ a * kernelOrbit q f n a * f a :=
        forward_reverse_inner hμ q hbal f f n
      _ = _ := by apply Finset.sum_congr rfl; intro a _; ring
  rw [hcross] at he
  have hdeficit : (∑ a, μ a * f a * (f a - kernelOrbit q f n a)) =
      (∑ a, μ a * (f a) ^ 2) - (∑ a, μ a * f a * kernelOrbit q f n a) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hp := weighted_product_le hμ q hbal hidem f n
  rw [hdeficit] at hp
  linarith

end GraphicalAllocation.Projections
