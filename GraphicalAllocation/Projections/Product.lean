import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Products of orthogonal projections

A strengthened form of equation (4.1), with canonical Mathlib orthogonal
projections and no commutativity assumption. The auxiliary nonnegative square
proof replaces the informal Cauchy–Schwarz/division argument.
-/

noncomputable section

open scoped BigOperators
open RCLike

namespace GraphicalAllocation
namespace Projections

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A scaled version of the elementary Hilbert-space Young inequality. -/
theorem four_re_inner_le (r d : E) :
    4 * re ⟪r, d⟫ ≤ 4 * ‖r‖ ^ 2 + ‖d‖ ^ 2 := by
  have h : 0 ≤ re ⟪r + r - d, r + r - d⟫ := inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    map_sub, map_add, inner_self_eq_norm_sq, inner_re_symm (𝕜 := 𝕜) d r] at h
  linarith

/-- The potential which telescopes along an ordered product of projections. -/
def potential (f v : E) : ℝ := 2 * re ⟪f, f - v⟫ + ‖f - v‖ ^ 2

/-- One projection changes the potential by at most four times the squared
residual of the original vector. -/
theorem potential_starProjection_le (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (f v : E) :
    potential (𝕜 := 𝕜) f (K.starProjection v) ≤
      potential (𝕜 := 𝕜) f v + 4 * ‖f - K.starProjection f‖ ^ 2 := by
  let d := v - K.starProjection v
  have horth (w : E) : ⟪K.starProjection w, d⟫ = 0 := by
    apply inner_eq_zero_symm.mp
    exact K.starProjection_inner_eq_zero v _ (K.starProjection_apply_mem w)
  have hv : re ⟪v, d⟫ = ‖d‖ ^ 2 := by
    have h := inner_self_eq_norm_sq (𝕜 := 𝕜) d
    dsimp [d] at h ⊢
    rw [inner_sub_left, horth v, sub_zero] at h
    exact h
  have hf : re ⟪f - K.starProjection f, d⟫ = re ⟪f, d⟫ := by
    rw [inner_sub_left, horth f, sub_zero]
  have hy := four_re_inner_le (𝕜 := 𝕜) (f - K.starProjection f) d
  rw [hf] at hy
  have heq : f - K.starProjection v = f - v + d := by
    dsimp [d]
    abel
  unfold potential
  rw [heq, inner_add_right, map_add, norm_add_sq (𝕜 := 𝕜), inner_sub_left, map_sub]
  linarith

/-- `orbit K f n` is `Q_(n-1) ... Q_0 f`, in that order. -/
def orbit (K : ℕ → Submodule 𝕜 E) [∀ j, (K j).HasOrthogonalProjection]
    (f : E) : ℕ → E
  | 0 => f
  | n + 1 => (K n).starProjection (orbit K f n)

@[simp] theorem orbit_zero (K : ℕ → Submodule 𝕜 E)
    [∀ j, (K j).HasOrthogonalProjection] (f : E) : orbit K f 0 = f := rfl

@[simp] theorem orbit_succ (K : ℕ → Submodule 𝕜 E)
    [∀ j, (K j).HasOrthogonalProjection] (f : E) (n : ℕ) :
    orbit K f (n + 1) = (K n).starProjection (orbit K f n) := rfl

/-- A strengthening of the product-of-projections inequality. -/
theorem product_potential_le (K : ℕ → Submodule 𝕜 E)
    [∀ j, (K j).HasOrthogonalProjection] (f : E) (n : ℕ) :
    2 * re ⟪f, f - orbit K f n⟫ + ‖f - orbit K f n‖ ^ 2 ≤
      4 * ∑ j ∈ Finset.range n, ‖f - (K j).starProjection f‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := potential_starProjection_le (K n) f (orbit K f n)
      unfold potential at hs
      rw [orbit_succ, Finset.sum_range_succ]
      linarith

/-- Equation (4.1), valid over both real and complex inner-product spaces. -/
theorem product_re_inner_le (K : ℕ → Submodule 𝕜 E)
    [∀ j, (K j).HasOrthogonalProjection] (f : E) (n : ℕ) :
    re ⟪f, f - orbit K f n⟫ ≤
      2 * ∑ j ∈ Finset.range n, ‖f - (K j).starProjection f‖ ^ 2 := by
  have h := product_potential_le K f n
  have hn := sq_nonneg ‖f - orbit K f n‖
  linarith

/-- The ordered orbit of a sequence of linear operators. -/
def linearOrbit (Q : ℕ → E →ₗ[𝕜] E) (f : E) : ℕ → E
  | 0 => f
  | n + 1 => Q n (linearOrbit Q f n)

/-- The one-step estimate in the canonical self-adjoint/idempotent API. -/
theorem potential_linearProjection_le (Q : E →ₗ[𝕜] E)
    (hQ : Q.IsSymmetricProjection) (f v : E) :
    potential (𝕜 := 𝕜) f (Q v) ≤
      potential (𝕜 := 𝕜) f v + 4 * ‖f - Q f‖ ^ 2 := by
  obtain ⟨K, hK, heq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection.mp hQ
  let := hK
  rw [heq]
  exact potential_starProjection_le K f v

/-- Equation (4.1) for any sequence of symmetric idempotent linear maps.
The hypothesis is Mathlib's canonical orthogonal-projection predicate. -/
theorem linear_product_re_inner_le (Q : ℕ → E →ₗ[𝕜] E)
    (hQ : ∀ j, (Q j).IsSymmetricProjection) (f : E) (n : ℕ) :
    re ⟪f, f - linearOrbit Q f n⟫ ≤
      2 * ∑ j ∈ Finset.range n, ‖f - Q j f‖ ^ 2 := by
  have hpotential : ∀ k,
      potential (𝕜 := 𝕜) f (linearOrbit Q f k) ≤
      4 * ∑ j ∈ Finset.range k, ‖f - Q j f‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp [linearOrbit, potential]
    | succ k ih =>
        have hs := potential_linearProjection_le (Q k) (hQ k) f (linearOrbit Q f k)
        simp only [linearOrbit, Finset.sum_range_succ]
        linarith
  have hn := sq_nonneg ‖f - linearOrbit Q f n‖
  have hp := hpotential n
  unfold potential at hp
  linarith

end Projections
end GraphicalAllocation
