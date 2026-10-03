import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hilbert geometry for displacement bounds

These are unconditional algebraic steps of the stationary-kernel expansion and
of the endpoint-to-midpoint comparison in Section 7. They do not assume a
Markov-chain representation or the conclusion of a displacement theorem.
-/

noncomputable section

open scoped BigOperators
open RCLike

namespace GraphicalAllocation
namespace Projections

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The stationary displacement expansion for a finite joint law. `w` can be
an arbitrary real matrix; only its two equal marginals are used. In particular,
this applies to every finite stationary coupling, scalar- or Hilbert-valued. -/
theorem stationary_coupling_square {ι : Type*} [Fintype ι]
    (ρ : ι → ℝ) (w : ι → ι → ℝ)
    (hrow : ∀ x, ∑ y, w x y = ρ x)
    (hcol : ∀ y, ∑ x, w x y = ρ y) (f : ι → E) :
    (∑ x, ∑ y, w x y * ‖f y - f x‖ ^ 2) =
      2 * (∑ x, ρ x * ‖f x‖ ^ 2) -
      2 * (∑ x, ∑ y, w x y * re ⟪f x, f y⟫) := by
  have hleft : (∑ x, ∑ y, w x y * ‖f x‖ ^ 2) =
      ∑ x, ρ x * ‖f x‖ ^ 2 := by
    simp_rw [← Finset.sum_mul, hrow]
  have hright : (∑ x, ∑ y, w x y * ‖f y‖ ^ 2) =
      ∑ x, ρ x * ‖f x‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol]
  have hcross : (∑ x, ∑ y, w x y * (2 * re ⟪f y, f x⟫)) =
      2 * (∑ x, ∑ y, w x y * re ⟪f x, f y⟫) := by
    calc
      _ = ∑ x, ∑ y, 2 * (w x y * re ⟪f x, f y⟫) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [inner_re_symm (𝕜 := 𝕜) (f y) (f x)]
        ring
      _ = _ := by simp_rw [Finset.mul_sum]
  simp_rw [norm_sub_sq (𝕜 := 𝕜), mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hleft, hright, hcross]
  ring

/-- A deterministic endpoint correction: two endpoint errors of at most
`η / 2` together cost at most `2 * η²` in the squared displacement. -/
theorem endpoint_midpoint_square_le (a b c d : E) (η : ℝ)
    (ha : ‖a - c‖ ≤ η / 2) (hb : ‖b - d‖ ≤ η / 2) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖c - d‖ ^ 2 + 2 * η ^ 2 := by
  have hη : 0 ≤ η := by linarith [norm_nonneg (a - c)]
  have hdist : ‖a - b‖ ≤ ‖c - d‖ + η := by
    calc
      ‖a - b‖ = ‖(a - c) + (c - d) + (d - b)‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + ‖c - d‖ + ‖d - b‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖c - d‖ + η := by rw [norm_sub_rev d b]; linarith
  have hsq := sq_le_sq₀ (norm_nonneg (a - b))
    (add_nonneg (norm_nonneg (c - d)) hη) |>.2 hdist
  nlinarith [sq_nonneg (‖c - d‖ - η)]

end Projections
end GraphicalAllocation
