import GraphicalAllocation.Process.PositiveJensen

/-! # Jensen for a positive unital expectation functional -/

namespace GraphicalAllocation.Transport
open GraphicalAllocation.Process
open scoped BoundedContinuousFunction

variable {S : Type*} [TopologicalSpace S] [DiscreteTopology S]

omit [DiscreteTopology S] in
/-- Positivity makes the actual expectation functional monotone. -/
theorem positive_functional_mono (L : (S →ᵇ ℝ) →L[ℝ] ℝ)
    (hpos : ∀ f : S →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    {f g : S →ᵇ ℝ} (hfg : ∀ x, f x ≤ g x) : L f ≤ L g := by
  have h := hpos (g - f) (fun x => sub_nonneg.mpr (hfg x))
  simpa using h

omit [DiscreteTopology S] in
/-- Centered-square Jensen uses only positivity and constant preservation. -/
theorem positive_functional_sq (L : (S →ᵇ ℝ) →L[ℝ] ℝ)
    (hpos : ∀ f : S →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hconst : ∀ c, L (BoundedContinuousFunction.const S c) = c) (f : S →ᵇ ℝ) :
    (L f) ^ 2 ≤ L (f ^ 2) := by
  let c := L f
  have h := hpos ((f - BoundedContinuousFunction.const S c) ^ 2) (fun x => sq_nonneg _)
  have he : (f - BoundedContinuousFunction.const S c) ^ 2 =
      f ^ 2 - (2 * c) • f + BoundedContinuousFunction.const S (c ^ 2) := by
    ext x
    simp
    ring
  rw [he, map_add, map_sub, map_smul, hconst] at h
  change 0 ≤ L (f ^ 2) - 2 * c * c + c ^ 2 at h
  change c ^ 2 ≤ L (f ^ 2)
  nlinarith

/-- Positive-part Jensen for a composed process expectation. -/
theorem positive_functional_pospart_sq (L : (S →ᵇ ℝ) →L[ℝ] ℝ)
    (hpos : ∀ f : S →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hconst : ∀ c, L (BoundedContinuousFunction.const S c) = c) (f : S →ᵇ ℝ) :
    max (L f) 0 ^ 2 ≤ L (positiveTest f ^ 2) := by
  have hs := positive_functional_sq L hpos hconst (positiveTest f)
  have hn : 0 ≤ L (positiveTest f) := hpos _ (fun x => le_max_right _ _)
  have hm : L f ≤ L (positiveTest f) := positive_functional_mono L hpos (fun x => le_max_left _ _)
  have hmax : max (L f) 0 ≤ L (positiveTest f) := max_le hm hn
  nlinarith [le_max_right (L f) 0]

/-- Energy lower bounds survive the full composed process expectation. -/
theorem positive_functional_energy_lower (L : (S →ᵇ ℝ) →L[ℝ] ℝ)
    (hpos : ∀ f : S →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L f)
    (hconst : ∀ c, L (BoundedContinuousFunction.const S c) = c)
    (f e : S →ᵇ ℝ) {B : ℝ} (hB : 0 < B)
    (hpoint : ∀ x, max (f x) 0 ^ 2 / B ≤ e x) :
    max (L f) 0 ^ 2 / B ≤ L e := by
  have hm := positive_functional_mono L hpos
    (f := B⁻¹ • (positiveTest f ^ 2)) (g := e) (by
      intro x
      change B⁻¹ * max (f x) 0 ^ 2 ≤ e x
      simpa [div_eq_mul_inv, mul_comm] using hpoint x)
  rw [map_smul] at hm
  have hs := div_le_div_of_nonneg_right (positive_functional_pospart_sq L hpos hconst f) hB.le
  exact hs.trans (by simpa [div_eq_mul_inv, mul_comm] using hm)

end GraphicalAllocation.Transport
