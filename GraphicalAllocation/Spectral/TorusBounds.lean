import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Folded frequency sum for the square torus

The finite sum is bounded by unfolding each coordinate into its two possible
orientations.  The resulting quadrant square grows by two boundary segments;
their reciprocal-square sum is bounded by a harmonic increment.  Thus the
estimate applies to the actual finite frequency set without spectral hypotheses.
-/

noncomputable section
open scoped BigOperators Fin.CommRing

namespace GraphicalAllocation.Spectral

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- Distance of a cyclic frequency to the zero frequency. -/
def foldedFrequency (L : ℕ) (a : Fin L) : ℕ := min a.val (L - a.val)

/-- Unfolding a cyclic coordinate costs at most its two orientations. -/
theorem sum_foldedFrequency_le (L : ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ a : Fin L, f (foldedFrequency L a) ≤
      2 * ∑ k ∈ Finset.range (L + 1), f k := by
  have h₁ : (∑ a : Fin L, f a.val) ≤ ∑ k ∈ Finset.range (L + 1), f k := by
    apply Finset.sum_le_sum_of_injOn Fin.val
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro k hk
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro a _
      exact le_rfl
    · intro k _ _
      exact hf k
  have h₂ : (∑ a : Fin L, f (L - a.val)) ≤
      ∑ k ∈ Finset.range (L + 1), f k := by
    apply Finset.sum_le_sum_of_injOn (fun a : Fin L => L - a.val)
    · intro a _ b _ hab
      apply Fin.ext
      dsimp only at hab
      have := a.isLt
      have := b.isLt
      omega
    · intro k hk
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro a _
      exact le_rfl
    · intro k _ _
      exact hf k
  calc
    _ ≤ ∑ a : Fin L, (f a.val + f (L - a.val)) := by
      apply Finset.sum_le_sum
      intro a _
      rcases le_total a.val (L - a.val) with ha | ha
      · simp only [foldedFrequency, min_eq_left ha]
        exact le_add_of_nonneg_right (hf _)
      · simp only [foldedFrequency, min_eq_right ha]
        exact le_add_of_nonneg_left (hf _)
    _ = (∑ a : Fin L, f a.val) + ∑ a : Fin L, f (L - a.val) :=
      Finset.sum_add_distrib
    _ ≤ 2 * ∑ k ∈ Finset.range (L + 1), f k := by linarith

/-- The quadrant sum grows at most as four times the harmonic numbers. -/
theorem quadrant_inverse_square_sum_le (L : ℕ) :
    ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1),
      ((i : ℝ)^2 + (j : ℝ)^2)⁻¹ ≤ 4 * (harmonic L : ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hk : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
    have hkpos : (0 : ℝ) < (L + 1 : ℕ) := lt_of_lt_of_le zero_lt_one hk
    have hkne : (L + 1 : ℝ) ≠ 0 := by positivity
    have hterm (i : ℕ) :
        ((i : ℝ)^2 + ((L + 1 : ℕ) : ℝ)^2)⁻¹ ≤ (((L + 1 : ℕ) : ℝ)^2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hkpos)
        (show (((L + 1 : ℕ) : ℝ)^2) ≤ (i : ℝ)^2 + ((L + 1 : ℕ) : ℝ)^2 by
          nlinarith [sq_nonneg (i : ℝ)])
    have hcol : (∑ i ∈ Finset.range (L + 1),
        ((i : ℝ)^2 + ((L + 1 : ℕ) : ℝ)^2)⁻¹) ≤
        ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ)^2)⁻¹ := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (L + 1), (((L + 1 : ℕ) : ℝ)^2)⁻¹ :=
          Finset.sum_le_sum (fun i _ => hterm i)
        _ = _ := by simp
    have hrow : (∑ j ∈ Finset.range (L + 1),
        (((L + 1 : ℕ) : ℝ)^2 + (j : ℝ)^2)⁻¹) ≤
        ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ)^2)⁻¹ := by
      simpa only [add_comm] using hcol
    have hb : 2 * ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ)^2)⁻¹ +
        (((L + 1 : ℕ) : ℝ)^2)⁻¹ ≤ 4 * (((L + 1 : ℕ) : ℝ))⁻¹ := by
      calc
        _ = (2 * ((L + 1 : ℕ) : ℝ) + 1) * (((L + 1 : ℕ) : ℝ)^2)⁻¹ := by ring
        _ ≤ (4 * ((L + 1 : ℕ) : ℝ)) * (((L + 1 : ℕ) : ℝ)^2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by push_cast; field_simp
    have hsplit :
        (∑ i ∈ Finset.range (L + 1 + 1), ∑ j ∈ Finset.range (L + 1 + 1),
          ((i : ℝ)^2 + (j : ℝ)^2)⁻¹) =
        (∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1),
          ((i : ℝ)^2 + (j : ℝ)^2)⁻¹) +
        (∑ i ∈ Finset.range (L + 1),
          ((i : ℝ)^2 + ((L + 1 : ℕ) : ℝ)^2)⁻¹) +
        (∑ j ∈ Finset.range (L + 1),
          (((L + 1 : ℕ) : ℝ)^2 + (j : ℝ)^2)⁻¹) +
        (((L + 1 : ℕ) : ℝ)^2 + ((L + 1 : ℕ) : ℝ)^2)⁻¹ := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      ring
    rw [hsplit, harmonic_succ]
    push_cast
    push_cast at hcol hrow hb
    have hc := hterm (L + 1)
    push_cast at hc
    linarith

/-- The folded finite torus frequency sum has the logarithmic bound. -/
theorem torus_folded_frequency_sum_le (n : ℕ) :
    ∑ a ∈ Finset.univ.erase (0 : Fin (n + 3) × Fin (n + 3)),
      1 / (16 * ((foldedFrequency (n + 3) a.1 : ℝ)^2 +
        (foldedFrequency (n + 3) a.2 : ℝ)^2)) ≤
      1 + Real.log (n + 3) := by
  let L := n + 3
  let f : ℕ → ℕ → ℝ := fun i j => ((i : ℝ)^2 + (j : ℝ)^2)⁻¹
  have hf (i j : ℕ) : 0 ≤ f i j := by dsimp [f]; positivity
  have hfold : (∑ a : Fin L, ∑ b : Fin L,
      f (foldedFrequency L a) (foldedFrequency L b)) ≤
      4 * ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1), f i j := by
    calc
      _ ≤ ∑ a : Fin L, 2 * ∑ j ∈ Finset.range (L + 1), f (foldedFrequency L a) j := by
        apply Finset.sum_le_sum
        intro a _
        exact sum_foldedFrequency_le L (f (foldedFrequency L a)) (hf _)
      _ = 2 * ∑ j ∈ Finset.range (L + 1), ∑ a : Fin L, f (foldedFrequency L a) j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * ∑ j ∈ Finset.range (L + 1), 2 * ∑ i ∈ Finset.range (L + 1), f i j := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro j _
        exact sum_foldedFrequency_le L (fun i => f i j) (fun i => hf i j)
      _ = 4 * ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1), f i j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        ring
  have hquadrant := quadrant_inverse_square_sum_le L
  change (∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1), f i j) ≤
    4 * (harmonic L : ℝ) at hquadrant
  have hresult : (∑ a ∈ Finset.univ.erase (0 : Fin L × Fin L),
      1 / (16 * ((foldedFrequency L a.1 : ℝ)^2 + (foldedFrequency L a.2 : ℝ)^2))) ≤
      1 + Real.log (L : ℝ) := by
    calc
      _ ≤ ∑ a : Fin L × Fin L,
          1 / (16 * ((foldedFrequency L a.1 : ℝ)^2 + (foldedFrequency L a.2 : ℝ)^2)) := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro a
        positivity
      _ = (1 / 16 : ℝ) * ∑ a : Fin L, ∑ b : Fin L,
          f (foldedFrequency L a) (foldedFrequency L b) := by
        simp only [one_div, mul_inv, Fintype.sum_prod_type, ← Finset.mul_sum, f]
      _ ≤ (1 / 16 : ℝ) * (4 * (4 * (harmonic L : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hfold.trans (mul_le_mul_of_nonneg_left hquadrant (by norm_num))
      _ = (harmonic L : ℝ) := by ring
      _ ≤ 1 + Real.log (L : ℝ) := harmonic_le_one_add_log L
  simpa only [L, Nat.cast_add, Nat.cast_ofNat] using hresult

end GraphicalAllocation.Spectral
