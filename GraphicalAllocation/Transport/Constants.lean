import GraphicalAllocation.Transport.Energy
import Mathlib.Tactic.FieldSimp

/-!
# Numerical specializations of transport energy

The constants here are algebraic consequences of the response envelope and
volume cap, not assumptions about any allocation process.
-/

namespace GraphicalAllocation.Transport

/-- The convenient `1/4` lower bound used after assuming both tails are at most `1/8`. -/
theorem quarter_le_response_sq {p q : ℝ} (hp : p ≤ 1 / 8) (hq : q ≤ 1 / 8) :
    (1 / 4 : ℝ) ≤ max (1 - p - 2 * q) 0 ^ 2 := by
  have h : (1 / 2 : ℝ) ≤ max (1 - p - 2 * q) 0 := by
    have := le_max_left (1 - p - 2 * q) 0
    linarith
  nlinarith

/-- The volume cap (6.6) absorbs the exact mean-increment correction. -/
theorem discrete_correction_absorbed {m N B Δ : ℝ}
    (hm : 0 < m) (hN : 0 < N) (hB : 0 < B) (hΔ : 0 < Δ)
    (hcap : B ≤ m ^ 2 / (32 * N * Δ ^ 2)) :
    4 * Δ ^ 2 / m ^ 2 ≤ 1 / (8 * N * B) := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hΔ2 : 0 < Δ ^ 2 := sq_pos_of_pos hΔ
  have hden : 0 < 32 * N * Δ ^ 2 := mul_pos (mul_pos (by norm_num) hN) hΔ2
  have hden' : 0 < 8 * N * B := mul_pos (mul_pos (by norm_num) hN) hB
  have hc := (le_div_iff₀ hden).mp hcap
  apply (div_le_div_iff₀ hm2 hden').mpr
  nlinarith

/-- Exact algebraic lower bound for each absorbed summand of (6.5). -/
theorem discrete_summand_lower {m N B Δ p q : ℝ}
    (hm : 0 < m) (hN : 0 < N) (hB : 0 < B) (hΔ : 0 < Δ)
    (hp : p ≤ 1 / 8) (hq : q ≤ 1 / 8)
    (hcap : B ≤ m ^ 2 / (32 * N * Δ ^ 2)) :
    1 / (8 * N * B) ≤
      max (max (1 - p - 2 * q) 0 ^ 2 / (N * B) - 4 * Δ ^ 2 / m ^ 2) 0 := by
  have hfirst := div_le_div_of_nonneg_right (quarter_le_response_sq hp hq)
    (le_of_lt (mul_pos hN hB))
  have hsub := discrete_correction_absorbed hm hN hB hΔ hcap
  apply le_trans _ (le_max_left _ _)
  have hid : (1 / 4 : ℝ) / (N * B) = 2 * (1 / (8 * N * B)) := by ring
  rw [hid] at hfirst
  linarith

end GraphicalAllocation.Transport
