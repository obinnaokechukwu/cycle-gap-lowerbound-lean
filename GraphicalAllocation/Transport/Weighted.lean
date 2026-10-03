import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Weighted Cauchy–Schwarz and protected-region volume

All weights may vanish. The theorem is for arbitrary finite measures, so it can
be used for finite histories and mark atoms before subsequent limiting or
Poisson arguments. No response lower bound or stochastic law is installed as a
structure field.
-/

noncomputable section

namespace GraphicalAllocation.Transport
open scoped BigOperators

variable {A : Type*}

/-- Weighted Cauchy–Schwarz, with no divisions and no positive-weight restriction. -/
theorem weighted_cauchy_schwarz (s : Finset A) (w f : A → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ s, w a * f a) ^ 2 ≤ (∑ a ∈ s, w a) * ∑ a ∈ s, w a * f a ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
    (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))
  intro a ha
  ring_nf
  exact le_rfl

/-- Positive part is essential when the raw response lower bound is negative. -/
theorem weighted_energy_of_response (s : Finset A) (w f : A → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {B L : ℝ} (hB : 0 < B)
    (hmass : ∑ a ∈ s, w a ≤ B) (hresponse : L ≤ ∑ a ∈ s, w a * f a) :
    max L 0 ^ 2 / B ≤ ∑ a ∈ s, w a * f a ^ 2 := by
  have henergy : 0 ≤ ∑ a ∈ s, w a * f a ^ 2 :=
    Finset.sum_nonneg (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))
  by_cases hL : 0 ≤ L
  · rw [max_eq_left hL, div_le_iff₀ hB]
    have hsquare : L ^ 2 ≤ (∑ a ∈ s, w a * f a) ^ 2 := by
      nlinarith [hresponse, hL]
    exact hsquare.trans ((weighted_cauchy_schwarz s w f hw).trans
      (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hmass henergy))
  · simp only [max_eq_right (le_of_not_ge hL), zero_pow (by decide : 2 ≠ 0), zero_div]
    exact henergy

section Balls
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Closed finite ball for an arbitrary real-valued pseudometric distance. -/
def closedBall (d : V → V → ℝ) (R : ℝ) (i : V) : Finset V :=
  Finset.univ.filter (fun v => d i v ≤ R)

omit [DecidableEq V] in
@[simp] theorem mem_closedBall (d : V → V → ℝ) (R : ℝ) (i v : V) :
    v ∈ closedBall d R i ↔ d i v ≤ R := by simp [closedBall]

/-- Symmetry identifies the transpose count with the same closed ball. -/
theorem transpose_ball_count (d : V → V → ℝ) (hsym : ∀ i j, d i j = d j i)
    (R : ℝ) (v : V) :
    (Finset.univ.filter (fun i => v ∈ closedBall d R i)).card =
      (closedBall d R v).card := by
  congr 1
  ext i
  simp [closedBall, hsym i v]

omit [DecidableEq V] in
/-- The exact double-counting identity behind the restricted-mass estimate. -/
theorem restricted_mass_eq (d : V → V → ℝ) (hsym : ∀ i j, d i j = d j i)
    (R : ℝ) (w : V → ℝ) :
    (∑ i, ∑ v ∈ closedBall d R i, w v) =
      ∑ v, ((closedBall d R v).card : ℝ) * w v := by
  classical
  simp only [closedBall, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 2
  congr 1
  ext i
  simp [hsym i v]

omit [DecidableEq V] in
/-- No independence of the rate weights and configurations is used. -/
theorem restricted_mass_le (d : V → V → ℝ) (hsym : ∀ i j, d i j = d j i)
    (R : ℝ) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {B : ℝ}
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B) :
    (∑ i, ∑ v ∈ closedBall d R i, w v) ≤ B * ∑ v, w v := by
  rw [restricted_mass_eq d hsym R w, Finset.mul_sum]
  exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (hvolume v) (hw v))

section Nonempty
variable [Nonempty V]

/-- The paper's actual finite ball-volume function. -/
def ballVolume (d : V → V → ℝ) (R : ℝ) : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty (fun v => (closedBall d R v).card)

omit [DecidableEq V] in
theorem card_closedBall_le_volume (d : V → V → ℝ) (R : ℝ) (v : V) :
    (closedBall d R v).card ≤ ballVolume d R :=
  Finset.le_sup' (fun u => (closedBall d R u).card) (Finset.mem_univ v)

omit [DecidableEq V] in
theorem ballVolume_pos (d : V → V → ℝ) (hdiag : ∀ v, d v v = 0)
    {R : ℝ} (hR : 0 ≤ R) : 0 < ballVolume d R := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hv : v ∈ closedBall d R v := by simpa [hdiag] using hR
  have hp : 0 < (closedBall d R v).card := Finset.card_pos.mpr ⟨v, hv⟩
  exact hp.trans_le (card_closedBall_le_volume d R v)

end Nonempty

end Balls
end GraphicalAllocation.Transport
