import GraphicalAllocation.Transport.FiniteLaw
import Mathlib.Data.Fintype.BigOperators

/-!
# The pointwise response-energy bound

This is the deterministic weighted Cauchy–Schwarz step of (5.10). The separate
finite-law result below supplies its response bound by actual averaging of
clipped derivatives. These theorems do not assert an unproved Palm identity or
continuous-time variance budget.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules
open scoped BigOperators

variable {V A Ω : Type*} [Fintype V] [DecidableEq V] [Fintype A]

omit [DecidableEq V] in
/-- Restricted weighted response pays energy in inverse proportion to ball volume. -/
theorem restricted_response_energy (d : V → V → ℝ)
    (hsym : ∀ i j, d i j = d j i) (R : ℝ) (start : A → V)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hnorm : ∑ a, w a = 1)
    (f : V → A → ℝ) {B L : ℝ} (hB : 0 < B)
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (hresponse : L ≤ ∑ i, ∑ a, if d i (start a) ≤ R then w a * f i a else 0) :
    max L 0 ^ 2 / B ≤ ∑ i, ∑ a, w a * f i a ^ 2 := by
  classical
  let wr : V × A → ℝ := fun z => if d z.1 (start z.2) ≤ R then w z.2 else 0
  have hwr : ∀ z ∈ (Finset.univ : Finset (V × A)), 0 ≤ wr z := by
    intro z hz
    dsimp [wr]
    split_ifs
    · exact hw _
    · exact le_rfl
  have hmass : (∑ z, wr z) ≤ B := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      _ = ∑ a, ((closedBall d R (start a)).card : ℝ) * w a := by
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [wr]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 2
        congr 1
        ext i
        simp [closedBall, hsym i (start a)]
      _ ≤ ∑ a, B * w a := Finset.sum_le_sum
        (fun a ha => mul_le_mul_of_nonneg_right (hvolume (start a)) (hw a))
      _ = B := by rw [← Finset.mul_sum, hnorm, mul_one]
  have hresp : L ≤ ∑ z, wr z * f z.1 z.2 := by
    simpa [Fintype.sum_prod_type, wr, ite_mul] using hresponse
  have he := weighted_energy_of_response Finset.univ wr (fun z => f z.1 z.2)
    hwr hB hmass hresp
  apply he.trans
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro a ha
  dsimp [wr]
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    exact mul_nonneg (hw a) (sq_nonneg _)

/-- The exact algebraic normalization appearing in (5.10). -/
theorem protected_energy_normalization {M B L : ℝ} (hM : 0 < M) :
    max (L / M) 0 ^ 2 / B = max L 0 ^ 2 / (M ^ 2 * B) := by
  by_cases hL : 0 ≤ L
  · rw [max_eq_left hL, max_eq_left (div_nonneg hL hM.le)]
    rw [div_pow, div_div]
  · rw [max_eq_right (le_of_not_ge hL),
      max_eq_right (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hL) hM.le)]
    simp

/-- A finite conditional terminal law gives the response through a literal sum. -/
def terminalResponse (κ : A → Ω → ℝ) [Fintype Ω]
    (x : A → Ω → Profile V) (finish : A → Ω → V) (ψ : Equiv.Perm V)
    (M : ℝ) (i : V) (a : A) : ℝ :=
  ∑ ω, κ a ω * finiteDifference (clippedContrast i (ψ i) M) (x a ω) (finish a ω)

section Conditional
variable [Fintype Ω] [Nonempty V]

/-- Pointwise finite-law transport energy, derived from the actual clipped
observable and a normalized conditional history law. There is no assumed
transport or response inequality in its inputs. To apply this to an allocation
process one must separately identify `terminalResponse` with its derivative. -/
theorem finite_conditional_transport_energy (d : V → V → ℝ)
    (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B p q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hnorm : ∑ a, w a = 1)
    (κ : A → Ω → ℝ) (hκ : ∀ a ω, 0 ≤ κ a ω) (hκnorm : ∀ a, ∑ ω, κ a ω = 1)
    (x : A → Ω → Profile V) (start : A → V) (finish : A → Ω → V)
    (hp : (∑ a, ∑ ω, w a * κ a ω * (if gap (x a ω) ≤ M - 1 then 0 else 1)) ≤ p)
    (hq : (∑ a, ∑ ω, w a * κ a ω * (if R ≤ d (start a) (finish a ω) then 1 else 0)) ≤ q) :
    max (1 - p - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      ∑ i, ∑ a, w a * terminalResponse κ x finish ψ M i a ^ 2 := by
  classical
  let W : A × Ω → ℝ := fun z => w z.1 * κ z.1 z.2
  have hW : ∀ z, 0 ≤ W z := fun z => mul_nonneg (hw z.1) (hκ z.1 z.2)
  have hWnorm : ∑ z, W z = 1 := by
    simp only [W, Fintype.sum_prod_type, ← Finset.mul_sum, hκnorm, mul_one]
    exact hnorm
  have hp' : (∑ z : A × Ω, W z * (if gap (x z.1 z.2) ≤ M - 1 then 0 else 1)) ≤ p := by
    simpa [W, Fintype.sum_prod_type] using hp
  have hq' : (∑ z : A × Ω, W z * (if R ≤ d (start z.1) (finish z.1 z.2) then 1 else 0)) ≤ q := by
    simpa [W, Fintype.sum_prod_type] using hq
  have hr := finite_law_protected_response_envelope W hW hWnorm
    (fun z => x z.1 z.2) (fun z => start z.1) (fun z => finish z.1 z.2)
    d hdiag hsym htriangle ψ hR hM hsep hp' hq'
  have hresponse : (1 - p - 2 * q) / M ≤
      ∑ i, ∑ a, if d i (start a) ≤ R then w a * terminalResponse κ x finish ψ M i a else 0 := by
    apply hr.trans_eq
    simp only [Fintype.sum_prod_type, W, Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro a ha
    unfold terminalResponse
    by_cases hia : d i (start a) ≤ R
    · simp [hia, Finset.mul_sum, mul_assoc]
    · simp [hia]
  have he := restricted_response_energy d hsym R start w hw hnorm
    (terminalResponse κ x finish ψ M) hB hvolume hresponse
  rwa [protected_energy_normalization (by linarith : 0 < M)] at he

end Conditional
end GraphicalAllocation.Transport
