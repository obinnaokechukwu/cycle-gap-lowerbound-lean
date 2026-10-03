import GraphicalAllocation.Transport.Counting
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-law transport

The distribution here is an arbitrary finite probability law over histories.
The start/end vertices and terminal configuration are actual functions on those
histories. The pointwise estimate is averaged directly, with no Palm identity
assumed. A separate connection to allocation transition kernels is still needed
to use these theorems for that stochastic model.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules
open scoped BigOperators

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Ω]

/-- Complementary event weights add to the total mass, including zero atoms. -/
theorem event_mass_complement (w : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    (∑ ω, w ω * (if P ω then 1 else 0)) +
      (∑ ω, w ω * (if P ω then 0 else 1)) = ∑ ω, w ω := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  split_ifs <;> ring

/-- Averaged protected response under a finite probability law, using the actual
bad-gap and displacement masses and no independence between any events. -/
theorem finite_law_protected_response (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (x : Ω → Profile V) (start finish : Ω → V)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0)
    (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) :
    (1 - (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 0 else 1)) -
      2 * (∑ ω, w ω * (if R ≤ d (start ω) (finish ω) then 1 else 0))) / M ≤
      ∑ ω, w ω * ∑ i, if d i (start ω) ≤ R then
        finiteDifference (clippedContrast i (ψ i) M) (x ω) (finish ω) else 0 := by
  have hpoint := Finset.sum_le_sum (s := Finset.univ) (fun ω hω =>
    mul_le_mul_of_nonneg_left
      (pathwise_protected_response d hdiag hsym htriangle ψ hR hM hsep
        (x ω) (start ω) (finish ω)) (hw ω))
  have hcomp := event_mass_complement w (fun ω => gap (x ω) ≤ M - 1)
  rw [hnorm] at hcomp
  have hgood : (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 1 / M else 0)) =
      (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 1 else 0)) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs <;> ring
  have htail : (∑ ω, w ω * (if R ≤ d (start ω) (finish ω) then 1 / M else 0)) =
      (∑ ω, w ω * (if R ≤ d (start ω) (finish ω) then 1 else 0)) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs <;> ring
  simp_rw [mul_sub, mul_left_comm (w _) 2] at hpoint
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hgood, htail] at hpoint
  calc
    _ = (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 1 else 0)) / M -
        2 * (∑ ω, w ω * (if R ≤ d (start ω) (finish ω) then 1 else 0)) / M := by
      rw [show 1 - (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 0 else 1)) =
        (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 1 else 0)) by linarith]
      ring
    _ ≤ _ := by simpa [mul_div_assoc] using hpoint

/-- Tail and gap envelopes may be substituted after computing their joint law. -/
theorem finite_law_protected_response_envelope (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hnorm : ∑ ω, w ω = 1) (x : Ω → Profile V) (start finish : Ω → V)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0)
    (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M p q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hp : (∑ ω, w ω * (if gap (x ω) ≤ M - 1 then 0 else 1)) ≤ p)
    (hq : (∑ ω, w ω * (if R ≤ d (start ω) (finish ω) then 1 else 0)) ≤ q) :
    (1 - p - 2 * q) / M ≤
      ∑ ω, w ω * ∑ i, if d i (start ω) ≤ R then
        finiteDifference (clippedContrast i (ψ i) M) (x ω) (finish ω) else 0 := by
  apply le_trans _ (finite_law_protected_response w hw hnorm x start finish d hdiag
    hsym htriangle ψ hR hM hsep)
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

end GraphicalAllocation.Transport
