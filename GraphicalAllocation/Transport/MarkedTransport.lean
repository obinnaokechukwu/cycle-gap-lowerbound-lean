import GraphicalAllocation.Transport.Energy
import GraphicalAllocation.Process.MarkedExperiment
import GraphicalAllocation.Process.DiscreteVariance

/-!
# Transport for genuine finite marked experiments

The response bound is obtained by applying the tagged transition operator to
the proved pathwise inequality. The resulting response is identified with the
base kernel's actual directional derivative. No Palm identity is assumed.
-/

noncomputable section
namespace GraphicalAllocation.Process.FiniteKernel
open scoped BigOperators
variable {S C I : Type*} [Fintype C]

/-- Finite-horizon expectation preserves finite sums. -/
theorem iterate_finset_sum (K : FiniteKernel S C) (h : ℕ) (s : Finset I) (f : I → S → ℝ) :
    K.iterate h (∑ i ∈ s, f i) = ∑ i ∈ s, K.iterate h (f i) := by
  induction h with
  | zero => rfl
  | succ h ih => rw [iterate_succ, ih, K.step_finset_sum]; rfl

/-- Finite-horizon expectation is homogeneous. -/
theorem iterate_const_mul (K : FiniteKernel S C) (h : ℕ) (c : ℝ) (f : S → ℝ) :
    K.iterate h (fun x => c * f x) = fun x => c * K.iterate h f x := by
  induction h with
  | zero => rfl
  | succ h ih =>
    funext x
    simp only [iterate_succ, ih, step, ← Finset.mul_sum, mul_left_comm]

end GraphicalAllocation.Process.FiniteKernel

namespace GraphicalAllocation.Process.FiniteMarks
open Rules
open scoped BigOperators
variable {V A : Type*} [DecidableEq V] [Fintype A]
variable (F : FiniteMarks V A)

/-- The unperturbed base path does not depend on the tag. -/
theorem tagged_iterate_base (h : ℕ) (f : Profile V → ℝ) (x : Profile V) (v : V) :
    F.tagged.iterate h (fun y => f y.1) (x, v) = F.base.iterate h f x := by
  induction h generalizing x v with
  | zero => rfl
  | succ h ih =>
    simp only [FiniteKernel.iterate_succ, FiniteKernel.step, tagged_weight, tagged_next,
      base_weight, base_next, ih]

end GraphicalAllocation.Process.FiniteMarks

namespace GraphicalAllocation.Transport
open Rules Process
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A]

/-- Probability of a large tag displacement in the actual finite-mark kernel,
averaged over its specified initial tag law. -/
def markedTail (F : FiniteMarks V A) (h : ℕ) (x : Profile V)
    (w : V → ℝ) (d : V → V → ℝ) (R : ℝ) : ℝ :=
  ∑ v, w v * F.tagged.iterate h (fun y => if R ≤ d v y.2 then 1 else 0) (x, v)

/-- Bad-gap probability after exactly h events of the actual finite-mark kernel. -/
def markedBadGap (F : FiniteMarks V A) (h : ℕ) (x : Profile V) (M : ℝ) : ℝ :=
  F.base.iterate h (fun y => if gap y ≤ M - 1 then 0 else 1) x

/-- Tagged expectation of the protected derivative sum, with the source held
fixed, is the restricted sum of genuine base-semigroup derivatives. -/
theorem marked_protected_response_at (F : FiniteMarks V A)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (h : ℕ) (x : Profile V) (v : V) :
    (1 - markedBadGap F h x M -
      2 * F.tagged.iterate h (fun y => if R ≤ d v y.2 then 1 else 0) (x, v)) / M ≤
    ∑ i, if d i v ≤ R then
      finiteDifference (F.base.iterate h (clippedContrast i (ψ i) M)) x v else 0 := by
  have hp := F.tagged.iterate_mono h
    (fun y => pathwise_protected_response d hdiag hsym htriangle ψ hR hM hsep y.1 v y.2)
    (x, v)
  have hfun : (fun y : Profile V × V =>
      (if gap y.1 ≤ M - 1 then 1 / M else 0) -
        2 * (if R ≤ d v y.2 then 1 / M else 0)) =
      (fun y => (1 / M) * (1 - (if gap y.1 ≤ M - 1 then 0 else 1))) -
      (fun y => (2 / M) * (if R ≤ d v y.2 then 1 else 0)) := by
    funext y
    simp only [Pi.sub_apply]
    split_ifs <;> ring
  rw [hfun, F.tagged.iterate_sub, F.tagged.iterate_const_mul,
    F.tagged.iterate_const_mul] at hp
  have hgood : F.tagged.iterate h
      (fun y : Profile V × V => 1 - (if gap y.1 ≤ M - 1 then 0 else 1)) (x, v) =
      1 - markedBadGap F h x M := by
    rw [F.tagged_iterate_base h (fun y => 1 - (if gap y ≤ M - 1 then 0 else 1))]
    change F.base.iterate h ((fun _ => 1) -
      (fun y => if gap y ≤ M - 1 then 0 else 1)) x = _
    simp [FiniteKernel.iterate_sub, markedBadGap]
  simp only [Pi.sub_apply] at hp
  rw [hgood] at hp
  have hsum : F.tagged.iterate h
      (fun y : Profile V × V => ∑ i, if d i v ≤ R then
        finiteDifference (clippedContrast i (ψ i) M) y.1 y.2 else 0) (x, v) =
      ∑ i, if d i v ≤ R then
        finiteDifference (F.base.iterate h (clippedContrast i (ψ i) M)) x v else 0 := by
    have heq : (fun y : Profile V × V => ∑ i, if d i v ≤ R then
        finiteDifference (clippedContrast i (ψ i) M) y.1 y.2 else 0) =
      (∑ i, fun y : Profile V × V => if d i v ≤ R then
        finiteDifference (clippedContrast i (ψ i) M) y.1 y.2 else 0) := by
      funext y
      simp only [Finset.sum_apply]
    rw [heq, F.tagged.iterate_finset_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiv : d i v ≤ R
    · simp only [hiv, ↓reduceIte]
      exact (F.iterate_finiteDifference h (clippedContrast i (ψ i) M) x v).symm
    · simp [hiv, FiniteKernel.iterate_const]
  rw [hsum] at hp
  convert hp using 1
  ring

/-- Initial-tag averaging of the proved genuine semigroup response. -/
theorem marked_protected_response (F : FiniteMarks V A)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (h : ℕ) (x : Profile V)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) :
    (1 - markedBadGap F h x M - 2 * markedTail F h x w d R) / M ≤
      ∑ i, ∑ v, if d i v ≤ R then
        w v * finiteDifference (F.base.iterate h (clippedContrast i (ψ i) M)) x v else 0 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v hv =>
    mul_le_mul_of_nonneg_left
      (marked_protected_response_at F d hdiag hsym htriangle ψ hR hM hsep h x v) (hw v))
  have he : (∑ v, w v * ((1 - markedBadGap F h x M -
      2 * F.tagged.iterate h (fun y => if R ≤ d v y.2 then 1 else 0) (x, v)) / M)) =
      (1 - markedBadGap F h x M - 2 * markedTail F h x w d R) / M := by
    calc
      _ = ((1 - markedBadGap F h x M) / M) * (∑ v, w v) -
          (2 / M) * markedTail F h x w d R := by
        unfold markedTail
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [hnorm]; ring
  rw [he] at hs
  convert hs using 1
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  exact Finset.sum_comm

/-- Pointwise energy for an actual finite marked allocation process. The response
is the derivative of `F.base.iterate`, rather than an unspecified test array. -/
theorem marked_transport_energy (F : FiniteMarks V A)
    (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M B p q : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hB : 0 < B) (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    (hvolume : ∀ v, ((closedBall d R v).card : ℝ) ≤ B)
    (h : ℕ) (x : Profile V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hnorm : ∑ v, w v = 1) (hp : markedBadGap F h x M ≤ p)
    (hq : markedTail F h x w d R ≤ q) :
    max (1 - p - 2 * q) 0 ^ 2 / (M ^ 2 * B) ≤
      ∑ i, ∑ v, w v * finiteDifference
        (F.base.iterate h (clippedContrast i (ψ i) M)) x v ^ 2 := by
  have hresp := marked_protected_response F d hdiag hsym htriangle ψ hR hM hsep h x w hw hnorm
  have hresp' : (1 - p - 2 * q) / M ≤
      ∑ i, ∑ v, if d i v ≤ R then
        w v * finiteDifference (F.base.iterate h (clippedContrast i (ψ i) M)) x v else 0 := by
    apply le_trans _ hresp
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have he := restricted_response_energy d hsym R id w hw hnorm
    (fun i v => finiteDifference (F.base.iterate h (clippedContrast i (ψ i) M)) x v)
    hB hvolume hresp'
  rwa [protected_energy_normalization (by linarith : 0 < M)] at he

end GraphicalAllocation.Transport
