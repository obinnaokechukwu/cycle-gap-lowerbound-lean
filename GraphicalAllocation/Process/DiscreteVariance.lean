import GraphicalAllocation.Process.FiniteKernel
import Mathlib.Algebra.BigOperators.Pi

/-!
# Event-time response energy

This module proves the exact variance correction and the telescoping finite-horizon
variance budget for an explicit finite-outcome transition kernel.
-/

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators

variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

/-- Mean squared response to a single transition. -/
def responseEnergy (f : State → ℝ) (x : State) : ℝ :=
  ∑ c, K.weight x c * (f (K.next x c) - f x) ^ 2

theorem responseEnergy_nonneg (f : State → ℝ) (x : State) :
    0 ≤ K.responseEnergy f x :=
  Finset.sum_nonneg fun c _ => mul_nonneg (K.nonneg x c) (sq_nonneg _)

/-- The mean-increment subtraction in equation (6.3). -/
theorem variance_eq_responseEnergy (f : State → ℝ) (x : State) :
    K.variance f x = K.responseEnergy f x - (K.step f x - f x) ^ 2 := by
  unfold responseEnergy variance
  simp only [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have h₁ : ∑ c, K.weight x c * (2 * f (K.next x c) * f x) =
      2 * K.step f x * f x := by
    calc
      _ = (∑ c, K.weight x c * f (K.next x c)) * (2 * f x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by rw [← step]; ring
  rw [h₁, ← Finset.sum_mul, K.total]
  unfold step
  ring

/-- Iterating commutes with the one-step mean-increment operator. -/
theorem iterate_increment (k : ℕ) (f : State → ℝ) :
    K.step (K.iterate k f) - K.iterate k f = K.iterate k (K.step f - f) := by
  rw [K.iterate_sub, K.iterate_step]

theorem iterate_increment_bounded (k : ℕ) (f : State → ℝ) (B : ℝ)
    (h : ∀ x, |K.step f x - f x| ≤ B) :
    ∀ x, |K.step (K.iterate k f) x - K.iterate k f x| ≤ B := by
  have hi := K.iterate_bounded k h
  intro x
  change |(K.step (K.iterate k f) - K.iterate k f) x| ≤ B
  rw [K.iterate_increment]
  exact hi x

theorem step_finset_sum {ι : Type*} (s : Finset ι) (f : ι → State → ℝ) :
    K.step (∑ i ∈ s, f i) = ∑ i ∈ s, K.step (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact K.step_zero
  | @insert a s ha ih => simp [ha, ih]

/-- Total variance of the terminal test, conditioned on the initial state. -/
def terminalVariance (k : ℕ) (f : State → ℝ) (x : State) : ℝ :=
  K.iterate k (fun y => f y ^ 2) x - K.iterate k f x ^ 2

@[simp] theorem terminalVariance_zero (f : State → ℝ) :
    K.terminalVariance 0 f = 0 := by
  funext x
  simp [terminalVariance]

theorem terminalVariance_succ (k : ℕ) (f : State → ℝ) :
    K.terminalVariance (k + 1) f =
      K.step (K.terminalVariance k f) + K.variance (K.iterate k f) := by
  funext x
  unfold terminalVariance variance
  change K.step (K.iterate k (fun y => f y ^ 2)) x - _ = _
  rw [show (fun x => K.iterate k (fun y => f y ^ 2) x - K.iterate k f x ^ 2) =
    K.iterate k (fun y => f y ^ 2) - (fun x => K.iterate k f x ^ 2) from rfl]
  rw [K.step_sub]
  simp only [Pi.add_apply, Pi.sub_apply, iterate_succ]
  ring

/-- Exact discrete martingale isometry, written entirely as finite expectation algebra. -/
theorem terminalVariance_eq_sum (k : ℕ) (f : State → ℝ) :
    K.terminalVariance k f =
      ∑ h ∈ Finset.range k, K.iterate (k - 1 - h) (K.variance (K.iterate h f)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [K.terminalVariance_succ, ih, K.step_finset_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, iterate_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    have hh' := Finset.mem_range.mp hh
    have he : k - h = (k - 1 - h) + 1 := by omega
    rw [he, iterate_succ]

theorem terminalVariance_nonneg (k : ℕ) (f : State → ℝ) (x : State) :
    0 ≤ K.terminalVariance k f x := by
  rw [K.terminalVariance_eq_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg fun h _ => K.iterate_nonneg _ (K.variance_nonneg _) x

/-- A bounded terminal test supplies an energy budget of one. -/
theorem terminalVariance_le_one (k : ℕ) {f : State → ℝ}
    (hf : ∀ x, |f x| ≤ 1) (x : State) :
    K.terminalVariance k f x ≤ 1 := by
  have hs : K.iterate k (fun y => f y ^ 2) x ≤ 1 := by
    have hsq : ∀ y, f y ^ 2 ≤ 1 := fun y => by
      have hy := abs_le.mp (hf y)
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - f y) (by linarith : 0 ≤ 1 + f y)]
    simpa using K.iterate_mono k hsq x
  unfold terminalVariance
  nlinarith [sq_nonneg (K.iterate k f x)]

/-- Full event-time bracket budget, including the crucial terminal `k+1`. -/
theorem discrete_bracket_budget (k : ℕ) {f : State → ℝ}
    (hf : ∀ x, |f x| ≤ 1) (x : State) :
    (∑ h ∈ Finset.range (k + 1),
      K.iterate (k - h) (K.variance (K.iterate h f)) x) ≤ 1 := by
  have h := K.terminalVariance_le_one (k + 1) hf x
  rw [K.terminalVariance_eq_sum] at h
  simpa only [Nat.add_sub_cancel, Finset.sum_apply] using h

end GraphicalAllocation.Process.FiniteKernel
