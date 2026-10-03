import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-branching transition operators

A transition has finitely many outcomes but its state space can be infinite.
This is the expectation-level foundation for event-count graphical allocation.
-/

namespace GraphicalAllocation.Process

open scoped BigOperators

/-- An explicit finite-outcome stochastic transition. -/
structure FiniteKernel (State Choice : Type*) [Fintype Choice] where
  weight : State → Choice → ℝ
  nonneg : ∀ x c, 0 ≤ weight x c
  total : ∀ x, ∑ c, weight x c = 1
  next : State → Choice → State

namespace FiniteKernel

variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

/-- Expected value of a test after one transition. -/
def step (f : State → ℝ) (x : State) : ℝ :=
  ∑ c, K.weight x c * f (K.next x c)

@[simp] theorem step_zero : K.step (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [step]

@[simp] theorem step_add (f g : State → ℝ) :
    K.step (f + g) = K.step f + K.step g := by
  funext x
  simp [step, mul_add, Finset.sum_add_distrib]

@[simp] theorem step_sub (f g : State → ℝ) :
    K.step (f - g) = K.step f - K.step g := by
  funext x
  simp [step, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem step_smul (a : ℝ) (f : State → ℝ) :
    K.step (a • f) = a • K.step f := by
  funext x
  simp [step, Finset.mul_sum, mul_left_comm]

@[simp] theorem step_const (a : ℝ) : K.step (fun _ => a) = fun _ => a := by
  funext x
  simp [step, ← Finset.sum_mul, K.total]

theorem step_mono {f g : State → ℝ} (h : ∀ x, f x ≤ g x) :
    ∀ x, K.step f x ≤ K.step g x := by
  intro x
  exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h _) (K.nonneg x c)

theorem step_nonneg {f : State → ℝ} (h : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ K.step f x := by
  intro x
  exact Finset.sum_nonneg fun c _ => mul_nonneg (K.nonneg x c) (h _)

theorem step_abs_le (f : State → ℝ) (x : State) :
    |K.step f x| ≤ K.step (fun y => |f y|) x := by
  unfold step
  calc
    |∑ c, K.weight x c * f (K.next x c)| ≤
      ∑ c, |K.weight x c * f (K.next x c)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_mul, abs_of_nonneg (K.nonneg x _)]

theorem step_bounded {f : State → ℝ} {B : ℝ} (h : ∀ x, |f x| ≤ B) :
    ∀ x, |K.step f x| ≤ B := by
  intro x
  calc
    |K.step f x| ≤ K.step (fun y => |f y|) x := K.step_abs_le f x
    _ ≤ K.step (fun _ => B) x := K.step_mono h x
    _ = B := congrFun (K.step_const B) x

/-- The expectation after exactly `k` transitions. -/
def iterate : ℕ → (State → ℝ) → State → ℝ
  | 0, f => f
  | k + 1, f => K.step (iterate k f)

@[simp] theorem iterate_zero (f : State → ℝ) : K.iterate 0 f = f := rfl
@[simp] theorem iterate_succ (k : ℕ) (f : State → ℝ) :
    K.iterate (k + 1) f = K.step (K.iterate k f) := rfl

@[simp] theorem iterate_add (k : ℕ) (f g : State → ℝ) :
    K.iterate k (f + g) = K.iterate k f + K.iterate k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

@[simp] theorem iterate_sub (k : ℕ) (f g : State → ℝ) :
    K.iterate k (f - g) = K.iterate k f - K.iterate k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

@[simp] theorem iterate_const (k : ℕ) (a : ℝ) :
    K.iterate k (fun _ => a) = fun _ => a := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem iterate_mono (k : ℕ) {f g : State → ℝ} (h : ∀ x, f x ≤ g x) :
    ∀ x, K.iterate k f x ≤ K.iterate k g x := by
  induction k with
  | zero => exact h
  | succ k ih => exact K.step_mono ih

theorem iterate_nonneg (k : ℕ) {f : State → ℝ} (h : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ K.iterate k f x := by
  induction k with
  | zero => exact h
  | succ k ih => exact K.step_nonneg ih

theorem iterate_bounded (k : ℕ) {f : State → ℝ} {B : ℝ} (h : ∀ x, |f x| ≤ B) :
    ∀ x, |K.iterate k f x| ≤ B := by
  induction k with
  | zero => exact h
  | succ k ih => exact K.step_bounded ih

theorem iterate_add_time (k l : ℕ) (f : State → ℝ) :
    K.iterate (k + l) f = K.iterate k (K.iterate l f) := by
  induction k with
  | zero => simp
  | succ k ih => simp [Nat.succ_add, ih]

theorem iterate_step (k : ℕ) (f : State → ℝ) :
    K.iterate k (K.step f) = K.step (K.iterate k f) := by
  simpa [Nat.add_comm] using (K.iterate_add_time k 1 f).symm

/-- One-step conditional variance of a test. -/
def variance (f : State → ℝ) (x : State) : ℝ :=
  K.step (fun y => f y ^ 2) x - K.step f x ^ 2

theorem variance_eq_sum (f : State → ℝ) (x : State) :
    K.variance f x =
      ∑ c, K.weight x c * (f (K.next x c) - K.step f x) ^ 2 := by
  simp only [variance, sub_sq, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h₁ : ∑ c, K.weight x c * (2 * f (K.next x c) * K.step f x) =
      2 * K.step f x ^ 2 := by
    calc
      _ = (∑ c, K.weight x c * f (K.next x c)) * (2 * K.step f x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by rw [← step]; ring
  rw [h₁, ← Finset.sum_mul, K.total]
  unfold step
  ring

theorem variance_nonneg (f : State → ℝ) (x : State) :
    0 ≤ K.variance f x := by
  rw [K.variance_eq_sum]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (K.nonneg x c) (sq_nonneg _)

theorem variance_le_one {f : State → ℝ} (h : ∀ x, |f x| ≤ 1) (x : State) :
    K.variance f x ≤ 1 := by
  have hs : K.step (fun y => f y ^ 2) x ≤ 1 := by
    have hsq : ∀ y, f y ^ 2 ≤ 1 := fun y => by
      have hy := abs_le.mp (h y)
      nlinarith [sq_nonneg (f y - 1), sq_nonneg (f y + 1), mul_nonneg (by linarith : 0 ≤ 1 - f y) (by linarith : 0 ≤ 1 + f y)]
    simpa using K.step_mono hsq x
  unfold variance
  nlinarith [sq_nonneg (K.step f x)]

end FiniteKernel
end GraphicalAllocation.Process
