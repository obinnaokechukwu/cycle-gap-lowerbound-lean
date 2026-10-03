import GraphicalAllocation.Process.FiniteKernel
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A finite transition as a bounded Markov operator

The state space is discrete, but need not be finite. The Banach space of bounded
continuous functions therefore contains exactly the bounded real observables.
-/

noncomputable section

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators BoundedContinuousFunction

variable {State Choice : Type*} [Fintype Choice]
variable [TopologicalSpace State] [DiscreteTopology State]
variable (K : FiniteKernel State Choice)

/-- One transition acting on bounded observables. -/
def boundedStep (f : State →ᵇ ℝ) : State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (K.step f) ‖f‖
    (K.step_bounded (fun x => f.norm_coe_le_norm x))

@[simp] theorem boundedStep_apply (f : State →ᵇ ℝ) (x : State) :
    K.boundedStep f x = K.step f x := rfl

theorem norm_boundedStep_le (f : State →ᵇ ℝ) : ‖K.boundedStep f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
    (K.step_bounded (fun x => f.norm_coe_le_norm x))

/-- The positive unital contraction associated to a finite branching kernel. -/
def operator : (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := K.boundedStep
      map_add' := fun f g => by
        ext x
        exact congrFun (K.step_add f g) x
      map_smul' := fun a f => by
        ext x
        exact congrFun (K.step_smul a f) x }
    1 (fun f => by simpa using K.norm_boundedStep_le f)

@[simp] theorem operator_apply (f : State →ᵇ ℝ) (x : State) :
    K.operator f x = K.step f x := rfl

theorem norm_operator_le : ‖K.operator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound K.operator (by norm_num)
  intro f
  simpa [operator] using K.norm_boundedStep_le f

@[simp] theorem operator_const (c : ℝ) :
    K.operator (BoundedContinuousFunction.const State c) =
      BoundedContinuousFunction.const State c := by
  ext x
  exact congrFun (K.step_const c) x

theorem operator_nonneg {f : State →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) (x : State) :
    0 ≤ K.operator f x := K.step_nonneg hf x

@[simp] theorem operator_pow_apply (n : ℕ) (f : State →ᵇ ℝ) (x : State) :
    (K.operator ^ n) f x = K.iterate n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change K.step ((K.operator ^ n) f) x = K.step (K.iterate n f) x
    congr 1
    funext y
    exact ih y

/-- Rate-scaled jump generator. -/
def generator (rate : ℝ) : (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ) :=
  rate • (K.operator - 1)

@[simp] theorem generator_apply (rate : ℝ) (f : State →ᵇ ℝ) (x : State) :
    K.generator rate f x = rate * (K.step f x - f x) := rfl

/-- Pointwise carré du champ, expressed without subtracting variances. -/
def energy (rate : ℝ) (f : State →ᵇ ℝ) : State →ᵇ ℝ :=
  K.generator rate (f ^ 2) - (2 : ℝ) • (f * K.generator rate f)

 theorem energy_apply (rate : ℝ) (f : State →ᵇ ℝ) (x : State) :
    K.energy rate f x =
      rate * ∑ c, K.weight x c * (f (K.next x c) - f x) ^ 2 := by
  change rate * (K.step (f ^ 2) x - f x ^ 2) -
    2 * (f x * (rate * (K.step f x - f x))) = _
  have h : ∑ c, K.weight x c * (f (K.next x c) - f x) ^ 2 =
      K.step (f ^ 2) x - 2 * f x * K.step f x + f x ^ 2 := by
    simp only [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, K.total, one_mul]
    unfold step
    simp only [Pi.pow_apply]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h]
  ring

theorem energy_nonneg {rate : ℝ} (hr : 0 ≤ rate) (f : State →ᵇ ℝ) (x : State) :
    0 ≤ K.energy rate f x := by
  rw [K.energy_apply]
  exact mul_nonneg hr (Finset.sum_nonneg fun c _ =>
    mul_nonneg (K.nonneg x c) (sq_nonneg _))

end GraphicalAllocation.Process.FiniteKernel
