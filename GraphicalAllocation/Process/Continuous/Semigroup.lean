import GraphicalAllocation.Process.Continuous.Kernel
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Poissonized finite-branching Markov semigroup

The definition is the exponential of the bounded jump generator. Its series
representation is exactly the Poisson mixture of finite event-count transitions.
-/

noncomputable section


namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators BoundedContinuousFunction

variable {State Choice : Type*} [Fintype Choice]
variable [TopologicalSpace State] [DiscreteTopology State]
variable (K : FiniteKernel State Choice)

-- Pin the operator norm topology before asking for the topological-ring instance.
local instance : NormedAddCommGroup (State →ᵇ ℝ) := inferInstance
local instance : NormedSpace ℝ (State →ᵇ ℝ) := inferInstance
local instance : NormedRing ((State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) := inferInstance

local instance : NormedAlgebra ℝ ((State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) := inferInstance
local instance : NormedAlgebra ℚ ((State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The rate-`rate` continuous-time transition operator, defined for all real
parameters; Markov positivity is asserted for nonnegative time and rate. -/
def semigroup (rate t : ℝ) : (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ) :=
  NormedSpace.exp (t • K.generator rate)

@[simp] theorem semigroup_zero (rate : ℝ) : K.semigroup rate 0 = 1 := by
  simp [semigroup]

theorem semigroup_add (rate s t : ℝ) :
    K.semigroup rate (s + t) = K.semigroup rate s * K.semigroup rate t := by
  simp only [semigroup, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

theorem semigroup_commute (rate s t : ℝ) :
    Commute (K.semigroup rate s) (K.semigroup rate t) := by
  show _ * _ = _ * _
  rw [← K.semigroup_add, ← K.semigroup_add, add_comm]

theorem hasDerivAt_semigroup (rate t : ℝ) :
    HasDerivAt (K.semigroup rate)
      (K.semigroup rate t * K.generator rate) t :=
  hasDerivAt_exp_smul_const (K.generator rate) t

theorem hasDerivAt_semigroup' (rate t : ℝ) :
    HasDerivAt (K.semigroup rate)
      (K.generator rate * K.semigroup rate t) t :=
  hasDerivAt_exp_smul_const' (K.generator rate) t

theorem continuous_semigroup (rate : ℝ) : Continuous (K.semigroup rate) :=
  continuous_iff_continuousAt.mpr fun t => (K.hasDerivAt_semigroup rate t).continuousAt

theorem hasDerivAt_semigroup_apply (rate t : ℝ) (f : State →ᵇ ℝ) :
    HasDerivAt (fun u => K.semigroup rate u f)
      (K.semigroup rate t (K.generator rate f)) t := by
  simpa using (K.hasDerivAt_semigroup rate t).clm_apply (hasDerivAt_const t f)

theorem hasDerivAt_semigroup_apply' (rate t : ℝ) (f : State →ᵇ ℝ) :
    HasDerivAt (fun u => K.semigroup rate u f)
      (K.generator rate (K.semigroup rate t f)) t := by
  simpa using (K.hasDerivAt_semigroup' rate t).clm_apply (hasDerivAt_const t f)

omit [DiscreteTopology State] in
private theorem exp_scalar_one (r : ℝ) :
    NormedSpace.exp (r • (1 : (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ))) =
      Real.exp r • 1 := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝔸 := (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) r).symm

theorem semigroup_eq_exp_operator (rate t : ℝ) :
    K.semigroup rate t = Real.exp (-(t * rate)) •
      NormedSpace.exp ((t * rate) • K.operator) := by
  have hsplit : t • K.generator rate =
      (-(t * rate)) • (1 : (State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) +
        (t * rate) • K.operator := by
    simp [generator, smul_smul, smul_sub]
    abel
  rw [semigroup, hsplit, NormedSpace.exp_add_of_commute
    (((Commute.one_left _).smul_left (-(t * rate))).smul_right (t * rate)),
    exp_scalar_one, smul_mul_assoc, one_mul]

/-- The scalar Poisson weight, including the degenerate time-zero law. -/
def poissonWeight (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a) * (n.factorial : ℝ)⁻¹ * a ^ n

theorem poissonWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ poissonWeight a n :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (pow_nonneg ha _)

/-- The exponential formula as a convergent Poisson mixture. -/
theorem semigroup_hasSum (rate t : ℝ) (f : State →ᵇ ℝ) (x : State) :
    HasSum (fun n => poissonWeight (t * rate) n * K.iterate n f x)
      (K.semigroup rate t f x) := by
  let L := (BoundedContinuousFunction.evalCLM ℝ x).comp
    (ContinuousLinearMap.apply ℝ (State →ᵇ ℝ) f)
  have h := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    ((t * rate) • K.operator))
  simp only [smul_pow] at h
  have h' := h.mul_left (Real.exp (-(t * rate)))
  simpa only [L, ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    ContinuousLinearMap.apply_apply, smul_apply,
    BoundedContinuousFunction.smul_apply, K.operator_pow_apply,
    poissonWeight, K.semigroup_eq_exp_operator, smul_smul, smul_eq_mul, mul_assoc] using h' 

theorem semigroup_nonneg {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t)
    {f : State →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) (x : State) :
    0 ≤ K.semigroup rate t f x :=
  HasSum.nonneg (fun n => mul_nonneg (poissonWeight_nonneg (mul_nonneg ht hr) n)
    (K.iterate_nonneg n hf x)) (K.semigroup_hasSum rate t f x)

theorem poissonWeight_hasSum (a : ℝ) : HasSum (poissonWeight a) 1 := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_left (Real.exp (-a))
  change HasSum (fun n => Real.exp (-a) * (n.factorial : ℝ)⁻¹ * a ^ n) 1
  simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_assoc] using h

@[simp] theorem semigroup_const (rate t c : ℝ) :
    K.semigroup rate t (BoundedContinuousFunction.const State c) =
      BoundedContinuousFunction.const State c := by
  ext x
  have h := K.semigroup_hasSum rate t (BoundedContinuousFunction.const State c) x
  have hc : HasSum (fun n => poissonWeight (t * rate) n *
      K.iterate n (BoundedContinuousFunction.const State c) x) c := by
    simpa using ((poissonWeight_hasSum (t * rate)).mul_right c)
  exact h.unique hc

theorem semigroup_mono {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t)
    {f g : State →ᵇ ℝ} (hfg : ∀ x, f x ≤ g x) (x : State) :
    K.semigroup rate t f x ≤ K.semigroup rate t g x := by
  have h := K.semigroup_nonneg hr ht (f := g - f) (fun x => sub_nonneg.mpr (hfg x)) x
  simpa only [map_sub, BoundedContinuousFunction.sub_apply, sub_nonneg] using h

theorem semigroup_bounded {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t)
    {f : State →ᵇ ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) (x : State) :
    |K.semigroup rate t f x| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := K.semigroup_mono hr ht
      (f := BoundedContinuousFunction.const State (-B)) (g := f)
      (fun y => (abs_le.mp (hf y)).1) x
    simpa using h
  · have h := K.semigroup_mono hr ht
      (f := f) (g := BoundedContinuousFunction.const State B)
      (fun y => (abs_le.mp (hf y)).2) x
    simpa using h

theorem norm_semigroup_apply_le {rate t : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ t)
    (f : State →ᵇ ℝ) : ‖K.semigroup rate t f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  exact K.semigroup_bounded hr ht (fun x => f.norm_coe_le_norm x)

end GraphicalAllocation.Process.FiniteKernel
