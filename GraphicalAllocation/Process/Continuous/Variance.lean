import GraphicalAllocation.Process.Continuous.Semigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Exact finite-horizon variance identity

This is the analytic proof of the response-energy budget for the actual
Poissonized finite transition. The proof differentiates a bounded function-valued
second moment and uses the fundamental theorem of calculus. It does not assume
a martingale or variance identity as a process axiom.
-/

noncomputable section

namespace GraphicalAllocation.Process.FiniteKernel

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

variable {State Choice : Type*} [Fintype Choice]
variable [TopologicalSpace State] [DiscreteTopology State]
variable (K : FiniteKernel State Choice)

local instance : NormedAddCommGroup (State →ᵇ ℝ) := inferInstance
local instance : NormedSpace ℝ (State →ᵇ ℝ) := inferInstance
local instance : NormedRing ((State →ᵇ ℝ) →L[ℝ] (State →ᵇ ℝ)) := inferInstance

/-- Continuity of the carré du champ as a map on bounded observables. -/
theorem continuous_energy (rate : ℝ) : Continuous (K.energy rate) := by
  unfold energy
  exact (K.generator rate).continuous.comp (continuous_id.pow 2) |>.sub
    ((continuous_id.mul (K.generator rate).continuous).const_smul (2 : ℝ))

/-- At intermediate time `u`, the expected squared backward-semigroup test. -/
def secondMomentBridge (rate t : ℝ) (f : State →ᵇ ℝ) (u : ℝ) : State →ᵇ ℝ :=
  K.semigroup rate u ((K.semigroup rate (t - u) f) ^ 2)

/-- The response-energy density, transported from the intermediate state. -/
def transportedEnergy (rate t : ℝ) (f : State →ᵇ ℝ) (u : ℝ) : State →ᵇ ℝ :=
  K.semigroup rate u (K.energy rate (K.semigroup rate (t - u) f))

theorem continuous_transportedEnergy (rate t : ℝ) (f : State →ᵇ ℝ) :
    Continuous (K.transportedEnergy rate t f) := by
  apply (K.continuous_semigroup rate).clm_apply
  exact (K.continuous_energy rate).comp
    (((K.continuous_semigroup rate).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const)

theorem hasDerivAt_secondMomentBridge (rate t : ℝ) (f : State →ᵇ ℝ) (u : ℝ) :
    HasDerivAt (K.secondMomentBridge rate t f) (K.transportedEnergy rate t f u) u := by
  have hg : HasDerivAt (fun v => K.semigroup rate (t - v) f)
      (-K.generator rate (K.semigroup rate (t - u) f)) u := by
    convert! (K.hasDerivAt_semigroup_apply' rate (t - u) f).scomp u
      ((hasDerivAt_id u).const_sub t) using 1
    simp
  have h := (K.hasDerivAt_semigroup rate u).clm_apply (hg.mul hg)
  convert h using 1
  · ext v
    simp [secondMomentBridge, pow_two]
  · dsimp [transportedEnergy]
    change K.semigroup rate u (K.energy rate (K.semigroup rate (t - u) f)) = _
    change K.semigroup rate u (K.energy rate (K.semigroup rate (t - u) f)) =
      K.semigroup rate u (K.generator rate (_ * _)) + _
    rw [← map_add]
    congr 1
    simp only [energy, pow_two]
    ext x
    simp
    ring

/-- Exact variance production for a deterministic initial state, as an identity
in the Banach space of bounded functions. -/
theorem integral_transportedEnergy (rate t : ℝ) (f : State →ᵇ ℝ) :
    (∫ u in (0 : ℝ)..t, K.transportedEnergy rate t f u) =
      K.semigroup rate t (f ^ 2) - (K.semigroup rate t f) ^ 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => K.hasDerivAt_secondMomentBridge rate t f u)
    ((K.continuous_transportedEnergy rate t f).intervalIntegrable 0 t)
  simpa [secondMomentBridge] using h

/-- The nonnegative response density on a forward horizon. -/
theorem transportedEnergy_nonneg {rate t u : ℝ} (hr : 0 ≤ rate) (hu : 0 ≤ u)
    (f : State →ᵇ ℝ) (x : State) : 0 ≤ K.transportedEnergy rate t f u x :=
  K.semigroup_nonneg hr hu (K.energy_nonneg hr _) x

end GraphicalAllocation.Process.FiniteKernel
