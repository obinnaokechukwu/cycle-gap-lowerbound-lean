import GraphicalAllocation.Process.FiniteKernel
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Probability laws of the explicit process

The event-count law is constructed by independent finite choices. Continuous time
is an independent Poisson event count. Initial distributions are arbitrary PMFs;
on the countable integer-profile space these represent all probability measures.
-/

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators NNReal ENNReal
open MeasureTheory

variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

/-- The state-dependent probability mass function of the next finite choice. -/
noncomputable def choiceLaw (x : State) : PMF Choice :=
  PMF.ofFintype (fun c => ENNReal.ofReal (K.weight x c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => K.nonneg x c), K.total]
    simp)

@[simp] theorem choiceLaw_apply (x : State) (c : Choice) :
    K.choiceLaw x c = ENNReal.ofReal (K.weight x c) := rfl

/-- Law after exactly `k` updates, from a deterministic state. -/
noncomputable def eventLaw : ℕ → State → PMF State
  | 0, x => PMF.pure x
  | k + 1, x => (K.choiceLaw x).bind (fun c => eventLaw k (K.next x c))

@[simp] theorem eventLaw_zero (x : State) : K.eventLaw 0 x = PMF.pure x := rfl

@[simp] theorem eventLaw_succ (k : ℕ) (x : State) :
    K.eventLaw (k + 1) x = (K.choiceLaw x).bind (fun c => K.eventLaw k (K.next x c)) := rfl

theorem eventLaw_add (k l : ℕ) (x : State) :
    K.eventLaw (k + l) x = (K.eventLaw k x).bind (K.eventLaw l) := by
  induction k generalizing x with
  | zero => simp [PMF.pure_bind]
  | succ k ih =>
    simp only [Nat.succ_add, eventLaw_succ, PMF.bind_bind]
    congr 1
    funext c
    exact ih _

/-- The event-count law from an arbitrary initial distribution. -/
noncomputable def eventLawFrom (μ : PMF State) (k : ℕ) : PMF State :=
  μ.bind (K.eventLaw k)

/-- The total event rate times elapsed physical time. -/
noncomputable def continuousLaw (rate time : ℝ≥0) (x : State) : PMF State :=
  (ProbabilityTheory.poissonMeasure (rate * time)).toPMF.bind (fun k => K.eventLaw k x)

/-- Initial states are sampled before independent future clocks and choices. -/
noncomputable def continuousLawFrom (μ : PMF State) (rate time : ℝ≥0) : PMF State :=
  μ.bind (K.continuousLaw rate time)

/-- A nonnegative observable's expectation, including the value infinity. -/
noncomputable def nonnegativeExpectation (μ : PMF State) (g : State → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, μ x * g x

/-- Event probability; no integrability assumptions are needed. -/
noncomputable def probability (μ : PMF State) (s : Set State) : ℝ≥0∞ :=
  μ.toOuterMeasure s

section Measurable

variable [MeasurableSpace Choice] [MeasurableSingletonClass Choice]

/-- The finite real expectation matches the genuine choice-law integral. -/
theorem integral_choiceLaw (x : State) (f : Choice → ℝ) :
    ∫ c, f c ∂(K.choiceLaw x).toMeasure = ∑ c, K.weight x c * f c := by
  rw [PMF.integral_eq_sum]
  simp [ENNReal.toReal_ofReal (K.nonneg x _)]

end Measurable

end GraphicalAllocation.Process.FiniteKernel
