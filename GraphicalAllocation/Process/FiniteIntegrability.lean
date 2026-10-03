import GraphicalAllocation.Process.LawExpectation

/-!
# Arbitrary observables at a finite deterministic event horizon

A finite-branching chain from a fixed state has finitely many terminal outcomes.
Consequently every real terminal observable is integrable, even when it is not
bounded on the entire state space. This is the upper-bound expectation bridge.
-/

namespace GraphicalAllocation.Process.FiniteKernel
open scoped BigOperators ENNReal
open MeasureTheory

variable {State Choice : Type*} [Fintype Choice]
variable [MeasurableSpace State] [MeasurableSingletonClass State]
variable (K : FiniteKernel State Choice)

/-- Finite horizons from a deterministic state give finite support and all real moments. -/
theorem integrable_eventLaw (k : ℕ) (x : State) (f : State → ℝ) :
    Integrable f (K.eventLaw k x).toMeasure := by
  induction k generalizing x with
  | zero =>
    simp only [eventLaw, PMF.toMeasure_pure]
    exact integrable_dirac (by simp)
  | succ k ih =>
    rw [eventLaw_succ, toMeasure_bind_fintype]
    apply integrable_finsetSum_measure.mpr
    intro c _
    exact (ih (K.next x c)).smul_measure ((K.choiceLaw x).apply_ne_top c)

/-- The finite-branching expectation formula needs no global bound on its test. -/
theorem integral_eventLaw_unbounded (k : ℕ) (x : State) (f : State → ℝ) :
    (∫ y, f y ∂(K.eventLaw k x).toMeasure) = K.iterate k f x := by
  induction k generalizing x with
  | zero => simp [eventLaw, PMF.toMeasure_pure]
  | succ k ih =>
    rw [eventLaw_succ, integral_bind_fintype]
    · simp only [choiceLaw_apply, ENNReal.toReal_ofReal (K.nonneg _ _), ih, iterate_succ, step]
    · exact fun c => K.integrable_eventLaw k (K.next x c) f

/-- Nonnegative finite-horizon expectations retain the extended-valued convention. -/
theorem lintegral_eventLaw_ofReal (k : ℕ) (x : State) (f : State → ℝ)
    (hf : ∀ y, 0 ≤ f y) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂(K.eventLaw k x).toMeasure) =
      ENNReal.ofReal (K.iterate k f x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (K.integrable_eventLaw k x f) (ae_of_all _ hf),
    K.integral_eventLaw_unbounded]

end GraphicalAllocation.Process.FiniteKernel
