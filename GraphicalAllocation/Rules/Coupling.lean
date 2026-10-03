import GraphicalAllocation.Rules.Selector
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Fixed-mark thresholds and finite-event one-ball coupling

The pathwise construction is deterministic and accepts every finite sequence of
marks. In particular no independence or distributional hypothesis is needed for
the one-ball identity. The finite weighted-expectation theorem is its algebraic
integration over an arbitrary finite sample space.
-/

namespace GraphicalAllocation.Rules

variable {V : Type*} [DecidableEq V]

/-- Real marks implement the paper's decision `mark ≤ p (x u - x v)`. -/
noncomputable def thresholdSelector (u v : V) (p : ℤ → ℝ) (mark : ℝ) :
    Profile V → Bool := fun x => decide (mark ≤ p (x u - x v))

omit [DecidableEq V] in
theorem threshold_endpointAntitone (u v : V) {p : ℤ → ℝ} (hp : Antitone p)
    (mark : ℝ) : EndpointAntitone u v (thresholdSelector u v p mark) := by
  classical
  refine ⟨fun d => decide (mark ≤ p d), (fun _ => rfl), ?_⟩
  intro a b hab hb
  simp only [decide_eq_true_eq] at hb ⊢
  exact hb.trans (hp hab)

omit [DecidableEq V] in
theorem threshold_translationInvariant (u v : V) (p : ℤ → ℝ) (mark : ℝ) :
    TranslationInvariant (thresholdSelector u v p mark) := by
  intro x c
  have hc : x u + c - (x v + c) = x u - x v := by omega
  simp only [thresholdSelector, translate, hc]

theorem threshold_unitDiscrepancy {u v : V} (huv : u ≠ v)
    {p : ℤ → ℝ} (hp : Antitone p) (mark : ℝ) :
    UnitDiscrepancy u v (thresholdSelector u v p mark) :=
  unitDiscrepancy_of_endpointAntitone huv (threshold_endpointAntitone u v hp mark)

theorem threshold_switchAway {u v : V} (huv : u ≠ v)
    {p : ℤ → ℝ} (hp : Antitone p) (mark : ℝ) :
    SwitchAway u v (thresholdSelector u v p mark) :=
  switchAway_of_unitDiscrepancy huv (threshold_unitDiscrepancy huv hp mark)

/-- A deterministic event together with its proved local discrepancy property. -/
structure Event (V : Type*) [DecidableEq V] where
  first : V
  second : V
  selector : Profile V → Bool
  switchAway : SwitchAway first second selector

namespace Event

variable (e : Event V)

def apply (x : Profile V) : Profile V := update e.first e.second e.selector x

/-- The tag stays when decisions agree and follows the new choice otherwise. -/
def tag (x : Profile V) (z : V) : V :=
  if e.selector (raise x z) = e.selector x then z
  else selected e.first e.second e.selector (raise x z)

/-- The explicit tag update, without choice of an existential witness. -/
theorem oneBall (x : Profile V) (z : V) :
    e.apply (raise x z) = raise (e.apply x) (e.tag x z) := by
  by_cases hs : e.selector (raise x z) = e.selector x
  · simp only [tag, hs, ↓reduceIte, apply, update, selected]
    exact raise_comm x z _
  · simp only [tag, hs, ↓reduceIte, apply, update]
    rw [e.switchAway x z hs]

/-- Every fixed-mark monotone randomized allocation is a valid deterministic event. -/
noncomputable def ofThreshold (u v : V) (huv : u ≠ v) (p : ℤ → ℝ)
    (hp : Antitone p) (mark : ℝ) : Event V where
  first := u
  second := v
  selector := thresholdSelector u v p mark
  switchAway := threshold_switchAway huv hp mark

end Event

/-- Execute an event sequence in chronological order. -/
def run : List (Event V) → Profile V → Profile V
  | [], x => x
  | e :: es, x => run es (e.apply x)

/-- Track the extra ball along the same chronological event sequence. -/
def runTag : List (Event V) → Profile V → V → V
  | [], _, z => z
  | e :: es, x, z => runTag es (e.apply x) (e.tag x z)

/-- Equations (2.3) and the pathwise part of (2.5), after a finite event sequence. -/
theorem run_oneBall (events : List (Event V)) (x : Profile V) (z : V) :
    run events (raise x z) = raise (run events x) (runTag events x z) := by
  induction events generalizing x z with
  | nil => rfl
  | cons e es ih =>
      simp only [run, runTag]
      rw [e.oneBall]
      exact ih (e.apply x) (e.tag x z)

/-- Finite difference in an integer-profile coordinate. -/
def finiteDifference (f : Profile V → ℝ) (x : Profile V) (z : V) : ℝ :=
  f (raise x z) - f x

/-- Pathwise derivative-tag identity; boundedness and translation invariance
are unnecessary before passage to infinite-dimensional expectations. -/
theorem finiteDifference_run (events : List (Event V)) (f : Profile V → ℝ)
    (x : Profile V) (z : V) :
    finiteDifference (fun y => f (run events y)) x z =
      finiteDifference f (run events x) (runTag events x z) := by
  simp only [finiteDifference, run_oneBall]

open scoped BigOperators

/-- The transition average for a finite sample space of event sequences. -/
noncomputable def finiteExpectation {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (events : Ω → List (Event V)) (f : Profile V → ℝ)
    (x : Profile V) : ℝ := ∑ ω, weight ω * f (run (events ω) x)

/-- The finite-expectation version of equations (2.4)–(2.5). It is valid for any
real weights, hence in particular any finite probability distribution. -/
theorem finiteDifference_expectation {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (events : Ω → List (Event V)) (f : Profile V → ℝ)
    (x : Profile V) (z : V) :
    finiteDifference (finiteExpectation weight events f) x z =
      ∑ ω, weight ω * finiteDifference f (run (events ω) x) (runTag (events ω) x z) := by
  simp only [finiteDifference, finiteExpectation, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [run_oneBall]
  ring

end GraphicalAllocation.Rules
