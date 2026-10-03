import GraphicalAllocation.Universal.Laws

/-!
# Canonical arbitrary-history statements of Proposition 7.8

A policy is an arbitrary Bernoulli probability depending on the initial profile,
the entire observed edge/choice history, and the currently arriving edge.
Conditioning additional private randomness gives precisely such probabilities.
The probability law below constructs fresh independent uniform arrivals; the
independence and untouched-vertex estimates are theorems, not policy fields.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped NNReal ENNReal
open Process Rules Transport MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]

/-- Lift an arbitrary initial load law to an empty observed history. -/
def historyInitialLaw (μ : PMF (Profile V)) : PMF (HistoryState G) :=
  μ.map (fun x => ⟨x, []⟩)

/-- The actual load law after `k` arrivals under a fully history-dependent policy. -/
def historyEventLaw (p : HistoryState G → G.edgeSet → ℝ)
    (hp0 : ∀ x e, 0 ≤ p x e) (hp1 : ∀ x e, p x e ≤ 1)
    (μ : PMF (Profile V)) (k : ℕ) : PMF (Profile V) :=
  ((historyStrategy G p hp0 hp1).kernel.eventLawFrom (historyInitialLaw G μ) k).map
    (historyStrategy G p hp0 hp1).load

/-- The published discrete-time assertion for arbitrary adapted randomized
history policies and every initial profile law. -/
theorem history_discrete_probability
    (p : HistoryState G → G.edgeSet → ℝ)
    (hp0 : ∀ x e, 0 ≤ p x e) (hp1 : ∀ x e, p x e ≤ 1)
    (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : max 1000 ((9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ)) ≤ Fintype.card V)
    (μ : PMF (Profile V)) (k : ℕ) (hk : logWindow (Fintype.card V) ≤ k) :
    (1 / 2 : ℝ≥0∞) ≤ (historyEventLaw G p hp0 hp1 μ k).toMeasure
      {x | Real.log (Fintype.card V) / 64 ≤ gap x} := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure]
  unfold historyEventLaw
  rw [PMF.toOuterMeasure_map_apply]
  exact (historyStrategy G p hp0 hp1).discrete_probability Δ hΔ
    ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN) (historyInitialLaw G μ) k hk

/-- A clock-conditioned physical law. Each event count may use its own arbitrary
history policy. This includes policies depending on event times: after
conditioning on times, their endpoint randomization is encoded by the policy. -/
def clockConditionedLaw
    (p : ℕ → HistoryState G → G.edgeSet → ℝ)
    (hp0 : ∀ k x e, 0 ≤ p k x e) (hp1 : ∀ k x e, p k x e ≤ 1)
    (μ : ℕ → PMF (Profile V)) (t : ℝ≥0) : PMF (Profile V) :=
  (poissonMeasure ((Fintype.card G.edgeSet : ℝ≥0) * t)).toPMF.bind
    (fun k => historyEventLaw G (p k) (hp0 k) (hp1 k) (μ k) k)

/-- The full physical-time assertion permits clock-conditioned policies and
initial laws, and therefore in particular every law independent of future clocks. -/
theorem history_continuous_probability
    (p : ℕ → HistoryState G → G.edgeSet → ℝ)
    (hp0 : ∀ k x e, 0 ≤ p k x e) (hp1 : ∀ k x e, p k x e ≤ 1)
    (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : max 1000 ((9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ)) ≤ Fintype.card V)
    (μ : ℕ → PMF (Profile V)) (t : ℝ≥0)
    (ht : Real.log (Fintype.card V) / (4 * Δ) ≤ t) :
    (7 / 16 : ℝ≥0∞) ≤ (clockConditionedLaw G p hp0 hp1 μ t).toMeasure
      {x | Real.log (Fintype.card V) / 64 ≤ gap x} := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure]
  have hcount := poisson_window_size G Δ hΔ ((le_max_left _ _).trans hN) t ht
  apply poisson_mixture_lower _ hcount.1 _ hcount.2
  intro k hk
  simpa only [PMF.toMeasure_apply_eq_toOuterMeasure] using
    history_discrete_probability G (p k) (hp0 k) (hp1 k) Δ hΔ hN (μ k) k hk

end GraphicalAllocation.Universal
