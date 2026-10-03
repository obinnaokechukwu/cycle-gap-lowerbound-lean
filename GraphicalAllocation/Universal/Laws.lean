import GraphicalAllocation.Universal.Strategy
import GraphicalAllocation.Probability.PoissonMoments

/-!
# Arbitrary initial laws and the physical-time bridge

Every law is constructed from the actual finite transitions. Initial states
are sampled before future independent edges. The Poisson bridge also permits
a different history strategy conditional on each event count, so conditioning
on a clock schedule does not impose a time-homogeneity restriction.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped BigOperators NNReal ENNReal
open Process Rules Transport MeasureTheory ProbabilityTheory

variable {State Choice Index : Type*} [Fintype Choice]

/-- Exact indicator bridge, valid even without a measurable structure on memory. -/
theorem eventLaw_outerProbability (K : FiniteKernel State Choice)
    (P : State → Prop) (k : ℕ) (x : State) :
    (K.eventLaw k x).toOuterMeasure {y | P y} =
      ENNReal.ofReal (K.iterate k (fun y => if P y then 1 else 0) x) := by
  induction k generalizing x with
  | zero =>
    simp only [FiniteKernel.eventLaw_zero, PMF.toOuterMeasure_pure_apply, FiniteKernel.iterate_zero, Set.mem_ofPred_eq]
    split_ifs <;> simp
  | succ k ih =>
    rw [K.eventLaw_succ, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    simp only [ih, FiniteKernel.choiceLaw_apply, FiniteKernel.iterate_succ, FiniteKernel.step]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro c _
      rw [ENNReal.ofReal_mul (K.nonneg x c)]
    · intro c _
      exact mul_nonneg (K.nonneg x c)
        (K.iterate_nonneg k (fun _ => by split_ifs <;> norm_num) _)

/-- A lower event probability remains valid after any independent initial mixture. -/
theorem bind_outerProbability_lower (μ : PMF Index) (f : Index → PMF State)
    (P : Set State) (c : ℝ≥0∞) (hc : ∀ i, c ≤ (f i).toOuterMeasure P) :
    c ≤ (μ.bind f).toOuterMeasure P := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    c = ∑' i, μ i * c := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (hc i) zero_le)

/-- Restricting a mixture to a set of indices retains the mass of that set. -/
theorem bind_outerProbability_on (μ : PMF Index) (f : Index → PMF State)
    (P : Set State) (B : Set Index) (c : ℝ≥0∞)
    (hc : ∀ i ∈ B, c ≤ (f i).toOuterMeasure P) :
    μ.toOuterMeasure B * c ≤ (μ.bind f).toOuterMeasure P := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : i ∈ B
  · simp only [Set.indicator_of_mem hi]
    exact mul_le_mul_of_nonneg_left (hc i hi) zero_le
  · simp [hi]

/-- A Poisson event count supplies the exact `7/16` physical-time constant. -/
theorem poisson_mixture_lower (r : ℝ≥0) (hr : 32 ≤ (r : ℝ)) (h : ℕ)
    (hh : (h : ℝ) ≤ r / 2) (f : ℕ → PMF State) (P : Set State)
    (hf : ∀ k, h ≤ k → (1 / 2 : ℝ≥0∞) ≤ (f k).toOuterMeasure P) :
    (7 / 16 : ℝ≥0∞) ≤ ((poissonMeasure r).toPMF.bind f).toOuterMeasure P := by
  have hp := GraphicalAllocation.Probability.poisson_half_mean_probability hr
  have hpe : (7 / 8 : ℝ≥0∞) ≤ (poissonMeasure r).toPMF.toOuterMeasure
      {k : ℕ | (r : ℝ) / 2 ≤ k} := by
    have hp' := ENNReal.ofReal_le_ofReal hp
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat, ← PMF.toMeasure_apply_eq_toOuterMeasure,
      Measure.toPMF_toMeasure] using hp'
  have hb := bind_outerProbability_on (poissonMeasure r).toPMF f P
    {k : ℕ | (r : ℝ) / 2 ≤ k} (1 / 2) (fun k hk => hf k (by
      have hk' : (h : ℝ) ≤ k := hh.trans hk
      exact_mod_cast hk'))
  calc
    (7 / 16 : ℝ≥0∞) = (7 / 8) * (1 / 2) := by
      have he := ENNReal.ofReal_mul (show (0 : ℝ) ≤ 7 / 8 by norm_num) (q := (1 / 2 : ℝ))
      norm_num only [show (7 / 8 : ℝ) * (1 / 2) = 7 / 16 by norm_num] at he
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using he
    _ ≤ _ := (mul_le_mul_of_nonneg_right hpe zero_le).trans hb

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]

omit [DecidableEq V] in
/-- The stated physical-time regime makes the mean at least two windows and 32. -/
theorem poisson_window_size (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V) (t : ℝ≥0)
    (ht : Real.log (Fintype.card V) / (4 * Δ) ≤ t) :
    32 ≤ ((Fintype.card G.edgeSet : ℝ≥0) * t : ℝ≥0) ∧
    (logWindow (Fintype.card V) : ℝ) ≤ ((Fintype.card G.edgeSet : ℝ≥0) * t : ℝ≥0) / 2 := by
  have hm : (0 : ℝ) < Fintype.card G.edgeSet := by exact_mod_cast Fintype.card_pos
  have hhand : (Fintype.card V : ℝ) * Δ = 2 * Fintype.card G.edgeSet := by
    exact_mod_cast regular_edge_count G Δ hΔ
  have hΔpos : (0 : ℝ) < Δ := by
    have hΔ0 := Nat.cast_nonneg (α := ℝ) Δ
    by_contra hn
    have hz : (Δ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) hΔ0
    rw [hz] at hhand
    nlinarith
  have ht' := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Δ)).mp ht
  have hprod : (Fintype.card V : ℝ) / 8 * Real.log (Fintype.card V) ≤
      (Fintype.card G.edgeSet : ℝ) * t := by
    have hmul := mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
    nlinarith
  have hlog := log_ge_one hN
  have hfloor : (logWindow (Fintype.card V) : ℝ) ≤
      (Fintype.card V : ℝ) / 16 * Real.log (Fintype.card V) :=
    Nat.floor_le (by positivity)
  norm_cast at hprod ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (Fintype.card V))]

namespace EndpointStrategy

variable {G} (S : EndpointStrategy G State)

/-- Proposition 7.8 after exactly `k` arrivals, for every initial memory law. -/
theorem discrete_probability (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (μ : PMF State) (k : ℕ) (hk : logWindow (Fintype.card V) ≤ k) :
    (1 / 2 : ℝ≥0∞) ≤ (S.kernel.eventLawFrom μ k).toOuterMeasure
      {y | Real.log (Fintype.card V) / 64 ≤ gap (S.load y)} := by
  apply bind_outerProbability_lower
  intro x
  rw [eventLaw_outerProbability]
  simpa using ENNReal.ofReal_le_ofReal (S.iterate_lower_bound Δ hΔ hN hsize k hk x)

/-- Proposition 7.8 in physical time, with every edge ringing at rate one. -/
theorem continuous_probability (Δ : ℕ) (hΔ : ∀ v, G.degree v = Δ)
    (hN : (1000 : ℝ) ≤ Fintype.card V)
    (hsize : (9 * ((Δ : ℝ) + 1)) ^ (4 / 3 : ℝ) ≤ Fintype.card V)
    (μ : PMF State) (t : ℝ≥0)
    (ht : Real.log (Fintype.card V) / (4 * Δ) ≤ t) :
    (7 / 16 : ℝ≥0∞) ≤
      (S.kernel.continuousLawFrom μ (Fintype.card G.edgeSet) t).toOuterMeasure
        {y | Real.log (Fintype.card V) / 64 ≤ gap (S.load y)} := by
  have htcount := poisson_window_size G Δ hΔ hN t ht
  have heq : S.kernel.continuousLawFrom μ (Fintype.card G.edgeSet) t =
      (poissonMeasure ((Fintype.card G.edgeSet : ℝ≥0) * t)).toPMF.bind
        (fun k => S.kernel.eventLawFrom μ k) := by
    exact PMF.bind_comm μ _ _
  rw [heq]
  exact poisson_mixture_lower _ htcount.1 _ htcount.2 _ _
    (fun k hk => S.discrete_probability Δ hΔ hN hsize μ k hk)

end EndpointStrategy
end GraphicalAllocation.Universal
