import GraphicalAllocation.Smoothed.Law

/-!
# Arbitrary fixed polynomial horizons in physical time

For a requested physical horizon `t ≤ N^a`, with `a ≥ 0`, choose the
smoothed rule once with event exponent `ζ = 2a + 4`.  A simple regular
graph has `m ≤ N²/2` edges, so the actual rate-one-per-edge Poisson mean
is at most `N^(a+2)/2`. The proved second-moment truncation then costs at
most one beyond the event-count estimate.  The event law, continuous
law, and Green radius below are the constructed mathematical objects;
no conditional-law identification or Green estimate is assumed.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators NNReal ENNReal
open Process Rules Transport Spectral MeasureTheory

/-- The total event-rate mean over a polynomial physical horizon. -/
lemma polynomial_poisson_mean_le {N m t a : ℝ} (hN : 3 ≤ N) (_hm : 0 ≤ m)
    (hmN : m ≤ N^2 / 2) (ht : 0 ≤ t) (htN : t ≤ N^a) :
    m * t ≤ N^(a + 2) / 2 := by
  have hN₀ : 0 < N := by linarith
  calc
    m * t ≤ (N^2 / 2) * N^a := by gcongr
    _ = N^(a + 2) / 2 := by rw [Real.rpow_add hN₀, Real.rpow_two]; ring

/-- The second-moment remainder is uniformly at most one. -/
lemma polynomial_poisson_remainder_le_one {N m t a : ℝ} (hN : 3 ≤ N) (hm : 0 ≤ m)
    (hmN : m ≤ N^2 / 2) (ht : 0 ≤ t) (ha : 0 ≤ a) (htN : t ≤ N^a) :
    ((m * t)^2 + m * t) / N^(2 * a + 4) ≤ 1 := by
  have hN₀ : 0 < N := by linarith
  have hμ := polynomial_poisson_mean_le hN hm hmN ht htN
  have hμ₀ : 0 ≤ m * t := mul_nonneg hm ht
  have hP : 1 ≤ N^(a + 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hden : N^(2 * a + 4) = (N^(a + 2))^2 := by
    rw [show 2 * a + 4 = (a + 2) * 2 by ring, Real.rpow_mul hN₀.le, Real.rpow_two]
  rw [hden]
  apply (div_le_iff₀ (by positivity : 0 < (N^(a + 2))^2)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hμ)
      (by positivity : 0 ≤ N^(a + 2) / 2 + m * t),
    mul_nonneg (by positivity : 0 ≤ N^(a + 2)) (by linarith : 0 ≤ N^(a + 2) - 1)]

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]

omit [DecidableEq V] [Nonempty G.edgeSet] in
/-- The simple-graph edge estimate used in the physical-time exponent choice. -/
lemma regular_edge_card_le_half_square {d : ℕ} (hd : G.IsRegularOfDegree d) :
    (Fintype.card G.edgeSet : ℝ) ≤ (Fintype.card V : ℝ)^2 / 2 := by
  have hcount := graph_regular_degree_sum G hd
  obtain ⟨v⟩ := ‹Nonempty V›
  have hdN : (d : ℝ) ≤ Fintype.card V := by
    have hv := G.degree_lt_card_verts v
    rw [hd.degree_eq] at hv
    exact_mod_cast hv.le
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card V)) (sub_nonneg.mpr hdN)]

/-- The actual physical-time allocation expectation, for every fixed polynomial
horizon, with a single cutoff selected by `ζ = 2a + 4`. -/
theorem smoothed_physical_polynomial_expectation_le
    [MeasurableSpace (Profile V)] [MeasurableSingletonClass (Profile V)]
    {d : ℕ} (hd : G.IsRegularOfDegree d) (hG : G.Connected)
    (hN : 3 ≤ Fintype.card V) {a : ℝ} (ha : 0 ≤ a)
    (time : ℝ≥0) (htime : (time : ℝ) ≤ (Fintype.card V : ℝ)^a) (b : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((polynomialRule G d (2 * a + 4) hN (by linarith)).kernel.continuousLaw
        (Fintype.card G.edgeSet) time (fun _ => b)).toMeasure) ≤
      ENNReal.ofReal (2 * beta (2 * a + 4) * Real.log (Fintype.card V) *
        (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3) + 3) := by
  let ζ : ℝ := 2 * a + 4
  have hζ : 1 ≤ ζ := by dsimp [ζ]; linarith
  let N : ℝ := Fintype.card V
  let B : ℝ := 2 * beta ζ * Real.log N *
    (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3) + 2
  have hNr : 3 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hB : 0 ≤ B := by
    have hl := log_ge_one hNr
    have hb := beta_ge_four hζ
    dsimp [B]
    positivity
  have hH : 0 < N^ζ := Real.rpow_pos_of_pos (by linarith) _
  have hsmall (k : ℕ) (hk : (k : ℝ) ≤ N^ζ) :
      (polynomialRule G d ζ hN hζ).kernel.iterate k gap (fun _ => b) ≤ B :=
    smoothed_polynomial_iterate_gap_le G hd hG hN hζ k hk b
  have hall (k : ℕ) : (polynomialRule G d ζ hN hζ).kernel.iterate k gap (fun _ => b) ≤ k :=
    smoothed_iterate_gap_le_count G _ k b
  have hp := (polynomialRule G d ζ hN hζ).kernel.poisson_upper_of_event_bound
    (Fintype.card G.edgeSet) time (fun _ => b) gap gap_nonneg hB hH hsmall hall
  have herr : (((Fintype.card G.edgeSet : ℝ≥0) * time : ℝ≥0)^2 +
      ((Fintype.card G.edgeSet : ℝ≥0) * time : ℝ≥0)) / (N^ζ : ℝ) ≤ 1 := by
    push_cast
    exact polynomial_poisson_remainder_le_one hNr (Nat.cast_nonneg _)
      (regular_edge_card_le_half_square G hd) time.coe_nonneg ha htime
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  dsimp [B, ζ, N] at *
  linarith

end GraphicalAllocation.Smoothed
