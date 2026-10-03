import GraphicalAllocation.Smoothed.PhysicalHorizon
import GraphicalAllocation.Spectral.TorusRadius

/-!
# Polynomial-horizon smoothed allocation on the actual square torus

For `L = n + 3` the graph is literally `C_L □ C_L`, has degree four and
`L²` vertices, and its Green radius is the proved graph-inverse radius.
The explicit coefficient `128 * beta ζ` witnesses the stated
`O_ζ((log L)^(3/2))` upper bound for a cutoff fixed for the event horizon
`k ≤ (L²)^ζ`.  The product `log L * sqrt (log L)` is also identified with
its real-power notation.
-/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators NNReal ENNReal
open Process Rules Transport Spectral MeasureTheory SimpleGraph
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

lemma torus_vertex_card (n : ℕ) : Fintype.card (TorusVertex n) = (n + 3)^2 := by
  simp [TorusVertex, pow_two]

lemma torus_vertex_card_ge_three (n : ℕ) : 3 ≤ Fintype.card (TorusVertex n) := by
  rw [torus_vertex_card, pow_two]
  have h : 3 ≤ n + 3 := by omega
  exact h.trans (Nat.le_mul_self _)

lemma torus_regular (n : ℕ) : (torusGraph n).IsRegularOfDegree 4 := by
  intro v
  change (cycleGraph (n + 3) □ cycleGraph (n + 3)).degree v = 4
  rw [degree_boxProd, cycleGraph_degree_three_le, cycleGraph_degree_three_le]

lemma torus_edge_card (n : ℕ) : Fintype.card (torusGraph n).edgeSet = 2 * (n + 3)^2 := by
  have h := graph_regular_degree_sum (torusGraph n)
    (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.ncard_neighborSet] using torus_regular n)
  rw [torus_vertex_card] at h
  have he : (Fintype.card (torusGraph n).edgeSet : ℝ) = 2 * ((n : ℝ) + 3)^2 := by
    push_cast at h
    linarith
  exact_mod_cast he

instance torus_edges_nonempty (n : ℕ) : Nonempty (torusGraph n).edgeSet := by
  apply Fintype.card_pos_iff.mp
  rw [torus_edge_card]
  positivity

/-- The actual square-torus rule, fixed once the polynomial exponent is chosen. -/
def torusPolynomialRule (n : ℕ) (ζ : ℝ) (hζ : 1 ≤ ζ) :
    AllocationRule (TorusVertex n) (torusGraph n).edgeSet :=
  polynomialRule (torusGraph n) 4 ζ (torus_vertex_card_ge_three n) hζ

/-- The torus specialization uses the concrete cutoff `38 beta(ζ) log L`. -/
lemma torus_cutoff_eq (n : ℕ) (ζ : ℝ) :
    cutoff (Fintype.card (TorusVertex n)) 4 ζ = 38 * beta ζ * Real.log (n + 3) := by
  rw [torus_vertex_card]
  push_cast
  rw [cutoff, Real.log_pow]
  ring

/-- Numerical absorption of the Green estimate with an explicit uniform coefficient. -/
lemma torus_bound_le {L R ζ : ℝ} (hL : 3 ≤ L) (hζ : 1 ≤ ζ)
    (hR : R ≤ 1 + Real.log L) :
    2 * beta ζ * Real.log (L^2) * (2 * Real.sqrt (4 * (4 * 4 + 3) * R) + 4 / 3) + 2 ≤
      128 * beta ζ * Real.log L * Real.sqrt (Real.log L) := by
  have hl : 1 ≤ Real.log L := log_ge_one hL
  have hb := beta_ge_four hζ
  have hr : 1 ≤ Real.sqrt (Real.log L) := Real.one_le_sqrt.mpr hl
  have hs : 4 ≤ beta ζ * Real.log L := by nlinarith [mul_nonneg (by linarith : 0 ≤ beta ζ - 4) (by linarith : 0 ≤ Real.log L - 1)]
  have hroot : Real.sqrt (4 * (4 * 4 + 3) * R) ≤ 13 * Real.sqrt (Real.log L) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log L)
      nlinarith
  calc
    _ = 4 * (beta ζ * Real.log L) *
        (2 * Real.sqrt (4 * (4 * 4 + 3) * R) + 4 / 3) + 2 := by
      rw [Real.log_pow]
      ring
    _ ≤ 4 * (beta ζ * Real.log L) *
        (26 * Real.sqrt (Real.log L) + 4 / 3) + 2 := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add _ le_rfl
        calc
          _ ≤ 2 * (13 * Real.sqrt (Real.log L)) :=
            mul_le_mul_of_nonneg_left hroot (by norm_num)
          _ = _ := by ring
      · positivity
    _ ≤ _ := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ beta ζ * Real.log L)
        (by linarith : 0 ≤ Real.sqrt (Real.log L) - 1)]

/-- Exact event counts satisfy the square-torus logarithmic-power upper bound. -/
theorem torus_polynomial_iterate_gap_le (n : ℕ) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ ((n + 3 : ℝ)^2)^ζ) (a : ℤ) :
    (torusPolynomialRule n ζ hζ).kernel.iterate k gap (fun _ => a) ≤
      128 * beta ζ * Real.log (n + 3) * Real.sqrt (Real.log (n + 3)) := by
  have hk' : (k : ℝ) ≤ (Fintype.card (TorusVertex n) : ℝ)^ζ := by
    simpa only [torus_vertex_card, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using hk
  have h := smoothed_polynomial_iterate_gap_le (torusGraph n)
    (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.ncard_neighborSet] using torus_regular n)
    (torus_connected n) (torus_vertex_card_ge_three n) hζ k hk' a
  apply h.trans
  simp only [torus_vertex_card, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  exact torus_bound_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hζ
    (torus_greenRadius_le_one_add_log n)

/-- Ordinary expected gap under the constructed square-torus event law. -/
theorem torus_polynomial_integral_gap_le (n : ℕ)
    [MeasurableSpace (Profile (TorusVertex n))] [MeasurableSingletonClass (Profile (TorusVertex n))]
    {ζ : ℝ} (hζ : 1 ≤ ζ) (k : ℕ) (hk : (k : ℝ) ≤ ((n + 3 : ℝ)^2)^ζ) (a : ℤ) :
    (∫ x, gap x ∂((torusPolynomialRule n ζ hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      128 * beta ζ * Real.log (n + 3) * Real.sqrt (Real.log (n + 3)) := by
  rw [FiniteKernel.integral_eventLaw_unbounded]
  exact torus_polynomial_iterate_gap_le n hζ k hk a

/-- Extended nonnegative expected gap under the constructed square-torus event law. -/
theorem torus_polynomial_expectation_le (n : ℕ)
    [MeasurableSpace (Profile (TorusVertex n))] [MeasurableSingletonClass (Profile (TorusVertex n))]
    {ζ : ℝ} (hζ : 1 ≤ ζ) (k : ℕ) (hk : (k : ℝ) ≤ ((n + 3 : ℝ)^2)^ζ) (a : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x) ∂((torusPolynomialRule n ζ hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      ENNReal.ofReal (128 * beta ζ * Real.log (n + 3) * Real.sqrt (Real.log (n + 3))) := by
  rw [FiniteKernel.lintegral_eventLaw_ofReal _ _ _ _ gap_nonneg]
  exact ENNReal.ofReal_le_ofReal (torus_polynomial_iterate_gap_le n hζ k hk a)


/-- The same concrete square-torus rule works through any prescribed fixed
polynomial physical horizon. Its exponent is chosen once as `2a + 4`. -/
theorem torus_physical_polynomial_expectation_le (n : ℕ)
    [MeasurableSpace (Profile (TorusVertex n))] [MeasurableSingletonClass (Profile (TorusVertex n))]
    {a : ℝ} (ha : 0 ≤ a) (time : ℝ≥0)
    (htime : (time : ℝ) ≤ ((n + 3 : ℝ)^2)^a) (b : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((torusPolynomialRule n (2 * a + 4) (by linarith)).kernel.continuousLaw
        (Fintype.card (torusGraph n).edgeSet) time (fun _ => b)).toMeasure) ≤
      ENNReal.ofReal (128 * beta (2 * a + 4) * Real.log (n + 3) *
        Real.sqrt (Real.log (n + 3)) + 1) := by
  have ht : (time : ℝ) ≤ (Fintype.card (TorusVertex n) : ℝ)^a := by
    simpa only [torus_vertex_card, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using htime
  have h := smoothed_physical_polynomial_expectation_le (torusGraph n)
    (by simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.ncard_neighborSet] using torus_regular n)
    (torus_connected n) (torus_vertex_card_ge_three n) ha time ht b
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [torus_vertex_card, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  have hb := torus_bound_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (3 : ℝ) ≤ n + 3)
    (by linarith : (1 : ℝ) ≤ 2 * a + 4) (torus_greenRadius_le_one_add_log n)
  linarith

/-- The elementary expression is exactly the conventional exponent `3/2`. -/
lemma log_mul_sqrt_log_eq_rpow {L : ℝ} (hL : 3 ≤ L) :
    Real.log L * Real.sqrt (Real.log L) = (Real.log L)^(3 / 2 : ℝ) := by
  have hl : 0 < Real.log L := lt_of_lt_of_le (by norm_num) (log_ge_one hL)
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hl, Real.rpow_one]


/-- R29 in conventional real-power notation, with the explicit coefficient
`128 beta(ζ)` independent of the side length and event count. -/
theorem torus_polynomial_expectation_rpow_le (n : ℕ)
    [MeasurableSpace (Profile (TorusVertex n))] [MeasurableSingletonClass (Profile (TorusVertex n))]
    {ζ : ℝ} (hζ : 1 ≤ ζ) (k : ℕ) (hk : (k : ℝ) ≤ ((n + 3 : ℝ)^2)^ζ) (a : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((torusPolynomialRule n ζ hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      ENNReal.ofReal (128 * beta ζ * (Real.log (n + 3))^(3 / 2 : ℝ)) := by
  rw [← log_mul_sqrt_log_eq_rpow (by have := Nat.cast_nonneg (α := ℝ) n; linarith)]
  simpa only [mul_assoc] using torus_polynomial_expectation_le n hζ k hk a

/-- R31 on the square torus, with the additive Poisson remainder absorbed.
The coefficient depends only on the prescribed physical-horizon exponent. -/
theorem torus_physical_polynomial_expectation_rpow_le (n : ℕ)
    [MeasurableSpace (Profile (TorusVertex n))] [MeasurableSingletonClass (Profile (TorusVertex n))]
    {a : ℝ} (ha : 0 ≤ a) (time : ℝ≥0)
    (htime : (time : ℝ) ≤ ((n + 3 : ℝ)^2)^a) (b : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x)
      ∂((torusPolynomialRule n (2 * a + 4) (by linarith)).kernel.continuousLaw
        (Fintype.card (torusGraph n).edgeSet) time (fun _ => b)).toMeasure) ≤
      ENNReal.ofReal ((128 * beta (2 * a + 4) + 1) *
        (Real.log (n + 3))^(3 / 2 : ℝ)) := by
  apply (torus_physical_polynomial_expectation_le n ha time htime b).trans
  apply ENNReal.ofReal_le_ofReal
  have hL : (3 : ℝ) ≤ n + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hl := log_ge_one hL
  have hr := Real.one_le_sqrt.mpr hl
  have hq : 1 ≤ Real.log (n + 3) * Real.sqrt (Real.log (n + 3)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)]
  rw [← log_mul_sqrt_log_eq_rpow hL]
  calc
    _ ≤ 128 * beta (2 * a + 4) * Real.log (n + 3) * Real.sqrt (Real.log (n + 3)) +
        Real.log (n + 3) * Real.sqrt (Real.log (n + 3)) := add_le_add le_rfl hq
    _ = _ := by ring

end GraphicalAllocation.Smoothed
