import GraphicalAllocation.Smoothed.UpperBound
import GraphicalAllocation.Smoothed.Constants
import GraphicalAllocation.Process.FiniteIntegrability
import GraphicalAllocation.Process.PoissonUpper

/-! # The paper's smoothed-rule theorem under the actual allocation laws -/

noncomputable section
namespace GraphicalAllocation.Smoothed
open scoped BigOperators NNReal ENNReal
open Process Rules Transport Spectral MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The fixed rule chosen for a specified polynomial event horizon. -/
def polynomialRule (d : ℕ) (ζ : ℝ) (hN : 3 ≤ Fintype.card V) (hζ : 1 ≤ ζ) :
    AllocationRule V G.edgeSet :=
  graphRule G (cutoff (Fintype.card V) d ζ)
    (cutoff_pos (by exact_mod_cast hN) (Nat.cast_nonneg _) hζ)

variable [Nonempty V] [Nonempty G.edgeSet]

/-- Flat-start growth can never exceed the number of allocations. -/
theorem smoothed_iterate_gap_le_count {θ : ℝ} (hθ : 0 < θ) (k : ℕ) (a : ℤ) :
    (graphRule G θ hθ).kernel.iterate k gap (fun _ => a) ≤ k := by
  rw [FiniteKernel.iterate_eq_pathSum]
  calc
    _ ≤ ∑ p, (graphRule G θ hθ).kernel.pathWeight k (fun _ => a) p * (k : ℝ) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
        (allocation_path_gap_le G hθ k a p) ((graphRule G θ hθ).kernel.pathWeight_nonneg _ _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteKernel.pathWeight_total, one_mul]

/-- Equation (8.2) at every exact event count, including the trivial count zero. -/
theorem smoothed_polynomial_iterate_gap_le {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (polynomialRule G d ζ hN hζ).kernel.iterate k gap (fun _ => a) ≤
      2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3) + 2 := by
  let N : ℝ := Fintype.card V
  let m : ℝ := Fintype.card G.edgeSet
  let s : ℝ := beta ζ * Real.log N
  let θ : ℝ := cutoff N d ζ
  let R : ℝ := s * (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3)
  have hNr : 3 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hcount : N * d = 2 * m := graph_regular_degree_sum G hd
  have hdpos : 0 < d := by
    by_contra hn
    have hd₀ : d = 0 := Nat.eq_zero_of_not_pos hn
    rw [hd₀] at hcount
    norm_num at hcount
    linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hθ : 0 < θ := cutoff_pos hNr hdr.le hζ
  have hs : 0 < s := scale_pos hNr hζ
  have hstep : stepSize G (θ := θ) * (2 * (d : ℝ)) ≤ 1 :=
    stepsize_bound hNr hdr hm hcount hζ
  have hradius : 0 < greenRadius G hG := by
    have hl := one_third_le_degree_radius G hG d hdr
      (fun v => by rw [hd.degree_eq]) hN
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos hdr.le (le_of_not_gt h)
    linarith
  have hθeq : θ = (4 * d + 3) * s := by dsimp [θ, s, cutoff]; ring
  have hedge : Real.sqrt (4 * (d : ℝ) * θ * s) + (4 / 3 : ℝ) * s ≤ θ := by
    rw [hθeq]
    have he : 4 * (d : ℝ) * ((4 * d + 3) * s) * s =
        2 * (2 * d * ((4 * d + 3) * s)) * s := by ring
    rw [he]
    exact edge_bernstein_threshold_le hdr.le hs.le
  have hvertex : Real.sqrt (4 * (d : ℝ) * θ * greenRadius G hG * s) + (4 / 3 : ℝ) * s = R := by
    have he : 4 * (d : ℝ) * θ * greenRadius G hG * s =
        2 * (2 * d * ((4 * d + 3) * s) * greenRadius G hG) * s := by rw [hθeq]; ring
    rw [he]
    exact vertex_bernstein_threshold hs.le
  have hdN : (d : ℝ) ≤ N := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv := G.degree_lt_card_verts v
    rw [hd.degree_eq] at hv
    dsimp [N]
    exact_mod_cast hv.le
  have hmN : m ≤ N^2 / 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ N) (sub_nonneg.mpr hdN)]
  have herr : (k : ℝ) * (2 * (k : ℝ) * m + 2 * N) * Real.exp (-s) ≤ 2 := by
    rw [show Real.exp (-s) = N ^ (-beta ζ) from exp_neg_scale (by linarith : 0 < N)]
    exact exceptional_expectation_le_two hNr hm.le hmN (Nat.cast_nonneg _) hζ hk
  have h := smoothed_iterate_gap_le G hθ hd hG hdpos hstep hradius k a hs hedge hvertex.le
  change (graphRule G θ hθ).kernel.iterate k gap (fun _ => a) ≤ _
  change (graphRule G θ hθ).kernel.iterate k gap (fun _ => a) ≤
    2 * R + (k : ℝ) * (2 * (k : ℝ) * m + 2 * N) * Real.exp (-s) at h
  have hh := h.trans (add_le_add (le_refl (2 * R)) herr)
  convert hh using 1
  dsimp [R, s, N]
  ring

/-- Ordinary expected gap is well-defined at each finite horizon and satisfies (8.2). -/
theorem smoothed_polynomial_integral_gap_le [MeasurableSpace (Profile V)]
    [MeasurableSingletonClass (Profile V)] {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫ x, gap x ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3) + 2 := by
  rw [FiniteKernel.integral_eventLaw_unbounded]
  exact smoothed_polynomial_iterate_gap_le G hd hG hN hζ k hk a

/-- The same upper bound in the paper's extended nonnegative expectation convention. -/
theorem smoothed_polynomial_expectation_le [MeasurableSpace (Profile V)]
    [MeasurableSingletonClass (Profile V)] {d : ℕ} (hd : G.IsRegularOfDegree d)
    (hG : G.Connected) (hN : 3 ≤ Fintype.card V) {ζ : ℝ} (hζ : 1 ≤ ζ)
    (k : ℕ) (hk : (k : ℝ) ≤ (Fintype.card V : ℝ) ^ ζ) (a : ℤ) :
    (∫⁻ x, ENNReal.ofReal (gap x) ∂((polynomialRule G d ζ hN hζ).kernel.eventLaw k (fun _ => a)).toMeasure) ≤
      ENNReal.ofReal (2 * beta ζ * Real.log (Fintype.card V) *
        (2 * Real.sqrt ((d : ℝ) * (4 * d + 3) * greenRadius G hG) + 4 / 3) + 2) := by
  rw [FiniteKernel.lintegral_eventLaw_ofReal _ _ _ _ gap_nonneg]
  exact ENNReal.ofReal_le_ofReal (smoothed_polynomial_iterate_gap_le G hd hG hN hζ k hk a)

end GraphicalAllocation.Smoothed
