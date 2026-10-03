import GraphicalAllocation.Gaussian.Field
import GraphicalAllocation.Gaussian.AbsoluteMoment

/-! # The finite Gaussian range and its coordinate lower bounds -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GraphicalAllocation.Gaussian

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Maximum coordinate minus minimum coordinate of a finite Euclidean vector. -/
def coordinateRange (x : EuclideanSpace ℝ V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun v ↦ x v) -
  Finset.univ.inf' Finset.univ_nonempty (fun v ↦ x v)

theorem coordinateRange_nonneg (x : EuclideanSpace ℝ V) : 0 ≤ coordinateRange x := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact sub_nonneg.mpr ((Finset.inf'_le _ (Finset.mem_univ v)).trans
    (Finset.le_sup' _ (Finset.mem_univ v)))

theorem continuous_coordinateRange : Continuous (coordinateRange (V := V)) := by
  apply Continuous.sub
  · exact Continuous.finset_sup'_apply _ (fun _ _ ↦ by fun_prop)
  · exact Continuous.finset_inf'_apply _ (fun _ _ ↦ by fun_prop)

theorem coordinateRange_le_norm (x : EuclideanSpace ℝ V) :
    coordinateRange x ≤ 2 * ‖x‖ := by
  have hs : Finset.univ.sup' Finset.univ_nonempty (fun v ↦ x v) ≤ ‖x‖ := by
    apply Finset.sup'_le
    intro v _
    exact (le_abs_self _).trans (PiLp.norm_apply_le x v)
  have hi : -‖x‖ ≤ Finset.univ.inf' Finset.univ_nonempty (fun v ↦ x v) := by
    apply Finset.le_inf'
    intro v _
    have h := PiLp.norm_apply_le x v
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  dsimp [coordinateRange]
  linarith

/-- A vector summing to zero has range at least each absolute coordinate. -/
theorem abs_coord_le_range (x : EuclideanSpace ℝ V) (hx : ∑ v, x v = 0) (v : V) :
    |x v| ≤ coordinateRange x := by
  let mx := Finset.univ.sup' Finset.univ_nonempty (fun v ↦ x v)
  let mn := Finset.univ.inf' Finset.univ_nonempty (fun v ↦ x v)
  have hvmax : x v ≤ mx := Finset.le_sup' _ (Finset.mem_univ v)
  have hvmin : mn ≤ x v := Finset.inf'_le _ (Finset.mem_univ v)
  have hmx : 0 ≤ mx := by
    by_contra hh
    have hs : ∑ v, x v < 0 := Finset.sum_neg
      (fun i _ ↦ (Finset.le_sup' _ (Finset.mem_univ i)).trans_lt (lt_of_not_ge hh))
      Finset.univ_nonempty
    linarith
  have hmn : mn ≤ 0 := by
    by_contra hh
    have hs : 0 < ∑ v, x v := Finset.sum_pos
      (fun i _ ↦ (lt_of_not_ge hh).trans_le (Finset.inf'_le _ (Finset.mem_univ i)))
      Finset.univ_nonempty
    linarith
  change |x v| ≤ mx - mn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

theorem freeField_integrable_range (d : ℝ) :
    Integrable (coordinateRange (V := V)) (freeField G hG d) := by
  apply (IsGaussian.integrable_fun_id.norm.const_mul 2).mono'
    continuous_coordinateRange.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (coordinateRange_nonneg x)]
    exact coordinateRange_le_norm x

/-- The expected range is a finite real integral, not an extended expectation. -/
def expectedRange (d : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ V, coordinateRange x ∂freeField G hG d

theorem expectedRange_nonneg (d : ℝ) : 0 ≤ expectedRange G hG d :=
  integral_nonneg coordinateRange_nonneg

theorem integral_abs_coord_le_expectedRange {d : ℝ} (hd : 0 ≤ d) (v : V) :
    ∫ x : EuclideanSpace ℝ V, |x v| ∂freeField G hG d ≤ expectedRange G hG d := by
  apply integral_mono_ae (freeField_integrable_coord G hG d v).abs
    (freeField_integrable_range G hG d)
  filter_upwards [freeField_sum_zero G hG hd] with x hx
  exact abs_coord_le_range x hx v

omit [Nonempty V] in
/-- The absolute first moment of each actual Gaussian coordinate. -/
theorem freeField_integral_abs_coord {d : ℝ} (hd : 0 ≤ d) (v : V) :
    ∫ x : EuclideanSpace ℝ V, |x v| ∂freeField G hG d =
      Real.sqrt (2 / Real.pi) * Real.sqrt (d * Spectral.greenDiagonal G hG v) := by
  have hm := freeField_coordinate_law G hG hd v
  have h := integral_abs_gaussianReal_zero
    (d * Spectral.greenDiagonal G hG v).toNNReal
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by fun_prop)] at h
  simpa only [Real.coe_toNNReal _ (mul_nonneg hd
    (Spectral.greenDiagonal_nonneg G hG v))] using h

theorem coordinate_stdDev_le_expectedRange {d : ℝ} (hd : 0 ≤ d) (v : V) :
    Real.sqrt (2 / Real.pi) * Real.sqrt (d * Spectral.greenDiagonal G hG v) ≤
      expectedRange G hG d := by
  rw [← freeField_integral_abs_coord G hG hd v]
  exact integral_abs_coord_le_expectedRange G hG hd v

/-- The largest coordinate standard deviation, using actual Gaussian variances. -/
def maxCoordinateStdDev (d : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun v ↦ Real.sqrt (d * Spectral.greenDiagonal G hG v))

theorem maxCoordinateStdDev_eq_radius {d : ℝ} (hd : 0 ≤ d) :
    maxCoordinateStdDev G hG d = Real.sqrt (d * Spectral.greenRadius G hG) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun v _ ↦ Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (Spectral.greenDiagonal_le_radius G hG v) hd))
  · obtain ⟨v, hv⟩ := Spectral.exists_greenDiagonal_eq_radius G hG
    rw [← hv]
    exact Finset.le_sup' (fun w ↦ Real.sqrt (d * Spectral.greenDiagonal G hG w))
      (Finset.mem_univ v)

/-- The first inequality stated in the Gaussian-free-field remark. -/
theorem max_stdDev_le_expectedRange {d : ℝ} (hd : 0 ≤ d) :
    Real.sqrt (2 / Real.pi) * maxCoordinateStdDev G hG d ≤ expectedRange G hG d := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun v ↦ Real.sqrt (d * Spectral.greenDiagonal G hG v))
  change Real.sqrt (2 / Real.pi) *
    Finset.univ.sup' Finset.univ_nonempty _ ≤ _
  rw [hv]
  exact coordinate_stdDev_le_expectedRange G hG hd v

/-- The range lower comparison with the actual maximum Green diagonal. -/
theorem sqrt_radius_le_expectedRange {d : ℝ} (hd : 0 ≤ d) :
    Real.sqrt (2 / Real.pi) * Real.sqrt (d * Spectral.greenRadius G hG) ≤
      expectedRange G hG d := by
  rw [← maxCoordinateStdDev_eq_radius G hG hd]
  exact max_stdDev_le_expectedRange G hG hd

/-- A graph-size independent positive lower bound for the Gaussian range scale. -/
theorem expectedRange_uniform_lower {d : ℝ} (hd : 0 < d)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ d) (hN : 3 ≤ Fintype.card V) :
    Real.sqrt (2 / Real.pi) * Real.sqrt (1 / 3 : ℝ) ≤ expectedRange G hG d := by
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (Spectral.one_third_le_degree_radius G hG d hd hdeg hN)) (by positivity)).trans
      (sqrt_radius_le_expectedRange G hG hd.le)

theorem expectedRange_pos {d : ℝ} (hd : 0 < d)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ d) (hN : 3 ≤ Fintype.card V) :
    0 < expectedRange G hG d :=
  lt_of_lt_of_le (by positivity) (expectedRange_uniform_lower G hG hd hdeg hN)

end GraphicalAllocation.Gaussian
