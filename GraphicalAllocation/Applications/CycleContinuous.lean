import GraphicalAllocation.Applications.CycleSetup
import GraphicalAllocation.Process.Normalized.Law
import GraphicalAllocation.Diffusion.Tail
import GraphicalAllocation.Transport.ContinuousTransport
/-!
# Continuous cycle lower bounds (Theorem 1.1 and Lemma 6.1)

The quantile theorem instantiates actual-process continuous transport and sharp
cycle diffusion. Every permitted edge-dependent rule and initial PMF is covered.
Expected gap is an extended nonnegative integral, including infinite values.
-/

noncomputable section
namespace GraphicalAllocation.Applications
open Rules Process Transport Geometry MeasureTheory Diffusion
open scoped ENNReal NNReal
theorem cycle_quantile (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (time : ℝ≥0)
    (r : ℕ) (hr : 24 ≤ r) (hrn : r ≤ (n + 3) / 2)
    (ht : ((r / 3 : ℕ) : ℝ) ^ 2 / (64 * Real.pi ^ 2) ≤ time)
    (M : ℝ) (hM : 1 ≤ M)
    (htail : (A.kernel.continuousLawFrom μ (n + 3) time).toMeasure
      {x | M - 1 < gap x} ≤ (1 / 8 : ℝ≥0∞)) :
    Real.sqrt r / (64 * Real.pi) ≤ M := by
  let R := r / 3
  let T : ℝ≥0 := ⟨(R : ℝ) ^ 2 / (64 * Real.pi ^ 2), by positivity⟩
  have hpars := continuous_radius_parameters hr
  have hR : 8 ≤ R := hpars.1
  have hRreal : (8 : ℝ) ≤ R := Nat.cast_le.mpr hR
  have hRpos : (0 : ℝ) < R := by linarith
  have hsep := cycle_continuous_separation n r hrn
  have hvolume := cycleMetric_ball_card n R
  have hq : ∀ s : ℝ≥0, s ≤ T → ∀ x,
      continuousTagTail A s x (cycleMetric n) R ≤ 1 / 16 := by
    intro s hs x
    have he := allocation_cycle_tail_physical n A hA x s hRpos
    have he' : continuousTagTail A s x (cycleMetric n) R ≤
        (2 * Real.pi ^ 2 * s + 2) / (R : ℝ) ^ 2 := by
      unfold continuousTagTail cycleMetric
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using he
    exact he'.trans (continuous_tail_parameter hRreal hs)
  have hp : continuousBadGapFrom A μ.toMeasure time M ≤ 1 / 8 := by
    rw [continuousBadGapFrom_eq_probability, measureReal_def]
    simpa using ENNReal.toReal_mono (by norm_num : (1 / 8 : ℝ≥0∞) ≠ ⊤) htail
  have hconstant := continuous_transport_volume_constant A μ.toMeasure
    (cycleMetric n) (cycleMetric_diag n) (cycleMetric_symm n) (cycleMetric_triangle n)
    (cycleHalfShift n) hM hRpos (by positivity : (0 : ℝ) < 2 * R + 1)
    time T.property ht hsep hvolume (fun s hs x =>
      (hq (Real.toNNReal s) (Real.toNNReal_le_iff_le_coe.mpr hs.2) x).trans
        (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8)) hp
  have htransport : (R : ℝ) ^ 2 / (64 * Real.pi ^ 2) / (4 * (2 * R + 1)) ≤ M ^ 2 := by
    have hn : (0 : ℝ) < n + 3 := by positivity
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hconstant
    convert hconstant using 1
    dsimp [T]
    field_simp
  apply continuous_quantile_arithmetic (Nat.cast_nonneg r) hRreal _ _ (by linarith) htransport
  · exact_mod_cast hpars.2.1
  · exact_mod_cast hpars.2.2.1


/-- Theorem 1.1 for the actual continuous-time process. -/
theorem cycle_lower_bound (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (time : ℝ≥0)
    (ht : 1 / (n + 3 : ℝ) ≤ time) :
    ENNReal.ofReal (cycleConstant * cycleScale (n + 3) time) ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.continuousLawFrom μ (n + 3) time).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (n + 3) time).toMeasure
        {x | cycleConstant * cycleScale (n + 3) time ≤ gap x} := by
  let r := ⌊min ((n + 3 : ℝ) / 2) (Real.sqrt time)⌋₊
  have hn : (0 : ℝ) ≤ n + 3 := by positivity
  have hphase := A.continuous_phase_third μ (n + 3) time (by positivity) (by simpa using ht)
  have hparam := continuous_floor_parameters (t := (time : ℝ)) hn r rfl
  by_cases hr : 24 ≤ r
  · have hrn : r ≤ (n + 3) / 2 := by
      have hh : (2 : ℝ) * r ≤ (n + 3 : ℕ) := by simpa using (show 2 * (r : ℝ) ≤ n + 3 by linarith [hparam.1])
      have hh' : 2 * r ≤ n + 3 := by exact_mod_cast hh
      omega
    have htime := continuous_time_parameter time.property hparam.2.1 (Nat.div_le_self r 3)
    have hquantile := transport_to_gap (A.kernel.continuousLawFrom μ (n + 3) time).toMeasure
      gap (measurable_of_countable _) gap_nonneg hphase (Real.sqrt r / (64 * Real.pi))
      (cycle_quantile n A hA μ time r hr hrn htime)
    exact gap_target_mono _ gap (continuous_scale_comparison hn (hparam.2.2.1 hr)) hquantile
  · exact small_gap_target _ gap (measurable_of_countable _) gap_nonneg hphase
      (continuous_small_scale hn (hparam.2.2.2 (by omega)))

/-- The literal exponent form of Theorem 1.1. -/
theorem cycle_lower_bound_paper (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (time : ℝ≥0)
    (ht : 1 / (n + 3 : ℝ) ≤ time) :
    let a := (1 / (1024 * Real.pi * Real.sqrt 3)) *
      min (Real.sqrt (n + 3)) ((time : ℝ) ^ (1 / 4 : ℝ))
    ENNReal.ofReal a ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.continuousLawFrom μ (n + 3) time).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (n + 3) time).toMeasure {x | a ≤ gap x} := by
  simpa only [cycleConstant, cycleScale_eq_min (n + 3) time time.property] using
    cycle_lower_bound n A hA μ time ht

/-- The continuous-time lower bound saturates once time reaches the square of cycle size. -/
theorem cycle_lower_bound_saturated (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (time : ℝ≥0)
    (ht : (n + 3 : ℝ) ^ 2 ≤ time) :
    ENNReal.ofReal (cycleConstant * Real.sqrt (n + 3)) ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.continuousLawFrom μ (n + 3) time).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ (n + 3) time).toMeasure
        {x | cycleConstant * Real.sqrt (n + 3) ≤ gap x} := by
  have hn : (1 : ℝ) ≤ n + 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htime : 1 / (n + 3 : ℝ) ≤ time := by
    have hi : 1 / (n + 3 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hn
    nlinarith
  simpa only [cycleScale_saturated (by positivity : (0 : ℝ) ≤ n + 3) ht] using
    cycle_lower_bound n A hA μ time htime


/-- The stationary normalized-cycle conclusion, for every invariant law. -/
theorem cycle_invariant_lower_bound (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (anchor : Fin (n + 3)) (π : PMF (NormalizedProfile anchor))
    (hπ : A.InvariantNormalizedLaw anchor π) :
    ENNReal.ofReal (cycleConstant * Real.sqrt (n + 3)) ≤
      ∫⁻ x, ENNReal.ofReal (gap x.val) ∂π.toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ π.toMeasure
        {x | cycleConstant * Real.sqrt (n + 3) ≤ gap x.val} := by
  let t : ℝ≥0 := (n + 3) ^ 2
  have ht : (n + 3 : ℝ) ^ 2 ≤ t := by simp [t]
  have h := cycle_lower_bound_saturated n A hA (π.map Subtype.val) t ht
  apply A.invariant_gap_lower_bound anchor π hπ t _ _ _
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using h.1
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using h.2

end GraphicalAllocation.Applications
