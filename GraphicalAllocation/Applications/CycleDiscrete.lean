import GraphicalAllocation.Applications.CycleSetup
import GraphicalAllocation.Diffusion.Tail
import GraphicalAllocation.Transport.DiscreteLaw

/-!
# Exact-count cycle lower bound (Theorem 1.2)

All transport and diffusion inputs below are theorems of the actual allocation
kernel. Initial profiles have an arbitrary PMF, without a moment assumption.
-/

noncomputable section
namespace GraphicalAllocation.Applications
open Rules Process Transport Geometry Diffusion MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The exact-count constant-radius transport estimate on an actual cycle. -/
theorem discrete_cycle_transport (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k H R : ℕ) (hH : H ≤ k + 1)
    (hR : 8 ≤ R) (hnR : (R : ℝ) ≤ (n + 3 : ℝ) / 512)
    (hHR : (H : ℝ) ≤ (n + 3 : ℝ) * R ^ 2 / (64 * Real.pi ^ 2))
    (M : ℝ) (hM : 1 ≤ M)
    (htail : (A.kernel.eventLawFrom μ k).toMeasure
      {x | M - 1 < gap x} ≤ (1 / 8 : ℝ≥0∞)) :
    (H : ℝ) / (8 * (n + 3 : ℝ) * (2 * R + 1)) ≤ M ^ 2 := by
  have hn : (0 : ℝ) < n + 3 := by positivity
  have hR' : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by linarith
  have hp : allocationBadGapFrom A μ.toMeasure k M ≤ 1 / 8 := by
    rw [allocationBadGapFrom_eq_probability, measureReal_def]
    simpa using ENNReal.toReal_mono (by norm_num : (1 / 8 : ℝ≥0∞) ≠ ⊤) htail
  have hvolcap : 2 * (R : ℝ) + 1 ≤ (n + 3 : ℝ) ^ 2 / (32 * (n + 3) * (2 : ℝ) ^ 2) := by
    have hc := (discrete_radius_parameters hR' hnR).2.1
    convert hc using 1
    field_simp
    ring
  have hq : ∀ h < H, ∀ x, allocationTagTail A h x (cycleMetric n) R ≤ 1 / 16 := by
    intro h hh x
    have hh' : (h : ℝ) ≤ (n + 3 : ℝ) * R ^ 2 / (64 * Real.pi ^ 2) :=
      (by exact_mod_cast (Nat.le_of_lt hh) : (h : ℝ) ≤ H).trans hHR
    exact (allocation_cycle_tail_events n A hA x h hRpos).trans
      (discrete_tail_parameter hn hR' hh')
  have htransport := discrete_transport_volume_from A μ.toMeasure
    (cycleMetric n) (cycleMetric_diag n) (cycleMetric_symm n) (cycleMetric_triangle n)
    (cycleHalfShift n) hM (Δ := 2)
    (fun v => by rw [cycle_allocation_degree n A hA]; norm_num) k H hH
    (fun _ => R) (fun _ => 2 * R + 1) (fun _ => 1 / 16)
    (fun _ _ => hRpos) (fun _ _ => by positivity)
    (fun _ _ => cycle_discrete_separation n R (by simpa using hnR))
    (fun _ _ => cycleMetric_ball_card n R) hq
  have hsummand : ∀ h ∈ Finset.range H,
      1 / (8 * (n + 3 : ℝ) * (2 * R + 1)) ≤
        max (max (1 - allocationBadGapFrom A μ.toMeasure k M - 2 * (1 / 16)) 0 ^ 2 /
          ((n + 3 : ℝ) * (2 * R + 1)) - 4 * (2 : ℝ) ^ 2 / (n + 3 : ℝ) ^ 2) 0 := by
    intro h hh
    exact discrete_summand_lower hn hn (by positivity) (by norm_num) hp (by norm_num) hvolcap
  have hs := Finset.sum_le_sum hsummand
  have hs' : (H : ℝ) / (8 * (n + 3 : ℝ) * (2 * R + 1)) ≤
      ∑ h ∈ Finset.range H,
        max (max (1 - allocationBadGapFrom A μ.toMeasure k M - 2 * (1 / 16)) 0 ^ 2 /
          ((n + 3 : ℝ) * (2 * R + 1)) - 4 * (2 : ℝ) ^ 2 / (n + 3 : ℝ) ^ 2) 0 := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] using hs
  exact hs'.trans (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using htransport)

/-- The discrete quantile bound at the paper's floor-selected comparison radius. -/
theorem discrete_cycle_quantile (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k : ℕ)
    (hR : 8 ≤ ⌊min ((n + 3 : ℝ) / 512) (Real.sqrt ((k : ℝ) / (n + 3)))⌋₊)
    (M : ℝ) (hM : 1 ≤ M)
    (htail : (A.kernel.eventLawFrom μ k).toMeasure
      {x | M - 1 < gap x} ≤ (1 / 8 : ℝ≥0∞)) :
    cycleScale (n + 3) ((k : ℝ) / (n + 3)) / (1024 * Real.pi * Real.sqrt 3) ≤ M := by
  let R := ⌊min ((n + 3 : ℝ) / 512) (Real.sqrt ((k : ℝ) / (n + 3)))⌋₊
  let H := ⌊(n + 3 : ℝ) * (R : ℝ) ^ 2 / (64 * Real.pi ^ 2)⌋₊
  change 8 ≤ R at hR
  have hn : (0 : ℝ) < n + 3 := by positivity
  have hparam := discrete_floor_parameters (t := (k : ℝ) / (n + 3)) hn.le R rfl
  have htime := discrete_horizon_parameters hn hR hparam.1 hparam.2.1
  have hHfloor : (H : ℝ) ≤ (n + 3 : ℝ) * (R : ℝ) ^ 2 / (64 * Real.pi ^ 2) :=
    Nat.floor_le (by positivity)
  have hHk : H ≤ k := htime.2.1
  have htransport := discrete_cycle_transport n A hA μ k H R (hHk.trans (Nat.le_succ k)) hR hparam.1 hHfloor M hM htail
  exact discrete_quantile_arithmetic hn (Nat.cast_le.mpr hR) (by linarith)
    (le_min hn.le (Real.sqrt_nonneg _)) (hparam.2.2.1 hR) htime.2.2 htransport

/-- Theorem 1.2, with its exact constant and both conclusions for every initial law. -/
theorem discrete_cycle_lower_bound (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal (discreteCycleConstant * cycleScale (n + 3) ((k : ℝ) / (n + 3))) ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.eventLawFrom μ k).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.eventLawFrom μ k).toMeasure
        {x | discreteCycleConstant * cycleScale (n + 3) ((k : ℝ) / (n + 3)) ≤ gap x} := by
  let R := ⌊min ((n + 3 : ℝ) / 512) (Real.sqrt ((k : ℝ) / (n + 3)))⌋₊
  have hphase := cycle_discrete_phase n A hA μ k hk
  by_cases hR : 8 ≤ R
  · rw [discrete_scale_identity]
    exact transport_to_gap _ gap (measurable_of_countable _) gap_nonneg hphase _
      (discrete_cycle_quantile n A hA μ k hR)
  · have hsmall := (discrete_floor_parameters (t := (k : ℝ) / (n + 3))
      (show (0 : ℝ) ≤ n + 3 by positivity) R rfl).2.2.2 (by omega)
    exact small_gap_target _ gap (measurable_of_countable _) gap_nonneg hphase
      (discrete_small_scale (by positivity) hsmall)


/-- The literal exponent form of the introductory exact-count theorem. -/
theorem discrete_cycle_lower_bound_paper (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k : ℕ) (hk : 1 ≤ k) :
    let a := (1 / (16384 * Real.pi * Real.sqrt 3)) *
      min (Real.sqrt (n + 3)) (((k : ℝ) / (n + 3)) ^ (1 / 4 : ℝ))
    ENNReal.ofReal a ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.eventLawFrom μ k).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.eventLawFrom μ k).toMeasure {x | a ≤ gap x} := by
  simpa only [discreteCycleConstant, cycleScale_eq_min (n + 3) ((k : ℝ) / (n + 3)) (by positivity)] using
    discrete_cycle_lower_bound n A hA μ k hk

/-- Saturation at a deterministic event count of at least the cube of cycle size. -/
theorem discrete_cycle_lower_bound_saturated (n : ℕ)
    (A : AllocationRule (Fin (n + 3)) (Fin (n + 3)))
    (hA : A.toOrientedGraph = cycleOrientation n)
    (μ : PMF (Profile (Fin (n + 3)))) (k : ℕ) (hk : (n + 3) ^ 3 ≤ k) :
    ENNReal.ofReal (discreteCycleConstant * Real.sqrt (n + 3)) ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂(A.kernel.eventLawFrom μ k).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ (A.kernel.eventLawFrom μ k).toMeasure
        {x | discreteCycleConstant * Real.sqrt (n + 3) ≤ gap x} := by
  have hk' : (n + 3 : ℝ) ^ 3 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn : 1 ≤ k := (one_le_pow₀ (by omega : 1 ≤ n + 3)).trans hk
  simpa only [discrete_cycleScale_saturated (by positivity : (0 : ℝ) < n + 3) hk'] using
    discrete_cycle_lower_bound n A hA μ k hkn

end GraphicalAllocation.Applications
