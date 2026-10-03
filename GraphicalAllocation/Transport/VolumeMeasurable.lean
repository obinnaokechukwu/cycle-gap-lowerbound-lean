import GraphicalAllocation.Transport.Weighted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Measurable finite balls and the corrected lag-dependent transport integral -/

noncomputable section
namespace GraphicalAllocation.Transport
open MeasureTheory
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [DecidableEq V] [Nonempty V] in
/-- Every finite closed-ball cardinality is a measurable function of its radius. -/
theorem measurable_card_closedBall (d : V → V → ℝ) (v : V) :
    Measurable (fun r : ℝ => (closedBall d r v).card) := by
  simp only [closedBall, Finset.card_filter]
  exact Finset.measurable_sum Finset.univ (fun w hw =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const)

omit [DecidableEq V] in
/-- The actual maximal ball volume is measurable; no regularity of the finite
distance table beyond its being fixed is required. -/
theorem measurable_ballVolume (d : V → V → ℝ) : Measurable (ballVolume d) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset V)) Finset.univ_nonempty
    (fun v hv => measurable_card_closedBall d v)
  convert h using 1
  funext r
  simp only [ballVolume, Finset.sup'_apply]

/-- Any bounded measurable real function is integrable on a finite interval. -/
theorem intervalIntegrable_of_measurable_bound {f : ℝ → ℝ} (hf : Measurable f)
    {T C : ℝ} (hT : 0 ≤ T) (hbound : ∀ s ∈ Set.Icc 0 T, |f s| ≤ C) :
    IntervalIntegrable f volume 0 T := by
  have hi : IntegrableOn f (Set.Icc 0 T) volume := IntegrableOn.of_bound
    (isCompact_Icc.measure_lt_top) hf.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simpa only [Real.norm_eq_abs] using hbound s hs)
  apply IntegrableOn.intervalIntegrable
  simpa only [Set.uIcc_of_le hT] using hi

omit [DecidableEq V] in
/-- Positive radii make inverse maximal volume measurable and at most one. -/
theorem intervalIntegrable_inverse_ballVolume (d : V → V → ℝ) (hdiag : ∀ v, d v v = 0)
    (R : ℝ → ℝ) (hRm : Measurable R) {T : ℝ} (hT : 0 ≤ T)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s) :
    IntervalIntegrable (fun s => 1 / (ballVolume d (R s) : ℝ)) volume 0 T := by
  have hv : Measurable (fun s => (ballVolume d (R s) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp ((measurable_ballVolume d).comp hRm)
  apply intervalIntegrable_of_measurable_bound (C := 1) (measurable_const.div hv) hT
  intro s hs
  change |1 / (ballVolume d (R s) : ℝ)| ≤ 1
  have hn := ballVolume_pos d hdiag (hR s hs).le
  have hp : (0 : ℝ) < ballVolume d (R s) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ ballVolume d (R s) := by exact_mod_cast hn
  rw [abs_of_nonneg (div_nonneg (by norm_num) hp.le)]
  exact (div_le_one hp).mpr h1

omit [DecidableEq V] in
/-- The corrected general transport integrand is measurable and bounded even
when the radius and tail envelope vary at every lag. -/
theorem intervalIntegrable_transport_ballVolume (d : V → V → ℝ) (hdiag : ∀ v, d v v = 0)
    (R q : ℝ → ℝ) (hRm : Measurable R) (hqm : Measurable q)
    {p T : ℝ} (hp : 0 ≤ p) (hT : 0 ≤ T)
    (hR : ∀ s ∈ Set.Icc 0 T, 0 < R s) (hq : ∀ s ∈ Set.Icc 0 T, 0 ≤ q s) :
    IntervalIntegrable (fun s => max (1 - p - 2 * q s) 0 ^ 2 /
      (ballVolume d (R s) : ℝ)) volume 0 T := by
  have hv : Measurable (fun s => (ballVolume d (R s) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp ((measurable_ballVolume d).comp hRm)
  have hn : Measurable (fun s => max (1 - p - 2 * q s) 0 ^ 2) :=
    ((measurable_const.sub (measurable_const.mul hqm)).max measurable_const).pow_const 2
  apply intervalIntegrable_of_measurable_bound (C := 1) (hn.div hv) hT
  intro s hs
  change |max (1 - p - 2 * q s) 0 ^ 2 / (ballVolume d (R s) : ℝ)| ≤ 1
  have hV := ballVolume_pos d hdiag (hR s hs).le
  have hVp : (0 : ℝ) < ballVolume d (R s) := by exact_mod_cast hV
  have hV1 : (1 : ℝ) ≤ ballVolume d (R s) := by exact_mod_cast hV
  have hnum0 : 0 ≤ max (1 - p - 2 * q s) 0 := le_max_right _ _
  have hnum1 : max (1 - p - 2 * q s) 0 ≤ 1 := max_le (by linarith [hq s hs]) (by norm_num)
  have hsq : max (1 - p - 2 * q s) 0 ^ 2 ≤ 1 := by nlinarith
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hVp.le)]
  exact (div_le_one hVp).mpr (hsq.trans hV1)

end GraphicalAllocation.Transport
