import GraphicalAllocation.Applications.Graphs.Torus
import GraphicalAllocation.Universal.Original

/-!
# Combined aspect-ratio and universal logarithmic torus bound

Corollary 7.9 combines the already proved actual-law transport bound with the
strategy-independent logarithmic bound, retaining the advertised constant
`c₃=c₂/2`, arbitrary initial laws, and extended expectations.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace GraphicalAllocation.Applications.Graphs

open Rules Process Transport Geometry MeasureTheory SimpleGraph Universal
open scoped ENNReal NNReal

/-- The combined lower-bound constant in the revised paper. -/
def torusCombinedConstant : ℝ := torusConstant / 2

lemma torusConstant_le_one_three_thousand : torusConstant ≤ 1 / 3000 := by
  have hs : 1 ≤ Real.sqrt 42 := by norm_num
  have hp := Real.pi_gt_three
  unfold torusConstant
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1280 * Real.pi * Real.sqrt 42)
    (by norm_num : (0 : ℝ) < 3000)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]


lemma combined_small_scale {L K : ℝ} (hK : 3 ≤ K) (hKL : K ≤ L) (hN : L * K < 1000) :
    torusCombinedConstant * (Real.sqrt (L / K) + Real.log (L * K)) ≤ 1 / 3 := by
  have hL : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hKp : 0 < K := by linarith
  have hNp : 0 < L * K := by positivity
  have hratio : L / K ≤ L * K :=
    (div_le_self hL (by linarith)).trans (by nlinarith)
  have hs : Real.sqrt (L / K) ≤ 1000 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have hl : Real.log (L * K) ≤ 1000 := (Real.log_le_sub_one_of_pos hNp).trans (by linarith)
  have hc := torusConstant_le_one_three_thousand
  have hc0 := torusConstant_pos
  unfold torusCombinedConstant
  nlinarith

/-- Combining two lower thresholds requires only choosing the larger one;
no independence or simultaneous-occurrence claim is used. -/
lemma combine_torus_scales {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (s l : ℝ) (hl : 0 < l)
    (hs : ENNReal.ofReal (torusConstant * s) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ)
    (hsp : (1 / 8 : ℝ≥0∞) ≤ μ {x | torusConstant * s ≤ g x})
    (hlp : (7 / 16 : ℝ≥0∞) ≤ μ {x | l / 64 ≤ g x}) :
    ENNReal.ofReal (torusCombinedConstant * (s + l)) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ ∧
      (1 / 8 : ℝ≥0∞) ≤ μ {x | torusCombinedConstant * (s + l) ≤ g x} := by
  have hc := torusConstant_le_one_three_thousand
  have hc1 : torusConstant * l ≤ l / 64 := by nlinarith
  have hc2 : torusConstant * l ≤ 7 * l / 1024 := by nlinarith
  have hle : ENNReal.ofReal (7 * l / 1024) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    have h := quantile_le_extended_expectation μ g hg hg0
      (a := l / 64) (c := 7 / 16) (by positivity) (by norm_num) (by
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16), ENNReal.ofReal_ofNat] using hlp)
    convert h using 1
    congr 1
    ring
  constructor
  · by_cases hb : torusConstant * s ≤ 7 * l / 1024
    · apply (ENNReal.ofReal_le_ofReal (show torusCombinedConstant * (s + l) ≤ 7 * l / 1024 by
        unfold torusCombinedConstant
        nlinarith)).trans hle
    · apply (ENNReal.ofReal_le_ofReal (show torusCombinedConstant * (s + l) ≤ torusConstant * s by
        unfold torusCombinedConstant
        linarith)).trans hs
  · by_cases hb : torusConstant * s ≤ l / 64
    · apply (show (1 / 8 : ℝ≥0∞) ≤ 7 / 16 by
        have h := ENNReal.ofReal_le_ofReal (show (1 / 8 : ℝ) ≤ 7 / 16 by norm_num)
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h).trans (hlp.trans (measure_mono ?_))
      intro x hx
      change l / 64 ≤ g x at hx
      change torusCombinedConstant * (s + l) ≤ g x
      unfold torusCombinedConstant
      nlinarith
    · apply hsp.trans (measure_mono ?_)
      intro x hx
      change torusConstant * s ≤ g x at hx
      change torusCombinedConstant * (s + l) ≤ g x
      unfold torusCombinedConstant
      linarith

/-- Corollary 7.9, with the actual process law and exactly `c₃=c₂/2`. -/
theorem torus_combined_lower_bound (n k : ℕ) (hkn : k ≤ n)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3)))
    (μ : PMF (Profile (Fin (n + 3) × Fin (k + 3)))) (t : ℝ≥0) (ht : (n + 3 : ℝ) ^ 2 ≤ t) :
    let a := torusCombinedConstant *
      (Real.sqrt ((n + 3 : ℝ) / (k + 3)) + Real.log ((n + 3 : ℝ) * (k + 3)))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom μ
        (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ
      (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure
      {x | a ≤ gap x} := by
  dsimp only
  have hK : (3 : ℝ) ≤ k + 3 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hKL : (k + 3 : ℝ) ≤ n + 3 := by exact_mod_cast Nat.add_le_add_right hkn 3
  have hNpos : (0 : ℝ) < (n + 3 : ℝ) * (k + 3) := by positivity
  have hcard : (Fintype.card (Fin (n + 3) × Fin (k + 3)) : ℝ) =
      (n + 3 : ℝ) * (k + 3) := by simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; rfl
  by_cases hlarge : (1000 : ℝ) ≤ (n + 3 : ℝ) * (k + 3)
  · have htime : Real.log (Fintype.card (Fin (n + 3) × Fin (k + 3))) / (4 * (4 : ℝ)) ≤ t := by
      rw [hcard]
      have hNle : (n + 3 : ℝ) * (k + 3) ≤ (n + 3 : ℝ) ^ 2 := by nlinarith
      have hl := Real.log_le_sub_one_of_pos hNpos
      nlinarith [Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ (n + 3 : ℝ) * (k + 3))]
    have hlog := allocation_continuous_probability (cycleGraph (n + 3) □ cycleGraph (k + 3)) A hA 4 (fun v => by
        simpa only [← SimpleGraph.ncard_neighborSet] using torus_degree n k v)
      (by simpa only [hcard] using hlarge)
      (degree_four_size.trans (by simpa only [hcard] using hlarge)) μ t htime
    rw [hcard] at hlog
    have htr := torus_lower_bound n k hkn A hA μ t ht
    have htr' := gap_target_mono _ gap (show torusConstant * Real.sqrt ((n + 3 : ℝ) / (k + 3)) ≤
        torusConstant * Real.sqrt ((n + 3 : ℝ) / (k + 3) + Real.log (k + 3)) by
      apply mul_le_mul_of_nonneg_left _ torusConstant_pos.le
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (Real.log_nonneg (by linarith)))) htr
    exact combine_torus_scales _ gap (measurable_of_countable gap) gap_nonneg
      _ _ (by have := log_ge_one hlarge; linarith) htr'.1 htr'.2 hlog
  · have hphase := A.continuous_phase_third μ
      (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t
      (by exact_mod_cast Fintype.card_pos (α := (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet))
      (cylinder_phase_time (cycleGraph (k + 3)) n t ht)
    exact small_gap_target _ gap (measurable_of_countable gap) gap_nonneg hphase
      (combined_small_scale hK hKL (lt_of_not_ge hlarge))

/-- The combined bound also holds under every invariant normalized law. -/
theorem torus_combined_invariant_lower_bound (n k : ℕ) (hkn : k ≤ n)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3)))
    (anchor : Fin (n + 3) × Fin (k + 3)) (π : PMF (NormalizedProfile anchor))
    (hπ : A.InvariantNormalizedLaw anchor π) :
    let a := torusCombinedConstant *
      (Real.sqrt ((n + 3 : ℝ) / (k + 3)) + Real.log ((n + 3 : ℝ) * (k + 3)))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x.val) ∂π.toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ π.toMeasure {x | a ≤ gap x.val} := by
  let t : ℝ≥0 := ⟨(n + 3 : ℝ) ^ 2, sq_nonneg _⟩
  have h := torus_combined_lower_bound n k hkn A hA (π.map Subtype.val) t le_rfl
  exact A.invariant_gap_lower_bound anchor π hπ t _ _ _ h.1 h.2

end GraphicalAllocation.Applications.Graphs
