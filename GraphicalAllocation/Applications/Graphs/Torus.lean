import GraphicalAllocation.Applications.Graphs.TorusTransport
import GraphicalAllocation.Process.Normalized.Law

/-! # Rectangular two-dimensional tori: actual-law Theorem 7.3

All geometric, Hilbert-diffusion, Poissonization, transport, and radius-integral
inputs have been proved for the actual model. The logarithm is obtained using
one fixed family of clipped terminal tests across all response lags.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

/-- The rectangular-torus lower bound with c₂=1/(1280π√42), arbitrary initial
law, and the exact physical-time regime t≥L². The parameters n,k represent
L=n+3 and K=k+3, thereby covering every 3≤K≤L. -/
theorem torus_lower_bound (n k : ℕ) (hkn : k ≤ n)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3)))
    (μ : PMF (Profile (Fin (n + 3) × Fin (k + 3)))) (t : ℝ≥0) (ht : (n + 3 : ℝ) ^ 2 ≤ t) :
    let a := torusConstant * Real.sqrt ((n + 3 : ℝ) / (k + 3) + Real.log (k + 3))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x)
      ∂(A.kernel.continuousLawFrom μ
        (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure ∧
    (1 / 8 : ℝ≥0∞) ≤ (A.kernel.continuousLawFrom μ
      (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure
      {x | a ≤ gap x} := by
  dsimp only
  have hK : (3 : ℝ) ≤ k + 3 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hKL : (k + 3 : ℝ) ≤ n + 3 := by exact_mod_cast Nat.add_le_add_right hkn 3
  have hZ0 := torus_scale_nonneg (by linarith : (1:ℝ) ≤ k + 3) hKL
  have hphase := A.continuous_phase_third μ
    (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t
    (by exact_mod_cast Fintype.card_pos (α := (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet))
    (cylinder_phase_time (cycleGraph (k + 3)) n t ht)
  by_cases hsmall : (n + 3 : ℝ) / (k + 3) + Real.log (k + 3) ≤ 32 * (1 + torusKappa)
  · exact small_gap_target _ gap (measurable_of_countable gap) gap_nonneg hphase
      (torus_small_scale hZ0 hsmall)
  · have hlargeZ : 32 * (1 + torusKappa) ≤
        (n + 3 : ℝ) / (k + 3) + Real.log (k + 3) := le_of_not_ge hsmall
    have hlargeL : 16 * torusKappa ≤ n + 3 := by
      by_contra hL
      exact hsmall (torus_short_side_scale hK hKL (lt_of_not_ge hL))
    let I : ℝ := 2 * ∫ s in (0:ℝ)..torusHorizon torusKappa (n + 3),
      1 / torusVolume (k + 3) torusKappa s
    have hIlower : ((n + 3 : ℝ) / (k + 3) + Real.log (k + 3)) /
        (200 * torusKappa ^ 2) ≤ I := by
      exact (torus_affine_large hlargeZ).trans
        (torus_volume_integral_lower (by linarith) hKL one_le_torusKappa hlargeL)
    have hI0 : 0 ≤ I := (by positivity : 0 ≤
      ((n + 3 : ℝ) / (k + 3) + Real.log (k + 3)) / (200 * torusKappa ^ 2)).trans hIlower
    have hmain := transport_to_gap
      (A.kernel.continuousLawFrom μ
        (Fintype.card (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet) t).toMeasure
      gap (measurable_of_countable gap) gap_nonneg hphase (Real.sqrt I / 2) (by
        intro M hM hp
        have htr := torus_transport_bound n k A hA μ t ht hlargeL M hM hp
        change I / 4 ≤ M ^ 2 at htr
        apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
        apply (Real.sqrt_le_iff).mpr
        constructor <;> nlinarith)
    have hcompare := torus_scale_comparison hZ0 hIlower
    apply gap_target_mono _ gap hcompare
    simpa only [div_div, show (2:ℝ) * 16 = 32 by norm_num] using hmain

/-- The rectangular-torus bound under every invariant normalized law. -/
theorem torus_invariant_lower_bound (n k : ℕ) (hkn : k ≤ n)
    (A : AllocationRule (Fin (n + 3) × Fin (k + 3))
      (cycleGraph (n + 3) □ cycleGraph (k + 3)).edgeSet)
    (hA : A.toOrientedGraph = canonicalOrientation (cycleGraph (n + 3) □ cycleGraph (k + 3)))
    (anchor : Fin (n + 3) × Fin (k + 3)) (π : PMF (NormalizedProfile anchor))
    (hπ : A.InvariantNormalizedLaw anchor π) :
    let a := torusConstant * Real.sqrt ((n + 3 : ℝ) / (k + 3) + Real.log (k + 3))
    ENNReal.ofReal a ≤ ∫⁻ x, ENNReal.ofReal (gap x.val) ∂π.toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ π.toMeasure {x | a ≤ gap x.val} := by
  let t : ℝ≥0 := ⟨(n + 3 : ℝ) ^ 2, sq_nonneg _⟩
  have h := torus_lower_bound n k hkn A hA (π.map Subtype.val) t le_rfl
  exact A.invariant_gap_lower_bound anchor π hπ t _ _ _ h.1 h.2

end GraphicalAllocation.Applications.Graphs
