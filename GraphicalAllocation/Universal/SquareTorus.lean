import GraphicalAllocation.Universal.History
import GraphicalAllocation.Applications.Graphs.Model

/-!
# Arbitrary-strategy square-torus consequence

The lower comparison in `rem:smoothed-gff` uses only the universal strategy
bound. Writing `L=n+3` retains the canonical cycle and edge instances while
covering every integer `L≥32` exactly.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace GraphicalAllocation.Universal

open Process Rules Transport Geometry SimpleGraph
open scoped NNReal ENNReal

/-- For every `L≥32`, every adapted randomized history policy has gap at least
`log L / 32` with probability at least one half after each
`k ≥ (L²/8) log L`. No endpoint-local or monotonicity hypothesis is present. -/
theorem square_torus_history_lower_bound (n : ℕ) (hL : 32 ≤ n + 3)
    (p : HistoryState (cycleGraph (n + 3) □ cycleGraph (n + 3)) →
      (cycleGraph (n + 3) □ cycleGraph (n + 3)).edgeSet → ℝ)
    (hp0 : ∀ x e, 0 ≤ p x e) (hp1 : ∀ x e, p x e ≤ 1)
    (μ : PMF (Profile (Fin (n + 3) × Fin (n + 3)))) (k : ℕ)
    (hk : (n + 3 : ℝ) ^ 2 / 8 * Real.log (n + 3) ≤ k) :
    (1 / 2 : ℝ≥0∞) ≤
      (historyEventLaw (cycleGraph (n + 3) □ cycleGraph (n + 3)) p hp0 hp1 μ k).toMeasure
        {x | Real.log (n + 3) / 32 ≤ gap x} := by
  have hLr : (32 : ℝ) ≤ n + 3 := by exact_mod_cast hL
  have hcard : (Fintype.card (Fin (n + 3) × Fin (n + 3)) : ℝ) = (n + 3 : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hlog : Real.log ((n + 3 : ℝ) ^ 2) = 2 * Real.log (n + 3) := by
    rw [Real.log_pow]
    norm_num
  have hN : (1000 : ℝ) ≤ Fintype.card (Fin (n + 3) × Fin (n + 3)) := by
    rw [hcard]
    nlinarith
  have hwindow : logWindow (Fintype.card (Fin (n + 3) × Fin (n + 3))) ≤ k := by
    apply Nat.floor_le_of_le
    rw [hcard, hlog]
    convert hk using 1
    ring
  have h := history_discrete_probability
    (cycleGraph (n + 3) □ cycleGraph (n + 3)) p hp0 hp1 4
    (fun v => by simpa only [← SimpleGraph.ncard_neighborSet] using torus_degree n n v)
    (max_le hN (degree_four_size.trans hN)) μ k hwindow
  rw [hcard, hlog] at h
  have hscale : 2 * Real.log (n + 3 : ℝ) / 64 = Real.log (n + 3 : ℝ) / 32 := by ring
  simpa only [hscale] using h

end GraphicalAllocation.Universal
