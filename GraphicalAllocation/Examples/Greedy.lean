import GraphicalAllocation.Applications.CycleDiscrete

/-! # Concrete nonvacuous examples: greedy and deterministic endpoint rules -/

noncomputable section
namespace GraphicalAllocation.Examples
open Process Geometry Applications Rules Transport
open scoped ENNReal

/-- The usual greedy probability, with uniform tie-breaking. -/
def greedyProbability (d : ℤ) : ℝ := if d < 0 then 1 else if d = 0 then 1 / 2 else 0

theorem greedyProbability_nonneg (d : ℤ) : 0 ≤ greedyProbability d := by
  unfold greedyProbability
  split_ifs <;> norm_num

theorem greedyProbability_le_one (d : ℤ) : greedyProbability d ≤ 1 := by
  unfold greedyProbability
  split_ifs <;> norm_num

theorem greedyProbability_antitone : Antitone greedyProbability := by
  intro a b hab
  unfold greedyProbability
  split_ifs <;> norm_num at * <;> omega

/-- Standard greedy allocation on the actual N=n+3 cycle. -/
def cycleGreedy (n : ℕ) : AllocationRule (Fin (n + 3)) (Fin (n + 3)) where
  toOrientedGraph := cycleOrientation n
  probability _ := greedyProbability
  probability_nonneg _ := greedyProbability_nonneg
  probability_le_one _ := greedyProbability_le_one
  probability_antitone _ := greedyProbability_antitone

/-- A constant-probability rule always sends each edge's ball to its head. -/
def cycleAlwaysHead (n : ℕ) : AllocationRule (Fin (n + 3)) (Fin (n + 3)) where
  toOrientedGraph := cycleOrientation n
  probability _ _ := 0
  probability_nonneg _ _ := le_rfl
  probability_le_one _ _ := zero_le_one
  probability_antitone _ := fun _ _ _ => le_rfl

/-- Example instantiation from a flat deterministic initial profile. -/
theorem greedy_cycle_from_flat (n k : ℕ) (hk : 1 ≤ k) :
    let μ := PMF.pure (fun _ : Fin (n + 3) => (0 : ℤ))
    let a := (1 / (16384 * Real.pi * Real.sqrt 3)) *
      min (Real.sqrt (n + 3)) (((k : ℝ) / (n + 3)) ^ (1 / 4 : ℝ))
    ENNReal.ofReal a ≤
      ∫⁻ x, ENNReal.ofReal (gap x) ∂((cycleGreedy n).kernel.eventLawFrom μ k).toMeasure ∧
      (1 / 8 : ℝ≥0∞) ≤ ((cycleGreedy n).kernel.eventLawFrom μ k).toMeasure {x | a ≤ gap x} :=
  discrete_cycle_lower_bound_paper n (cycleGreedy n) rfl _ k hk

end GraphicalAllocation.Examples
