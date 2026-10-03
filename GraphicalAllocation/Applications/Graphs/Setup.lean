import GraphicalAllocation.Geometry.Products
import GraphicalAllocation.Geometry.Oriented
import GraphicalAllocation.Applications.CycleSetup
import GraphicalAllocation.Applications.Graphs.CylinderConstants
import GraphicalAllocation.Applications.Graphs.Constants

/-! # Genuine graph-metric interfaces for the graph applications -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalAllocation.Applications.Graphs
open Rules Process Transport Geometry MeasureTheory SimpleGraph
open scoped ENNReal NNReal

lemma cylinder_ball_card {W : Type*} [Fintype W] [DecidableEq W]
    (n R : ℕ) (x : Fin (n + 3) × W) :
    ((closedBall (cylinderDistance n) R x).card : ℝ) ≤
      Fintype.card W * (2 * R + 1) := by
  have heq : closedBall (cylinderDistance n) R x = cylinderBall n x R := by
    ext y
    simp only [closedBall, cylinderBall, Finset.mem_filter, Finset.mem_univ, true_and,
      cylinderDistance]
    exact_mod_cast (Iff.rfl : (cycleGraph (n + 3)).dist x.1 y.1 ≤ R ↔ _)
  rw [heq]
  exact_mod_cast cylinderBall_card_le n x R

lemma cylinder_half_separated {W : Type*} (n R : ℕ) (hR : 2 * R ≤ (n + 3) / 2) :
    ∀ x : Fin (n + 3) × W, 2 * (R : ℝ) ≤ cylinderDistance n x (productHalfShift n W x) := by
  intro x
  rw [cylinderHalfShift_distance]
  exact_mod_cast hR

/-- Real-valued genuine graph distance on the rectangular torus. -/
def torusDistance (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) : ℝ :=
  (cycleGraph (n + 3) □ cycleGraph (k + 3)).dist x y

@[simp] lemma torusDistance_diag (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    torusDistance n k x x = 0 := by simp [torusDistance]

lemma torusDistance_symm (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) :
    torusDistance n k x y = torusDistance n k y x := by
  simp only [torusDistance, SimpleGraph.dist_comm]

lemma torusDistance_triangle (n k : ℕ) (x y z : Fin (n + 3) × Fin (k + 3)) :
    torusDistance n k x z ≤ torusDistance n k x y + torusDistance n k y z := by
  unfold torusDistance
  exact_mod_cast ((cycleGraph_connected (n := n + 2)).boxProd
    (cycleGraph_connected (n := k + 2))).dist_triangle (u := x) (v := y) (w := z)

lemma torusDistance_nonneg (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) :
    0 ≤ torusDistance n k x y := by unfold torusDistance; positivity

lemma torusDistance_half (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    torusDistance n k x (productHalfShift n (Fin (k + 3)) x) = ((n + 3) / 2 : ℕ) := by
  unfold torusDistance
  rw [torusHalfShift_distance]

/-- R≤L/8 is more than enough for the fixed half-period shift, including odd L. -/
lemma torus_half_separated (n k : ℕ) {R : ℝ} (hR : R ≤ (n + 3 : ℕ) / 8) :
    ∀ x : Fin (n + 3) × Fin (k + 3),
      2 * R ≤ torusDistance n k x (productHalfShift n (Fin (k + 3)) x) := by
  intro x
  rw [torusDistance_half]
  have hn : n + 3 ≤ 4 * ((n + 3) / 2) := by omega
  have hn' : (n + 3 : ℕ) ≤ (4 : ℝ) * ((n + 3) / 2 : ℕ) := by exact_mod_cast hn
  linarith

end GraphicalAllocation.Applications.Graphs
