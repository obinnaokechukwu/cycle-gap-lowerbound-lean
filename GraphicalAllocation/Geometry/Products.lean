import GraphicalAllocation.Geometry.Fourier
import GraphicalAllocation.Geometry.CycleEdges
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-! # Cylinder pseudometric and direct-sum torus embedding -/

noncomputable section
namespace GraphicalAllocation.Geometry
open SimpleGraph
open scoped Fin.CommRing

/-- The cylinder pseudometric forgets the cross-section, so disconnected
cross-sections cause no problem. -/
def cylinderDistance {W : Type*} (n : ℕ) (x y : Fin (n + 3) × W) : ℝ :=
  (cycleGraph (n + 3)).dist x.1 y.1

@[simp] theorem cylinderDistance_self {W : Type*} (n : ℕ) (x : Fin (n + 3) × W) :
    cylinderDistance n x x = 0 := by simp [cylinderDistance]

theorem cylinderDistance_nonneg {W : Type*} (n : ℕ) (x y : Fin (n + 3) × W) :
    0 ≤ cylinderDistance n x y := by unfold cylinderDistance; positivity

theorem cylinderDistance_comm {W : Type*} (n : ℕ) (x y : Fin (n + 3) × W) :
    cylinderDistance n x y = cylinderDistance n y x := by
  simp only [cylinderDistance, SimpleGraph.dist_comm]

theorem cylinderDistance_triangle {W : Type*} (n : ℕ) (x y z : Fin (n + 3) × W) :
    cylinderDistance n x z ≤ cylinderDistance n x y + cylinderDistance n y z := by
  unfold cylinderDistance
  exact_mod_cast (cycleGraph_connected (n := n + 2)).dist_triangle
    (u := x.1) (v := y.1) (w := z.1)

/-- A genuine canonical `PseudoMetricSpace` structure for the cylinder distance. -/
@[instance_reducible]
def cylinderPseudoMetric (n : ℕ) (W : Type*) : PseudoMetricSpace (Fin (n + 3) × W) where
  dist := cylinderDistance n
  dist_self := cylinderDistance_self n
  dist_comm := cylinderDistance_comm n
  dist_triangle := cylinderDistance_triangle n

/-- The cylinder coordinate is edge-Lipschitz on the actual Cartesian graph. -/
theorem cylinderEmbedding_edge {W : Type*} (H : SimpleGraph W) (n : ℕ)
    {x y : Fin (n + 3) × W} (h : (cycleGraph (n + 3) □ H).Adj x y) :
    ‖cycleEmbedding n y.1 - cycleEmbedding n x.1‖ ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact (cycleEmbedding_edge n h).le
  · simp [h]

/-- The circle distortion is unchanged by an arbitrary cross-section. -/
theorem cylinderEmbedding_distortion {W : Type*} (n : ℕ) (x y : Fin (n + 3) × W) :
    cylinderDistance n x y ≤ Real.pi / 2 * ‖cycleEmbedding n y.1 - cycleEmbedding n x.1‖ :=
  cycleEmbedding_distortion n x.1 y.1

/-- Finite balls for the cylinder pseudometric. -/
def cylinderBall {W : Type*} [Fintype W] (n : ℕ) (x : Fin (n + 3) × W) (r : ℕ) :
    Finset (Fin (n + 3) × W) := by
  classical
  exact Finset.univ.filter (fun y => (cycleGraph (n + 3)).dist x.1 y.1 ≤ r)

/-- Such a ball is exactly a cyclic ball times the whole cross-section. -/
theorem cylinderBall_eq_product {W : Type*} [Fintype W] (n : ℕ)
    (x : Fin (n + 3) × W) (r : ℕ) :
    cylinderBall n x r = graphBall (cycleGraph (n + 3)) x.1 r ×ˢ (Finset.univ : Finset W) := by
  classical
  ext y
  simp only [cylinderBall, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, mem_graphBall, and_true]
  have he := ((cycleGraph_connected (n := n + 2)) x.1 y.1).coe_dist_eq_edist
  rw [← he]
  exact_mod_cast (Iff.rfl : (cycleGraph (n + 3)).dist x.1 y.1 ≤ r ↔ _)

/-- The finite-width cylinder ball bound `w(2R+1)`. -/
theorem cylinderBall_card_le {W : Type*} [Fintype W] (n : ℕ)
    (x : Fin (n + 3) × W) (r : ℕ) :
    (cylinderBall n x r).card ≤ Fintype.card W * (2 * r + 1) := by
  rw [cylinderBall_eq_product, Finset.card_product, Finset.card_univ, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (cycle_graphBall_card_le n x.1 r)

/-- The exact graph metric of a rectangular torus is the sum of its cyclic
coordinate distances. -/
theorem torus_dist (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) :
    (cycleGraph (n + 3) □ cycleGraph (k + 3)).dist x y =
      (cycleGraph (n + 3)).dist x.1 y.1 + (cycleGraph (k + 3)).dist x.2 y.2 := by
  have h₁ := ((cycleGraph_connected (n := n + 2)) x.1 y.1).coe_dist_eq_edist
  have h₂ := ((cycleGraph_connected (n := k + 2)) x.2 y.2).coe_dist_eq_edist
  have hp := (((cycleGraph_connected (n := n + 2)).boxProd
    (cycleGraph_connected (n := k + 2))) x y).coe_dist_eq_edist
  rw [product_edist, ← h₁, ← h₂] at hp
  exact_mod_cast hp

/-- Hilbert direct sum of the two edge-normalized circles. The ordinary product
norm would be the max norm; `WithLp 2` specifies the required Hilbert norm. -/
def torusEmbedding (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (cycleEmbedding n x.1, cycleEmbedding k x.2)

/-- Pythagoras for the two circle coordinates. -/
theorem torusEmbedding_chord_sq (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) :
    ‖torusEmbedding n k y - torusEmbedding n k x‖ ^ 2 =
      ‖cycleEmbedding n y.1 - cycleEmbedding n x.1‖ ^ 2 +
      ‖cycleEmbedding k y.2 - cycleEmbedding k x.2‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- Every torus edge has Hilbert length one. -/
theorem torusEmbedding_edge (n k : ℕ) {x y : Fin (n + 3) × Fin (k + 3)}
    (h : (cycleGraph (n + 3) □ cycleGraph (k + 3)).Adj x y) :
    ‖torusEmbedding n k y - torusEmbedding n k x‖ = 1 := by
  have hs := torusEmbedding_chord_sq n k x y
  rcases h with ⟨h, he⟩ | ⟨h, he⟩
  · rw [he, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      cycleEmbedding_edge n h] at hs
    nlinarith [norm_nonneg (torusEmbedding n k y - torusEmbedding n k x)]
  · rw [he, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
      cycleEmbedding_edge k h] at hs
    nlinarith [norm_nonneg (torusEmbedding n k y - torusEmbedding n k x)]

/-- The actual torus graph metric has Hilbert distortion at most `π/√2`. -/
theorem torusEmbedding_distortion (n k : ℕ) (x y : Fin (n + 3) × Fin (k + 3)) :
    ((cycleGraph (n + 3) □ cycleGraph (k + 3)).dist x y : ℝ) ≤
      Real.pi / Real.sqrt 2 * ‖torusEmbedding n k y - torusEmbedding n k x‖ := by
  have h₁ := cycleEmbedding_distortion n x.1 y.1
  have h₂ := cycleEmbedding_distortion k x.2 y.2
  have h₁sq := (sq_le_sq₀ (by positivity) (by positivity)).mpr h₁
  have h₂sq := (sq_le_sq₀ (by positivity) (by positivity)).mpr h₂
  have hnorm := torusEmbedding_chord_sq n k x y
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hconst : (Real.pi / Real.sqrt 2) ^ 2 = Real.pi ^ 2 / 2 := by
    rw [div_pow, hsqrt]
  rw [torus_dist, Nat.cast_add]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, hconst]
  nlinarith [sq_nonneg (((cycleGraph (n + 3)).dist x.1 y.1 : ℝ) -
    ((cycleGraph (k + 3)).dist x.2 y.2 : ℝ))]

/-- Shift the long cyclic coordinate and leave the cross-section fixed. -/
def productHalfShift (n : ℕ) (W : Type*) : Equiv.Perm (Fin (n + 3) × W) :=
  (cycleHalfShift n).prodCongr (Equiv.refl W)

@[simp] theorem productHalfShift_apply {W : Type*} (n : ℕ) (x : Fin (n + 3) × W) :
    productHalfShift n W x = (cycleHalfShift n x.1, x.2) := rfl

/-- The fixed product shift separates cylinder vertices by half the long period. -/
theorem cylinderHalfShift_distance {W : Type*} (n : ℕ) (x : Fin (n + 3) × W) :
    cylinderDistance n x (productHalfShift n W x) = ((n + 3) / 2 : ℕ) := by
  simp [cylinderDistance, cycle_half_shift_dist]

/-- The same fixed shift separates torus vertices in the actual graph metric. -/
theorem torusHalfShift_distance (n k : ℕ) (x : Fin (n + 3) × Fin (k + 3)) :
    (cycleGraph (n + 3) □ cycleGraph (k + 3)).dist x
      (productHalfShift n (Fin (k + 3)) x) = (n + 3) / 2 := by
  simp [torus_dist, cycle_half_shift_dist]

end GraphicalAllocation.Geometry
