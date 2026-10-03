import GraphicalAllocation.Spectral.Green

/-! # Elementary Dirichlet-form estimates for actual simple graphs -/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each unoriented edge contributes one square to the Dirichlet energy. -/
theorem edge_square_le_energy {u v : V} (huv : G.Adj u v) (x : V → ℝ) :
    (x u - x v)^2 ≤ x ⬝ᵥ laplacian G x := by
  let row (i : V) := ∑ j, if G.Adj i j then (x i - x j)^2 else 0
  have hr (i : V) : 0 ≤ row i := by dsimp [row]; positivity
  have hu : (x u - x v)^2 ≤ row u := by
    simpa [row, huv] using
      (Finset.single_le_sum (f := fun j => if G.Adj u j then (x u - x j)^2 else 0)
        (fun j _ => by positivity) (Finset.mem_univ v))
  have hv : (x v - x u)^2 ≤ row v := by
    simpa [row, huv.symm] using
      (Finset.single_le_sum (f := fun j => if G.Adj v j then (x v - x j)^2 else 0)
        (fun j _ => by positivity) (Finset.mem_univ u))
  have hp : row u + row v ≤ ∑ i, row i := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({u, v} : Finset V)) (fun i _ _ => hr i)
    simpa [Finset.sum_pair huv.ne] using hs
  rw [laplacian_energy]
  change (x u - x v)^2 ≤ (∑ i, row i) / 2
  nlinarith [hu, hv, hp]

/-- The maximum-degree estimate for the largest Laplacian eigenvalue,
expressed as a quadratic-form inequality and requiring no spectral theorem. -/
theorem laplacian_energy_le (d : ℝ) (hd : ∀ v, (G.degree v : ℝ) ≤ d)
    (x : V → ℝ) : x ⬝ᵥ laplacian G x ≤ 2 * d * (x ⬝ᵥ x) := by
  have hrow (i : V) :
      (∑ j, if G.Adj i j then (x i)^2 else 0) = G.degree i * (x i)^2 := by
    rw [G.degree_eq_sum_if_adj]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  have hflip : (∑ i, ∑ j, if G.Adj i j then (x j)^2 else 0) =
      ∑ i, G.degree i * (x i)^2 := by
    rw [Finset.sum_comm]
    simp_rw [G.adj_comm, hrow]
  have hsum : (∑ i, ∑ j, if G.Adj i j then (x i - x j)^2 else 0) ≤
      4 * ∑ i, G.degree i * (x i)^2 := by
    calc
      _ ≤ ∑ i, ∑ j, if G.Adj i j then 2 * (x i)^2 + 2 * (x j)^2 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> nlinarith [sq_nonneg (x i + x j)]
      _ = _ := by
        have he (i j : V) :
            (if G.Adj i j then 2 * (x i)^2 + 2 * (x j)^2 else 0) =
              2 * (if G.Adj i j then (x i)^2 else 0) +
              2 * (if G.Adj i j then (x j)^2 else 0) := by
          split_ifs <;> ring
        simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hflip]
        simp_rw [hrow]
        ring
  have hd' : (∑ i, G.degree i * (x i)^2) ≤ d * (x ⬝ᵥ x) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [sq] using mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (x i))
  rw [laplacian_energy]
  linarith

variable (hG : G.Connected)

/-- Unit resistance of a single graph edge, derived from the inverse equation. -/
theorem edge_energy_le_one {u v : V} (huv : G.Adj u v) :
    energy G hG (Pi.single u 1 - Pi.single v 1) ≤ 1 := by
  let x : V → ℝ := Pi.single u 1 - Pi.single v 1
  have he : energy G hG x = green G hG x u - green G hG x v := by
    simp [energy, x, sub_dotProduct]
    ring
  have hs := edge_square_le_energy G huv (green G hG x)
  rw [← energy_eq_dirichlet G hG x, ← he] at hs
  have hq := energy_nonneg G hG x
  nlinarith

end GraphicalAllocation.Spectral
