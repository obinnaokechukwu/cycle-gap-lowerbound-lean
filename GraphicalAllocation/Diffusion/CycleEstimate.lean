import GraphicalAllocation.Diffusion.TagJoint
import GraphicalAllocation.Geometry.CycleMidpoint

/-! # The sharp cycle diffusion constant from actual Fourier geometry -/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators
open Palm Projections Geometry SimpleGraph

lemma cycle_endpoint_square_fourier_le (n : ℕ) (a b u v : Fin (n + 3))
    (hu : u = a ∨ u = a + 1) (hv : v = b ∨ v = b + 1) :
    (((cycleGraph (n + 3)).dist u v : ℝ) ^ 2) ≤
      ((n + 3 : ℝ) ^ 2 / 8) * ‖cycleMidpointFourier n b - cycleMidpointFourier n a‖ ^ 2 + 2 := by
  have hn : (0 : ℝ) < n + 3 := by positivity
  have hd : ((cycleGraph (n + 3)).dist u v : ℝ) ≤ (cycleGraph (n + 3)).dist a b + 1 := by
    exact_mod_cast cycle_endpoint_dist_le n a b u v hu hv
  have hc := cycleFourier_chord_lower n a b
  rw [← cycleMidpointFourier_chord] at hc
  have hc' : 4 * ((cycleGraph (n + 3)).dist a b : ℝ) ≤
      ‖cycleMidpointFourier n b - cycleMidpointFourier n a‖ * (n + 3) :=
    (div_le_iff₀ hn).mp hc
  have hs := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 4 * ((cycleGraph (n + 3)).dist a b : ℝ))
    (by positivity : (0 : ℝ) ≤ ‖cycleMidpointFourier n b - cycleMidpointFourier n a‖ * (n + 3))).mpr hc'
  have ht := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (cycleGraph (n + 3)).dist u v)
    (by positivity : (0 : ℝ) ≤ (cycleGraph (n + 3)).dist a b + 1)).mpr hd
  nlinarith [sq_nonneg (((cycleGraph (n + 3)).dist a b : ℝ) - 1)]

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The conditional cycle estimate from exact local cells and four-fiber mass.
Every geometric constant is proved using the canonical cycle metric. -/
theorem cycle_tag_displacement_le (n : ℕ) {μ : M → ℝ} (hμ : ∀ a, 0 < μ a)
    (htotal : ∑ a, μ a = 1) (edge : M → Fin (n + 3))
    (p : ℕ → M → Fin (n + 3)) (S : ℕ → Finset (Fin (n + 3)))
    (hend : ∀ k a, p k a = (cycleOrientation n).tail (edge a) ∨
      p k a = (cycleOrientation n).head (edge a))
    (houtside : ∀ k a, p (k + 1) a ∉ S k → p k a = p (k + 1) a)
    (hmass : ∀ k, (∑ a, if p (k + 1) a ∈ S k then μ a else 0) ≤ 4 / (n + 3)) (h : ℕ) :
    (∑ i, ∑ j, cellMass μ (p 0) i * tagEvolution μ p h i j *
      ((cycleGraph (n + 3)).dist i j : ℝ) ^ 2) ≤ 2 * Real.pi ^ 2 * h / (n + 3) + 2 := by
  let g : M → ℂ := fun a => cycleMidpointFourier n (edge a)
  let q := fun k => cellKernel μ (localKey (p (k + 1)) (S k))
  have hp := cell_endpointJoint_probability hμ htotal (fun k => localKey (p (k + 1)) (S k)) h
  have he := local_chain_displacement_le hμ (fun k => p (k + 1)) S g
    (fun _ => cycleCellCenter n) (Real.sin (Real.pi / (n + 3))) (4 / (n + 3))
    (fun k a _ => (cycle_cell_radius n (p (k + 1) a) (edge a) (hend (k + 1) a)).le) hmass h
  rw [← endpointJoint_observable hμ p S houtside h (fun i j => ((cycleGraph (n + 3)).dist i j : ℝ) ^ 2)]
  have hbound : (∑ a, ∑ b, endpointJoint μ q h a b *
      ((cycleGraph (n + 3)).dist (p 0 a) (p h b) : ℝ) ^ 2) ≤
      ((n + 3 : ℝ) ^ 2 / 8) * (∑ a, ∑ b, endpointJoint μ q h a b * ‖g b - g a‖ ^ 2) + 2 := by
    calc
      _ ≤ ∑ a, ∑ b, endpointJoint μ q h a b *
          (((n + 3 : ℝ) ^ 2 / 8) * ‖g b - g a‖ ^ 2 + 2) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left
          (cycle_endpoint_square_fourier_le n (edge a) (edge b) (p 0 a) (p h b) (hend 0 a) (hend h b)) (hp.1 a b)
      _ = ((n + 3 : ℝ) ^ 2 / 8) * (∑ a, ∑ b, endpointJoint μ q h a b * ‖g b - g a‖ ^ 2) +
          (∑ a, ∑ b, endpointJoint μ q h a b) * 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        congr 1
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [hp.2]; ring
  have hn : (0 : ℝ) < n + 3 := by positivity
  have hs : Real.sin (Real.pi / (n + 3)) ^ 2 ≤ (Real.pi / (n + 3)) ^ 2 :=
    (sq_le_sq₀ (cycle_sin_pos n).le (by positivity)).mpr (Real.sin_le (by positivity))
  calc
    _ ≤ ((n + 3 : ℝ) ^ 2 / 8) * (∑ a, ∑ b, endpointJoint μ q h a b * ‖g b - g a‖ ^ 2) + 2 := hbound
    _ ≤ ((n + 3 : ℝ) ^ 2 / 8) * (4 * h * (4 / (n + 3)) * Real.sin (Real.pi / (n + 3)) ^ 2) + 2 := by
      gcongr
    _ ≤ ((n + 3 : ℝ) ^ 2 / 8) * (4 * h * (4 / (n + 3)) * (Real.pi / (n + 3)) ^ 2) + 2 := by
      gcongr
    _ = _ := by field_simp; ring

end GraphicalAllocation.Diffusion
