import GraphicalAllocation.Spectral.Dirichlet

/-! # Green diagonal, maximum diagonal, and the normalization lower bound -/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- Variational lower bound for the inverse energy. -/
theorem energy_variational {x : V → ℝ} (hx : x ∈ meanZero) (f : V → ℝ) :
    2 * (x ⬝ᵥ f) - f ⬝ᵥ laplacian G f ≤ energy G hG x := by
  have hn := laplacian_nonneg G (green G hG x - f)
  rw [map_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    ← energy_eq_dirichlet, laplacian_green, center_eq_self hx] at hn
  have hc : green G hG x ⬝ᵥ laplacian G f = x ⬝ᵥ f := by
    rw [laplacian_self_adjoint, laplacian_green, center_eq_self hx, dotProduct_comm]
  rw [hc, dotProduct_comm f x] at hn
  linarith

/-- The largest-eigenvalue estimate gives a lower bound on inverse energy. -/
theorem norm_le_energy (d : ℝ) (hdpos : 0 < d)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) {x : V → ℝ} (hx : x ∈ meanZero) :
    x ⬝ᵥ x ≤ (2 * d) * energy G hG x := by
  let c : ℝ := (2 * d)⁻¹
  have hc : c * (2 * d) = 1 := inv_mul_cancel₀ (by positivity)
  have hcp : 0 < c := by dsimp [c]; positivity
  have hv := energy_variational G hG hx (c • x)
  simp only [map_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hv
  have hu := mul_le_mul_of_nonneg_left (laplacian_energy_le G d hd x) (sq_nonneg c)
  have he : c^2 * (2 * d * (x ⬝ᵥ x)) = c * (x ⬝ᵥ x) := by
    calc
      _ = (c * (2 * d)) * (c * (x ⬝ᵥ x)) := by ring
      _ = _ := by rw [hc, one_mul]
  rw [he] at hu
  have hq : c * (x ⬝ᵥ x) ≤ energy G hG x := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * d by positivity)
  have he' : (2 * d) * (c * (x ⬝ᵥ x)) = x ⬝ᵥ x := by
    calc
      _ = (c * (2 * d)) * (x ⬝ᵥ x) := by ring
      _ = _ := by rw [hc, one_mul]
  rwa [he'] at hh

theorem center_single_norm (v : V) :
    center (Pi.single v (1 : ℝ)) ⬝ᵥ center (Pi.single v 1) =
      1 - 1 / (Fintype.card V : ℝ) := by
  let : Nonempty V := ⟨v⟩
  rw [dot_center_left _ (center_mem _), single_one_dotProduct]
  simp [center_apply]

/-- Each diagonal has the lower bound used in the GFF comparison. -/
theorem greenDiagonal_lower (d : ℝ) (hdpos : 0 < d)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (v : V) :
    (1 - 1 / (Fintype.card V : ℝ)) / 2 ≤ d * greenDiagonal G hG v := by
  have h := norm_le_energy G hG d hdpos hd
    (@center_mem V _ hG.nonempty (Pi.single v 1))
  rw [center_single_norm, energy_center_single] at h
  linarith

/-- The paper's `R_G`, using the maximum of actual Green diagonal entries. -/
def greenRadius : ℝ := by
  letI : Nonempty V := hG.nonempty
  exact Finset.univ.sup' Finset.univ_nonempty (greenDiagonal G hG)

theorem greenDiagonal_le_radius (v : V) :
    greenDiagonal G hG v ≤ greenRadius G hG :=
  Finset.le_sup' (greenDiagonal G hG) (Finset.mem_univ v)

theorem greenRadius_le {c : ℝ} (hc : ∀ v, greenDiagonal G hG v ≤ c) :
    greenRadius G hG ≤ c := Finset.sup'_le _ _ (fun v _ => hc v)

theorem exists_greenDiagonal_eq_radius : ∃ v, greenDiagonal G hG v = greenRadius G hG := by
  let : Nonempty V := hG.nonempty
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) Finset.univ_nonempty (greenDiagonal G hG)
  exact ⟨v, hv.symm⟩

theorem greenRadius_nonneg : 0 ≤ greenRadius G hG := by
  obtain ⟨v⟩ := hG.nonempty
  exact (greenDiagonal_nonneg G hG v).trans (greenDiagonal_le_radius G hG v)

theorem greenRadius_lower (d : ℝ) (hdpos : 0 < d)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) :
    (1 - 1 / (Fintype.card V : ℝ)) / 2 ≤ d * greenRadius G hG := by
  obtain ⟨v⟩ := hG.nonempty
  exact (greenDiagonal_lower G hG d hdpos hd v).trans
    (mul_le_mul_of_nonneg_left (greenDiagonal_le_radius G hG v) hdpos.le)

theorem one_third_le_degree_radius (d : ℝ) (hdpos : 0 < d)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (hN : 3 ≤ Fintype.card V) :
    (1 : ℝ) / 3 ≤ d * greenRadius G hG := by
  have hNr : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hi : (1 : ℝ) / (Fintype.card V : ℝ) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num) hNr
  have h := greenRadius_lower G hG d hdpos hd
  linarith

end GraphicalAllocation.Spectral
