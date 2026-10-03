import GraphicalAllocation.Spectral.Laplacian

/-!
# The graph Green operator

The inverse is constructed on the mean-zero subspace using connectedness and
finite dimensionality.  Its extension by zero on constants is the graph
Laplacian pseudoinverse used in the paper.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)

/-- Connectedness makes the mean-zero Laplacian an actual linear equivalence. -/
def laplacianEquiv : meanZero (V := V) ≃ₗ[ℝ] meanZero (V := V) :=
  LinearEquiv.ofInjectiveEndo (laplacianZero G) (laplacianZero_injective G hG)

/-- The Laplacian pseudoinverse, zero on constants and inverse on mean-zero profiles. -/
def green : Module.End ℝ (V → ℝ) := by
  letI : Nonempty V := hG.nonempty
  exact meanZero.subtype ∘ₗ (laplacianEquiv G hG).symm.toLinearMap ∘ₗ
    center.codRestrict meanZero center_mem

theorem green_mem (x : V → ℝ) : green G hG x ∈ meanZero := by
  exact ((laplacianEquiv G hG).symm ⟨center x, @center_mem V _ hG.nonempty x⟩).property

theorem laplacian_green (x : V → ℝ) :
    laplacian G (green G hG x) = center x := by
  exact congrArg Subtype.val ((laplacianEquiv G hG).apply_symm_apply
    ⟨center x, @center_mem V _ hG.nonempty x⟩)

theorem green_laplacian (x : V → ℝ) :
    green G hG (laplacian G x) = center x := by
  have hx := @center_mem V _ hG.nonempty x
  have he : (⟨center (laplacian G x),
      @center_mem V _ hG.nonempty (laplacian G x)⟩ : meanZero) =
      laplacianEquiv G hG ⟨center x, hx⟩ := by
    apply Subtype.ext
    exact (center_eq_self (laplacian_mem G x)).trans (laplacian_center G x).symm
  change ((laplacianEquiv G hG).symm ⟨center (laplacian G x),
    @center_mem V _ hG.nonempty (laplacian G x)⟩ : V → ℝ) = center x
  rw [he, LinearEquiv.symm_apply_apply]

theorem green_unique {x f : V → ℝ} (hf : f ∈ meanZero)
    (hLf : laplacian G f = center x) : green G hG x = f := by
  have he : laplacianZero G ⟨green G hG x, green_mem G hG x⟩ =
      laplacianZero G ⟨f, hf⟩ := by
    apply Subtype.ext
    exact (laplacian_green G hG x).trans hLf.symm
  exact congrArg Subtype.val (laplacianZero_injective G hG he)

theorem green_center (x : V → ℝ) : green G hG (center x) = green G hG x := by
  apply green_unique G hG (green_mem G hG x)
  rw [laplacian_green, center_eq_self (@center_mem V _ hG.nonempty x)]

theorem green_constant (c : ℝ) : green G hG (fun _ => c) = 0 := by
  apply green_unique G hG (meanZero.zero_mem)
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    let : Nonempty V := hG.nonempty
    exact_mod_cast Fintype.card_ne_zero
  ext v
  simp [center_apply, hn]

theorem green_self_adjoint (x y : V → ℝ) :
    x ⬝ᵥ green G hG y = y ⬝ᵥ green G hG x := by
  calc
    x ⬝ᵥ green G hG y = center x ⬝ᵥ green G hG y :=
      (dot_center_left x (green_mem G hG y)).symm
    _ = laplacian G (green G hG x) ⬝ᵥ green G hG y := by rw [laplacian_green]
    _ = laplacian G (green G hG y) ⬝ᵥ green G hG x := by
      simpa only [dotProduct_comm] using
        (laplacian_self_adjoint G (green G hG x) (green G hG y)).symm
    _ = y ⬝ᵥ green G hG x := by
      rw [laplacian_green, dot_center_left y (green_mem G hG x)]

/-- The quadratic form of the graph pseudoinverse. -/
def energy (x : V → ℝ) : ℝ := x ⬝ᵥ green G hG x

theorem energy_eq_dirichlet (x : V → ℝ) :
    energy G hG x = green G hG x ⬝ᵥ laplacian G (green G hG x) := by
  rw [laplacian_green, dot_center_right (green_mem G hG x), dotProduct_comm]
  rfl

theorem energy_nonneg (x : V → ℝ) : 0 ≤ energy G hG x := by
  rw [energy_eq_dirichlet]
  exact laplacian_nonneg G _

/-- Diagonal coefficients of the actual pseudoinverse matrix. -/
def greenDiagonal (v : V) : ℝ := green G hG (Pi.single v 1) v

theorem energy_center_single (v : V) :
    energy G hG (center (Pi.single v 1)) = greenDiagonal G hG v := by
  rw [energy, green_center, dot_center_left _ (green_mem G hG _)]
  exact single_one_dotProduct v _

theorem greenDiagonal_nonneg (v : V) : 0 ≤ greenDiagonal G hG v := by
  rw [← energy_center_single]
  exact energy_nonneg G hG _

end GraphicalAllocation.Spectral
