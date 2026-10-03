import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Graph Laplacian and the mean-zero space

The operator in this file is Mathlib's actual combinatorial Laplacian.  No
spectral estimates or inverse-energy inequalities are part of its interface.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The subspace orthogonal to the constant profile. -/
def meanZero : Submodule ℝ (V → ℝ) where
  carrier := {x | ∑ v, x v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ v, x v = 0 at hx
    change ∑ v, y v = 0 at hy
    simp [Finset.sum_add_distrib, hx, hy]
  smul_mem' := by
    intro a x hx
    change ∑ v, x v = 0 at hx
    simp [← Finset.mul_sum, hx]

omit [DecidableEq V] in
@[simp] theorem mem_meanZero (x : V → ℝ) :
    x ∈ meanZero ↔ ∑ v, x v = 0 := Iff.rfl

/-- Orthogonal removal of the constant profile, as a linear endomorphism. -/
def center : Module.End ℝ (V → ℝ) where
  toFun x v := x v - (∑ w, x w) / Fintype.card V
  map_add' x y := by ext v; simp [Finset.sum_add_distrib]; ring
  map_smul' a x := by ext v; simp [← Finset.mul_sum]; ring

omit [DecidableEq V] in
@[simp] theorem center_apply (x : V → ℝ) (v : V) :
    center x v = x v - (∑ w, x w) / Fintype.card V := rfl

omit [DecidableEq V] in
theorem center_mem [Nonempty V] (x : V → ℝ) : center x ∈ meanZero := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change ∑ v, (x v - (∑ w, x w) / Fintype.card V) = 0
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq V] in
theorem center_eq_self {x : V → ℝ} (hx : x ∈ meanZero) : center x = x := by
  ext v
  simp [center_apply, (mem_meanZero x).mp hx]

omit [DecidableEq V] in
theorem dot_center_right {x : V → ℝ} (hx : x ∈ meanZero) (y : V → ℝ) :
    x ⬝ᵥ center y = x ⬝ᵥ y := by
  simp [dotProduct, center_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, (mem_meanZero x).mp hx]

omit [DecidableEq V] in
theorem dot_center_left (x : V → ℝ) {y : V → ℝ} (hy : y ∈ meanZero) :
    center x ⬝ᵥ y = x ⬝ᵥ y := by
  rw [dotProduct_comm, dot_center_right hy, dotProduct_comm]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The genuine combinatorial Laplacian, acting on real vertex profiles. -/
def laplacian : Module.End ℝ (V → ℝ) := (G.lapMatrix ℝ).toLin'

@[simp] theorem laplacian_apply (x : V → ℝ) :
    laplacian G x = G.lapMatrix ℝ *ᵥ x := rfl

theorem laplacian_self_adjoint (x y : V → ℝ) :
    x ⬝ᵥ laplacian G y = y ⬝ᵥ laplacian G x := by
  simpa only [laplacian_apply, (G.isSymm_lapMatrix ℝ).eq] using
    dotProduct_transpose_mulVec (G.lapMatrix ℝ) x y

theorem laplacian_mem (x : V → ℝ) : laplacian G x ∈ meanZero := by
  have h := laplacian_self_adjoint G (1 : V → ℝ) x
  simpa [dotProduct, G.lapMatrix_mulVec_one_eq_zero ℝ] using h

theorem laplacian_energy (x : V → ℝ) :
    x ⬝ᵥ laplacian G x =
      (∑ i, ∑ j, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  simpa only [Matrix.toLinearMap₂'_apply', laplacian_apply] using
    G.lapMatrix_toLinearMap₂' ℝ x

theorem laplacian_nonneg (x : V → ℝ) : 0 ≤ x ⬝ᵥ laplacian G x := by
  rw [laplacian_energy]
  positivity

theorem laplacian_constant (c : ℝ) : laplacian G (fun _ => c) = 0 := by
  ext v
  simp [SimpleGraph.lapMatrix_mulVec_apply']

theorem laplacian_center (x : V → ℝ) : laplacian G (center x) = laplacian G x := by
  have h : center x = x - fun _ => (∑ w, x w) / Fintype.card V := rfl
  rw [h, map_sub, laplacian_constant, sub_zero]

/-- The restriction of the Laplacian to the invariant mean-zero space. -/
def laplacianZero : Module.End ℝ (meanZero (V := V)) where
  toFun x := ⟨laplacian G x, laplacian_mem G x⟩
  map_add' x y := Subtype.ext <| (laplacian G).map_add x y
  map_smul' a x := Subtype.ext <| (laplacian G).map_smul a x

theorem laplacianZero_injective (hG : G.Connected) :
    Function.Injective (laplacianZero G) := by
  let : Nonempty V := hG.nonempty
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hL : G.lapMatrix ℝ *ᵥ (x : V → ℝ) = 0 := congrArg Subtype.val hx
  have hc := G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hL
  apply Subtype.ext
  ext v
  have hs : (Fintype.card V : ℝ) * (x : V → ℝ) v = 0 := by
    have he : (x : V → ℝ) = fun _ => (x : V → ℝ) v := funext (fun w => hc w v (hG w v))
    have hm := x.property
    change ∑ w, (x : V → ℝ) w = 0 at hm
    rw [he] at hm
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hm
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hs).resolve_left hn

end GraphicalAllocation.Spectral
