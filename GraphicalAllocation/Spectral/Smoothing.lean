import GraphicalAllocation.Spectral.Dirichlet
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Smoothing powers and the Green-energy budget

The finite-time bound needed by the stopped martingale follows by telescoping
the Green energy.  This proves the geometric-series estimate without assuming
a spectral decomposition or a bound on the graph's inverse energy.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace GraphicalAllocation.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One step of the discrete heat operator. -/
def smoothing (α : ℝ) : Module.End ℝ (V → ℝ) := LinearMap.id - α • laplacian G

theorem smoothing_apply (α : ℝ) (x : V → ℝ) :
    smoothing G α x = x - α • laplacian G x := rfl

theorem smoothing_self_adjoint (α : ℝ) (x y : V → ℝ) :
    smoothing G α x ⬝ᵥ y = x ⬝ᵥ smoothing G α y := by
  simp only [smoothing_apply, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (laplacian G x) y, laplacian_self_adjoint]

theorem smoothing_pow_self_adjoint (α : ℝ) (k : ℕ) (x y : V → ℝ) :
    (((smoothing G α)^k) x) ⬝ᵥ y = x ⬝ᵥ (((smoothing G α)^k) y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, smoothing_self_adjoint,
      ← Module.End.mul_apply, ← pow_succ']
    rw [pow_succ]

theorem smoothing_constant (α c : ℝ) : smoothing G α (fun _ => c) = fun _ => c := by
  rw [smoothing_apply, laplacian_constant, smul_zero, sub_zero]

theorem smoothing_apply_vertex (α : ℝ) (x : V → ℝ) (v : V) :
    smoothing G α x v = (1 - α * G.degree v) * x v +
      α * ∑ w ∈ G.neighborFinset v, x w := by
  simp [smoothing_apply, SimpleGraph.lapMatrix_mulVec_apply]
  ring

theorem smoothing_mem (α : ℝ) {x : V → ℝ} (hx : x ∈ meanZero) :
    smoothing G α x ∈ meanZero :=
  meanZero.sub_mem hx (meanZero.smul_mem α (laplacian_mem G x))

theorem smoothing_pow_mem (α : ℝ) {x : V → ℝ} (hx : x ∈ meanZero) (k : ℕ) :
    ((smoothing G α)^k) x ∈ meanZero := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    simpa only [pow_succ', Module.End.mul_apply] using smoothing_mem G α ih

/-- The nonnegative stochastic heat step preserves every uniform bound. -/
theorem abs_smoothing_le (α c : ℝ) (hα : 0 ≤ α)
    (hαd : ∀ v, α * (G.degree v : ℝ) ≤ 1)
    {x : V → ℝ} (hx : ∀ v, |x v| ≤ c) (v : V) :
    |smoothing G α x v| ≤ c := by
  have hcoef : 0 ≤ 1 - α * G.degree v := sub_nonneg.mpr (hαd v)
  have hi : ∑ w ∈ G.neighborFinset v, x w ≤ (G.degree v : ℝ) * c := by
    calc
      _ ≤ ∑ _w ∈ G.neighborFinset v, c := Finset.sum_le_sum (fun w _ => (abs_le.mp (hx w)).2)
      _ = _ := by simp
  have lo : -((G.degree v : ℝ) * c) ≤ ∑ w ∈ G.neighborFinset v, x w := by
    calc
      _ = ∑ _w ∈ G.neighborFinset v, -c := by simp
      _ ≤ _ := Finset.sum_le_sum (fun w _ => (abs_le.mp (hx w)).1)
  rw [smoothing_apply_vertex, abs_le]
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hx v)).1 hcoef
    have h₂ := mul_le_mul_of_nonneg_left lo hα
    nlinarith
  · have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hx v)).2 hcoef
    have h₂ := mul_le_mul_of_nonneg_left hi hα
    nlinarith

theorem abs_smoothing_pow_le (α c : ℝ) (hα : 0 ≤ α)
    (hαd : ∀ v, α * (G.degree v : ℝ) ≤ 1)
    {x : V → ℝ} (hx : ∀ v, |x v| ≤ c) (k : ℕ) (v : V) :
    |(((smoothing G α)^k) x) v| ≤ c := by
  induction k generalizing v with
  | zero => simpa using hx v
  | succ k ih =>
    simpa only [pow_succ', Module.End.mul_apply] using
      abs_smoothing_le G α c hα hαd (fun w => ih w) v

variable (hG : G.Connected)

theorem green_smoothing (α : ℝ) (x : V → ℝ) :
    green G hG (smoothing G α x) = green G hG x - α • center x := by
  rw [smoothing_apply, map_sub, map_smul, green_laplacian]

theorem energy_smoothing (α : ℝ) {x : V → ℝ} (hx : x ∈ meanZero) :
    energy G hG (smoothing G α x) = energy G hG x - 2 * α * (x ⬝ᵥ x) +
      α^2 * (x ⬝ᵥ laplacian G x) := by
  rw [energy, green_smoothing, smoothing_apply, center_eq_self hx]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  have he : laplacian G x ⬝ᵥ green G hG x = x ⬝ᵥ x := by
    rw [dotProduct_comm, laplacian_self_adjoint, laplacian_green, center_eq_self hx]
  rw [he, dotProduct_comm (laplacian G x) x]
  unfold energy
  ring

/-- The inverse energy dissipated in one heat step controls the squared norm. -/
theorem smoothing_dissipation (α d : ℝ) (hα : 0 ≤ α)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (hstep : α * (2 * d) ≤ 1)
    {x : V → ℝ} (hx : x ∈ meanZero) :
    α * (x ⬝ᵥ x) ≤ energy G hG x - energy G hG (smoothing G α x) := by
  rw [energy_smoothing G hG α hx]
  have hu := laplacian_energy_le G d hd x
  have hnorm : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have h₁ := mul_le_mul_of_nonneg_left hu (sq_nonneg α)
  have h₂ := mul_le_mul_of_nonneg_right hstep (mul_nonneg hα hnorm)
  nlinarith

/-- The finite geometric-series energy bound needed for every fixed horizon. -/
theorem smoothing_energy_budget (α d : ℝ) (hα : 0 < α)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (hstep : α * (2 * d) ≤ 1)
    {x : V → ℝ} (hx : x ∈ meanZero) (k : ℕ) :
    (∑ j ∈ Finset.range k, (((smoothing G α)^j) x) ⬝ᵥ (((smoothing G α)^j) x)) ≤
      energy G hG x / α := by
  have ht : α * (∑ j ∈ Finset.range k,
      (((smoothing G α)^j) x) ⬝ᵥ (((smoothing G α)^j) x)) ≤
      energy G hG x - energy G hG (((smoothing G α)^k) x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h₁ := smoothing_dissipation G hG α d hα.le hd hstep
        (smoothing_pow_mem G α hx k)
      rw [Finset.sum_range_succ, mul_add, pow_succ', Module.End.mul_apply]
      linarith
  apply (le_div_iff₀ hα).mpr
  have hn := energy_nonneg G hG (((smoothing G α)^k) x)
  nlinarith

include hG in
/-- The full infinite series in the paper's energy budget is summable. -/
theorem smoothing_energy_summable (α d : ℝ) (hα : 0 < α)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (hstep : α * (2 * d) ≤ 1)
    {x : V → ℝ} (hx : x ∈ meanZero) :
    Summable (fun j : ℕ => (((smoothing G α)^j) x) ⬝ᵥ (((smoothing G α)^j) x)) := by
  apply summable_of_sum_range_le (c := energy G hG x / α)
  · intro j
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  · exact smoothing_energy_budget G hG α d hα hd hstep hx

/-- Infinite geometric-series bound, proved by finite energy dissipation. -/
theorem smoothing_energy_tsum_le (α d : ℝ) (hα : 0 < α)
    (hd : ∀ v, (G.degree v : ℝ) ≤ d) (hstep : α * (2 * d) ≤ 1)
    {x : V → ℝ} (hx : x ∈ meanZero) :
    (∑' j : ℕ, (((smoothing G α)^j) x) ⬝ᵥ (((smoothing G α)^j) x)) ≤
      energy G hG x / α := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  · exact smoothing_energy_budget G hG α d hα hd hstep hx

end GraphicalAllocation.Spectral
