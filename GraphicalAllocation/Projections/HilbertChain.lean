import GraphicalAllocation.Projections.Chain

/-!
# Hilbert-valued finite stationary projection chains

Reduce first to orthonormal coordinates in a finite-dimensional Hilbert space,
then to the finite-dimensional span of the finitely many function values.
Thus the final theorem has no finite-dimensionality assumption on its target.
-/

noncomputable section

open scoped BigOperators Matrix

namespace GraphicalAllocation.Projections

variable {A E : Type*} [Fintype A] [DecidableEq A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Kernel averaging of a Hilbert-valued function. -/
def vectorAverage (q : Matrix A A ℝ) (f : A → E) (a : A) : E :=
  ∑ b, q a b • f b

private theorem sum_rotate {I J K : Type*} (s : Finset I) (t : Finset J) (u : Finset K)
    (f : I → J → K → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) =
      ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, f i j k := by
  calc
    _ = ∑ i ∈ s, ∑ k ∈ u, ∑ j ∈ t, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Hilbert-valued version in finite-dimensional real spaces. -/
theorem finiteDimensional_chain_displacement_le [FiniteDimensional ℝ E]
    {μ : A → ℝ} (hμ : ∀ a, 0 < μ a) (q : ℕ → Matrix A A ℝ)
    (hrow : ∀ j a, ∑ b, q j a b = 1)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a)
    (hidem : ∀ j, q j * q j = q j) (f : A → E) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ q n a b * ‖f b - f a‖ ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a * ‖f a - vectorAverage (q j) f a‖ ^ 2 := by
  let e := stdOrthonormalBasis ℝ E
  have hnorm (x : E) : ‖x‖ ^ 2 = ∑ i, (inner ℝ (e i) x) ^ 2 := by
    symm
    simpa only [Real.norm_eq_abs, sq_abs] using e.sum_sq_norm_inner_right x
  have hcoord (i : Fin (Module.finrank ℝ E)) (j : ℕ) (a : A) :
      inner ℝ (e i) (f a - vectorAverage (q j) f a) =
      inner ℝ (e i) (f a) - (q j *ᵥ (fun b => inner ℝ (e i) (f b))) a := by
    simp [vectorAverage, inner_sub_right, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin (Module.finrank ℝ E)) _ =>
      stationary_chain_displacement_le hμ q hrow hbal hidem
        (fun a => inner ℝ (e i) (f a)) n)
  have hleft : (∑ a, ∑ b, endpointJoint μ q n a b * ‖f b - f a‖ ^ 2) =
      ∑ i, ∑ a, ∑ b, endpointJoint μ q n a b *
        (inner ℝ (e i) (f b) - inner ℝ (e i) (f a)) ^ 2 := by
    simp_rw [hnorm, inner_sub_right, Finset.mul_sum]
    exact sum_rotate _ _ _ _
  have hright : (∑ i : Fin (Module.finrank ℝ E),
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a *
        (inner ℝ (e i) (f a) - (q j *ᵥ (fun b => inner ℝ (e i) (f b))) a) ^ 2) =
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a * ‖f a - vectorAverage (q j) f a‖ ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [hnorm, hcoord, Finset.mul_sum]
    exact (sum_rotate _ _ _ _).symm
  rw [hleft]
  rw [← hright]
  exact h

/-- Equation (4.2) for finite stationary chains and arbitrary real Hilbert-valued
functions. Every function on a finite atom space has finite-dimensional range. -/
theorem hilbert_chain_displacement_le {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (q : ℕ → Matrix A A ℝ)
    (hrow : ∀ j a, ∑ b, q j a b = 1)
    (hbal : ∀ j a b, μ a * q j a b = μ b * q j b a)
    (hidem : ∀ j, q j * q j = q j) (f : A → E) (n : ℕ) :
    (∑ a, ∑ b, endpointJoint μ q n a b * ‖f b - f a‖ ^ 2) ≤
      4 * ∑ j ∈ Finset.range n, ∑ a, μ a * ‖f a - vectorAverage (q j) f a‖ ^ 2 := by
  let S := Submodule.span ℝ (Set.range f)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let g : A → S := fun a => ⟨f a, Submodule.subset_span (Set.mem_range_self a)⟩
  have h := finiteDimensional_chain_displacement_le hμ q hrow hbal hidem g n
  simpa only [vectorAverage, ← Submodule.norm_coe, Submodule.coe_sub,
    Submodule.coe_sum, Submodule.coe_smul, g] using h

end GraphicalAllocation.Projections
