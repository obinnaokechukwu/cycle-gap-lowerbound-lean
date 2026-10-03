import GraphicalAllocation.Palm.FiniteKernel

/-! # Finite-path Palm intertwining

The inhomogeneous tag chain is defined by the literal cell-overlap transition
probabilities. The rate-biased marginal identity is proved at every event count.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

/-- Transition probability across the first `n` partitions. -/
def tagEvolution (μ : A → ℝ) (p : ℕ → A → V) : ℕ → V → V → ℝ
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑ k, tagEvolution μ p n i k * tagKernel μ (p n) (p (n + 1)) k j

omit [DecidableEq A] in
lemma tagEvolution_nonneg {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (p : ℕ → A → V) (n : ℕ) (i j : V) :
    0 ≤ tagEvolution μ p n i j := by
  induction n generalizing i j with
  | zero => simp [tagEvolution]; split_ifs <;> norm_num
  | succ n ih =>
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (ih i k) (tagKernel_nonneg hμ _ _ _ _)

omit [DecidableEq A] in
lemma tagEvolution_row_sum (μ : A → ℝ) (p : ℕ → A → V) (n : ℕ) (i : V) :
    ∑ j, tagEvolution μ p n i j = 1 := by
  induction n with
  | zero => simp [tagEvolution]
  | succ n ih =>
    simp only [tagEvolution]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, tagKernel_row_sum, mul_one]
    exact ih

omit [DecidableEq A] in
/-- The discrete-event Palm identity, for every deterministic sequence of
selection partitions, including empty vertex cells. -/
lemma palm_finite_path {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (p : ℕ → A → V) (n : ℕ) (j : V) :
    ∑ i, cellMass μ (p 0) i * tagEvolution μ p n i j = cellMass μ (p n) j := by
  induction n generalizing j with
  | zero => simp [tagEvolution]
  | succ n ih =>
    simp only [tagEvolution, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ih]
    exact palm_one_step hμ (p n) (p (n + 1)) j

omit [DecidableEq A] in
/-- Test-function version of the finite-event rate-biased intertwining. -/
lemma palm_finite_path_test {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (p : ℕ → A → V) (n : ℕ) (F : V → ℝ) :
    (∑ i, cellMass μ (p 0) i * ∑ j, tagEvolution μ p n i j * F j) =
      ∑ j, cellMass μ (p n) j * F j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, palm_finite_path hμ]

end GraphicalAllocation.Palm
