import GraphicalAllocation.Transport.Clipped
import GraphicalAllocation.Transport.Weighted

/-!
# Protected-ball counting, path by path

The loss and negative-credit families each contain at most one index, because
the terminal vertex is unique and the comparison map is a permutation. These
facts are proved before averaging, so neither event independence nor terminal
Palm conditional probabilities are needed for the lower bound.
-/

noncomputable section
namespace GraphicalAllocation.Transport
open Rules
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_supported_two (F : V → ℝ) (p q : V) (hpq : p ≠ q)
    (hzero : ∀ i, i ≠ p → i ≠ q → F i = 0) : ∑ i, F i = F p + F q := by
  calc
    ∑ i, F i = ∑ i, ((if i = p then F p else 0) + (if i = q then F q else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hip : i = p
      · subst i
        simp [hpq]
      · by_cases hiq : i = q
        · subst i
          simp [Ne.symm hpq]
        · simp [hip, hiq, hzero i hip hiq]
    _ = F p + F q := by simp [Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
/-- Positive radius and endpoint separation exclude fixed points even for a pseudometric. -/
theorem ne_of_separated (d : V → V → ℝ) (hdiag : ∀ i, d i i = 0)
    (ψ : Equiv.Perm V) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (i : V) : i ≠ ψ i := by
  intro hi
  have h := hsep i
  rw [← hi, hdiag] at h
  linarith

omit [Fintype V] [DecidableEq V] in
/-- A lost positive history must move at least the protecting radius. -/
theorem lost_positive_forces_displacement (d : V → V → ℝ)
    (hsym : ∀ i j, d i j = d j i) {R : ℝ} {a b : V}
    (hlost : ¬d b a ≤ R) : R ≤ d a b := by
  rw [hsym a b]
  exact le_of_lt (lt_of_not_ge hlost)

omit [Fintype V] [DecidableEq V] in
/-- An admitted negative history must move at least the protecting radius. -/
theorem admitted_negative_forces_displacement (d : V → V → ℝ)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R : ℝ} (hsep : ∀ i, 2 * R ≤ d i (ψ i))
    {a b : V} (hadmit : d (ψ.symm b) a ≤ R) : R ≤ d a b := by
  have hs := hsep (ψ.symm b)
  have ht := htriangle (ψ.symm b) a b
  simp only [Equiv.apply_symm_apply] at hs
  linarith

/-- Exact decomposition of the restricted derivative sum into two endpoint credits. -/
theorem restricted_terminal_sum (ψ : Equiv.Perm V) (hψ : ∀ i, i ≠ ψ i)
    (d : V → V → ℝ) (R M : ℝ) (x : Profile V) (a b : V) :
    (∑ i, if d i a ≤ R then finiteDifference (clippedContrast i (ψ i) M) x b else 0) =
      (if d b a ≤ R then finiteDifference (clippedContrast b (ψ b) M) x b else 0) +
      (if d (ψ.symm b) a ≤ R then
        finiteDifference (clippedContrast (ψ.symm b) b M) x b else 0) := by
  have hbi : b ≠ ψ.symm b := by
    intro hb
    have h := hψ (ψ.symm b)
    simp only [Equiv.apply_symm_apply] at h
    exact h hb.symm
  have h := sum_supported_two
    (fun i => if d i a ≤ R then finiteDifference (clippedContrast i (ψ i) M) x b else 0)
    b (ψ.symm b) hbi (by
      intro i hi hj
      have hbψ : b ≠ ψ i := by
        intro heq
        apply hj
        apply ψ.injective
        simpa using heq.symm
      simp [finiteDifference_off_endpoints i (ψ i) b M x (Ne.symm hi) hbψ])
  simpa using h

/-- The two-endpoint mean-increment bound used in the repaired discrete lemma. -/
theorem weighted_clipped_increment_abs_le (i j : V) (hij : i ≠ j)
    {M Δ : ℝ} (hM : 0 < M) (x : Profile V) (rate : V → ℝ)
    (hrate : ∀ v, 0 ≤ rate v) (hΔ : ∀ v, rate v ≤ Δ) :
    |∑ v, rate v * finiteDifference (clippedContrast i j M) x v| ≤ 2 * Δ / M := by
  rw [sum_supported_two _ i j hij (by
    intro v hvi hvj
    rw [finiteDifference_off_endpoints i j v M x hvi hvj, mul_zero])]
  have hi := finiteDifference_abs_le i j i hij hM x
  have hj := finiteDifference_abs_le i j j hij hM x
  calc
    _ ≤ |rate i * finiteDifference (clippedContrast i j M) x i| +
        |rate j * finiteDifference (clippedContrast i j M) x j| := abs_add_le _ _
    _ = rate i * |finiteDifference (clippedContrast i j M) x i| +
        rate j * |finiteDifference (clippedContrast i j M) x j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hrate i), abs_of_nonneg (hrate j)]
    _ ≤ rate i * (1 / M) + rate j * (1 / M) := add_le_add
      (mul_le_mul_of_nonneg_left hi (hrate i)) (mul_le_mul_of_nonneg_left hj (hrate j))
    _ ≤ Δ * (1 / M) + Δ * (1 / M) := add_le_add
      (mul_le_mul_of_nonneg_right (hΔ i) (le_of_lt (one_div_pos.mpr hM)))
      (mul_le_mul_of_nonneg_right (hΔ j) (le_of_lt (one_div_pos.mpr hM)))
    _ = 2 * Δ / M := by ring

section Gap
variable [Nonempty V]

/-- Pathwise protected-ball response. This is stronger than merely counting
expectations of exceptional histories: no stochastic independence is used. -/
theorem pathwise_protected_response (d : V → V → ℝ)
    (hdiag : ∀ i, d i i = 0) (hsym : ∀ i j, d i j = d j i)
    (htriangle : ∀ i j k, d i k ≤ d i j + d j k)
    (ψ : Equiv.Perm V) {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hsep : ∀ i, 2 * R ≤ d i (ψ i)) (x : Profile V) (a b : V) :
    (if gap x ≤ M - 1 then 1 / M else 0) -
        2 * (if R ≤ d a b then 1 / M else 0) ≤
      ∑ i, if d i a ≤ R then finiteDifference (clippedContrast i (ψ i) M) x b else 0 := by
  have hMpos : 0 < M := by linarith
  have hc : 0 ≤ 1 / M := le_of_lt (one_div_pos.mpr hMpos)
  have hψ := ne_of_separated d hdiag ψ hR hsep
  rw [restricted_terminal_sum ψ hψ d R M x a b]
  have hp := finiteDifference_first b (ψ b) (hψ b) hMpos x
  have hi : ψ.symm b ≠ b := by simpa using hψ (ψ.symm b)
  have hn := finiteDifference_second (ψ.symm b) b hi hMpos x
  have hg := finiteDifference_first_lower b (ψ b) (hψ b) hM x
  by_cases ht : R ≤ d a b
  · rw [ite_eq_left ht]
    split_ifs <;> linarith
  · have hpos : d b a ≤ R := by
      by_contra hbad
      exact ht (lost_positive_forces_displacement d hsym hbad)
    have hneg : ¬d (ψ.symm b) a ≤ R := by
      intro hbad
      exact ht (admitted_negative_forces_displacement d htriangle ψ hsep hbad)
    simp only [ite_eq_right ht, ite_eq_left hpos, ite_eq_right hneg, mul_zero, sub_zero, add_zero]
    exact hg

end Gap
end GraphicalAllocation.Transport
