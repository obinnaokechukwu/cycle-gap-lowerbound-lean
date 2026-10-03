import GraphicalAllocation.Process.FinitePaths
import GraphicalAllocation.Probability.BernsteinScalar

/-!
# Bernstein concentration on the actual finite Markov path law

The six reconstruction stages are recorded in order.
0. Logical skeleton: for every kernel, reward and deterministic variance budget,
   centered bounded rewards imply an MGF bound and a two-sided tail bound.
1. Types: an arbitrary state type, a finite choice type, real rewards indexed by
   chronological natural time, and the existing `ChoicePath` sample space.
2. Predicates: finite weighted mean zero, a pointwise absolute bound, finite
   second moments and the existing normalized actual `pathWeight` law.
3. Architecture: split a path into first choice and remaining path, induct on
   length, apply the scalar exponential bound, and then exponential Markov to
   each sign of the reward.
4. Steps: the proofs below implement the induction and sign union bound.
5. Bookkeeping: finite-product sums, chronological index arithmetic, and the
   scalar Bernstein parameter and threshold identities.
-/

namespace GraphicalAllocation.Probability

open scoped BigOperators

/-- Exponential Markov inequality written directly as a finite weighted sum. -/
theorem sum_tail_le_exp_mul_sum_exp {ι : Type*} [Fintype ι]
    (p X : ι → ℝ) {a χ : ℝ} (hp : ∀ i, 0 ≤ p i) (hχ : 0 ≤ χ) :
    (∑ i, if a ≤ X i then p i else 0) ≤
      Real.exp (-χ * a) * ∑ i, p i * Real.exp (χ * X i) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hpi := hp i
  by_cases hi : a ≤ X i
  · rw [ite_eq_left hi]
    calc
      p i = p i * Real.exp 0 := by simp
      _ ≤ p i * Real.exp (-χ * a + χ * X i) := by
        apply mul_le_mul_of_nonneg_left _ (hp i)
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-χ * a) * (p i * Real.exp (χ * X i)) := by
        rw [Real.exp_add]
        ring
  · rw [ite_eq_right hi]
    positivity

/-- Apply exponential Markov to both signs and add their finite event masses. -/
theorem sum_abs_tail_le_of_mgf {ι : Type*} [Fintype ι]
    (p X : ι → ℝ) {a χ B : ℝ} (hp : ∀ i, 0 ≤ p i) (hχ : 0 ≤ χ)
    (hpos : ∑ i, p i * Real.exp (χ * X i) ≤ Real.exp B)
    (hneg : ∑ i, p i * Real.exp (χ * (-X i)) ≤ Real.exp B) :
    (∑ i, if a ≤ |X i| then p i else 0) ≤ 2 * Real.exp (-χ * a + B) := by
  classical
  have hunion : (∑ i, if a ≤ |X i| then p i else 0) ≤
      (∑ i, if a ≤ X i then p i else 0) +
        ∑ i, if a ≤ -X i then p i else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hpi := hp i
    by_cases habs : a ≤ |X i|
    · rw [ite_eq_left habs]
      rcases le_abs.mp habs with hi | hi
      · rw [ite_eq_left hi]
        exact le_add_of_nonneg_right (by split <;> positivity)
      · rw [ite_eq_left hi]
        exact le_add_of_nonneg_left (by split <;> positivity)
    · rw [ite_eq_right habs]
      positivity
  calc
    _ ≤ (∑ i, if a ≤ X i then p i else 0) +
        ∑ i, if a ≤ -X i then p i else 0 := hunion
    _ ≤ Real.exp (-χ * a) * (∑ i, p i * Real.exp (χ * X i)) +
        Real.exp (-χ * a) * ∑ i, p i * Real.exp (χ * (-X i)) :=
      add_le_add (sum_tail_le_exp_mul_sum_exp p X hp hχ)
        (sum_tail_le_exp_mul_sum_exp p (fun i => -X i) hp hχ)
    _ ≤ Real.exp (-χ * a) * Real.exp B + Real.exp (-χ * a) * Real.exp B :=
      add_le_add (mul_le_mul_of_nonneg_left hpos (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hneg (Real.exp_pos _).le)
    _ = 2 * Real.exp (-χ * a + B) := by rw [Real.exp_add]; ring

end GraphicalAllocation.Probability

namespace GraphicalAllocation.Process.FiniteKernel

open scoped BigOperators
open GraphicalAllocation.Probability

variable {State Choice : Type*} [Fintype Choice]
variable (K : FiniteKernel State Choice)

/-- Additive reward along the states and choices of the actual path, starting at
chronological time `start`. -/
def pathReward (r : ℕ → State → Choice → ℝ) :
    (start n : ℕ) → State → ChoicePath Choice n → ℝ
  | _, 0, _, _ => 0
  | start, n + 1, x, p => r start x p.1 +
      pathReward r (start + 1) n (K.next x p.1) p.2

@[simp] theorem pathReward_neg (r : ℕ → State → Choice → ℝ) (start n : ℕ)
    (x : State) (p : ChoicePath Choice n) :
    K.pathReward (fun i y c => -r i y c) start n x p = -K.pathReward r start n x p := by
  induction n generalizing start x with
  | zero => simp [pathReward]
  | succ n ih => simp [pathReward, ih, add_comm]

/-- Telescoping for chronological rewards supplied by local potential differences. -/
theorem pathReward_eq_terminal_sub (r : ℕ → State → Choice → ℝ)
    (φ : ℕ → State → ℝ) (start n : ℕ) (x : State) (p : ChoicePath Choice n)
    (hstep : ∀ i < n, ∀ y c, r (start + i) y c =
      φ (start + i + 1) (K.next y c) - φ (start + i) y) :
    K.pathReward r start n x p = φ (start + n) (K.pathTerminal n x p) - φ start x := by
  induction n generalizing start x with
  | zero => simp [pathReward, pathTerminal]
  | succ n ih =>
    rw [pathReward, pathTerminal]
    have hfirst := hstep 0 (by omega) x p.1
    simp only [Nat.add_zero] at hfirst
    rw [hfirst, ih (start + 1) (K.next x p.1) p.2]
    · have : start + 1 + n = start + (n + 1) := by omega
      rw [this]
      ring
    · intro i hi y c
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hstep (i + 1) (by omega) y c

/-- A difference reward sums exactly to terminal minus initial potential. -/
theorem pathReward_telescope (φ : ℕ → State → ℝ) (start n : ℕ)
    (x : State) (p : ChoicePath Choice n) :
    K.pathReward (fun i y c => φ (i + 1) (K.next y c) - φ i y) start n x p =
      φ (start + n) (K.pathTerminal n x p) - φ start x :=
  K.pathReward_eq_terminal_sub _ φ start n x p (by intros; rfl)

/-- Splitting the exponential path sum at the first actual transition. -/
theorem pathReward_mgf_succ (r : ℕ → State → Choice → ℝ) (start n : ℕ)
    (x : State) (χ : ℝ) :
    (∑ p, K.pathWeight (n + 1) x p * Real.exp (χ * K.pathReward r start (n + 1) x p)) =
      ∑ c, (K.weight x c * Real.exp (χ * r start x c)) *
        ∑ p, K.pathWeight n (K.next x c) p *
          Real.exp (χ * K.pathReward r (start + 1) n (K.next x c) p) := by
  change (∑ p : Choice × ChoicePath Choice n,
    (K.weight x p.1 * K.pathWeight n (K.next x p.1) p.2) *
      Real.exp (χ * (r start x p.1 + K.pathReward r (start + 1) n (K.next x p.1) p.2))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_add, Real.exp_add]
  ring

/-- Finite-path exponential estimate, with deterministic inhomogeneous variance. -/
theorem pathReward_mgf (r : ℕ → State → Choice → ℝ) (v : ℕ → ℝ)
    (start n : ℕ) (x : State) {b χ : ℝ}
    (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hχb : χ * b < 3)
    (hmean : ∀ i < n, ∀ y, ∑ c, K.weight y c * r (start + i) y c = 0)
    (hbound : ∀ i < n, ∀ y c, |r (start + i) y c| ≤ b)
    (hvar : ∀ i < n, ∀ y, ∑ c, K.weight y c * (r (start + i) y c) ^ 2 ≤ v (start + i)) :
    (∑ p, K.pathWeight n x p * Real.exp (χ * K.pathReward r start n x p)) ≤
      Real.exp ((χ ^ 2 / (2 * (1 - χ * b / 3))) * ∑ i ∈ Finset.range n, v (start + i)) := by
  induction n generalizing start x with
  | zero =>
    change (∑ _ : PUnit, (1 : ℝ) * Real.exp (χ * 0)) ≤ _
    simp
  | succ n ih =>
    let C : ℝ := χ ^ 2 / (2 * (1 - χ * b / 3))
    have htail (y : State) :
        (∑ p, K.pathWeight n y p * Real.exp (χ * K.pathReward r (start + 1) n y p)) ≤
        Real.exp (C * ∑ i ∈ Finset.range n, v (start + 1 + i)) := by
      apply ih (start + 1) y
      · intro i hi y
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hmean (i + 1) (by omega) y
      · intro i hi y c
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hbound (i + 1) (by omega) y c
      · intro i hi y
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hvar (i + 1) (by omega) y
    have hone : (∑ c, K.weight x c * Real.exp (χ * r start x c)) ≤
        Real.exp (C * v start) := by
      apply sum_mul_exp_le_exp_variance (K.nonneg x) (K.total x)
        (by simpa using hmean 0 (by omega) x) hb hχ hχb
      · intro c
        simpa using hbound 0 (by omega) x c
      · simpa using hvar 0 (by omega) x
    rw [K.pathReward_mgf_succ]
    calc
      _ ≤ ∑ c, (K.weight x c * Real.exp (χ * r start x c)) *
          Real.exp (C * ∑ i ∈ Finset.range n, v (start + 1 + i)) := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left (htail _) (mul_nonneg (K.nonneg _ _) (Real.exp_pos _).le)
      _ = (∑ c, K.weight x c * Real.exp (χ * r start x c)) *
          Real.exp (C * ∑ i ∈ Finset.range n, v (start + 1 + i)) := by
        rw [Finset.sum_mul]
      _ ≤ Real.exp (C * v start) *
          Real.exp (C * ∑ i ∈ Finset.range n, v (start + 1 + i)) :=
        mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le
      _ = Real.exp (C * ∑ i ∈ Finset.range (n + 1), v (start + i)) := by
        rw [← Real.exp_add, Finset.sum_range_succ']
        congr 1
        simp only [Nat.add_zero]
        have heq : (∑ i ∈ Finset.range n, v (start + (i + 1))) =
            ∑ i ∈ Finset.range n, v (start + 1 + i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          omega
        rw [heq]
        ring

/-- Two-sided Bernstein concentration under the normalized actual path law. -/
theorem pathReward_bernstein (r : ℕ → State → Choice → ℝ) (v : ℕ → ℝ)
    (n : ℕ) (x : State) {b σ s : ℝ}
    (hb : 0 ≤ b) (hσ : 0 < σ) (hs : 0 < s)
    (hmean : ∀ i < n, ∀ y, ∑ c, K.weight y c * r i y c = 0)
    (hbound : ∀ i < n, ∀ y c, |r i y c| ≤ b)
    (hvar : ∀ i < n, ∀ y, ∑ c, K.weight y c * (r i y c) ^ 2 ≤ v i)
    (hbudget : ∑ i ∈ Finset.range n, v i ≤ σ) :
    (∑ p, if Real.sqrt (2 * σ * s) + (2 * b / 3) * s ≤
        |K.pathReward r 0 n x p| then K.pathWeight n x p else 0) ≤
      2 * Real.exp (-s) := by
  classical
  let a : ℝ := Real.sqrt (2 * σ * s) + (2 * b / 3) * s
  let χ : ℝ := a / (σ + b * a / 3)
  let C : ℝ := χ ^ 2 / (2 * (1 - χ * b / 3))
  have ha : 0 < a := bernstein_threshold_pos hb hσ hs
  have hχ : 0 ≤ χ := (bernstein_parameter_pos ha hb hσ).le
  have hχb : χ * b < 3 := bernstein_parameter_mul_lt_three ha.le hb hσ
  have hc : 0 ≤ C := by
    dsimp [C]
    have : 0 < 1 - χ * b / 3 := by linarith
    positivity
  have hmgf (q : ℕ → State → Choice → ℝ)
      (hqmean : ∀ i < n, ∀ y, ∑ c, K.weight y c * q i y c = 0)
      (hqbound : ∀ i < n, ∀ y c, |q i y c| ≤ b)
      (hqvar : ∀ i < n, ∀ y, ∑ c, K.weight y c * (q i y c) ^ 2 ≤ v i) :
      (∑ p, K.pathWeight n x p * Real.exp (χ * K.pathReward q 0 n x p)) ≤
        Real.exp (C * σ) := by
    calc
      _ ≤ Real.exp (C * ∑ i ∈ Finset.range n, v (0 + i)) :=
        K.pathReward_mgf q v 0 n x hb hχ hχb
          (by simpa using hqmean) (by simpa using hqbound) (by simpa using hqvar)
      _ ≤ Real.exp (C * σ) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by simpa using hbudget) hc
  have hpos := hmgf r hmean hbound hvar
  have hneg := hmgf (fun i y c => -r i y c)
    (by
      intro i hi y
      simpa only [mul_neg, Finset.sum_neg_distrib, neg_eq_zero] using hmean i hi y)
    (by simpa only [abs_neg] using hbound)
    (by simpa only [neg_sq] using hvar)
  simp only [K.pathReward_neg] at hneg
  change (∑ p, if a ≤ |K.pathReward r 0 n x p| then K.pathWeight n x p else 0) ≤ _
  calc
    _ ≤ 2 * Real.exp (-χ * a + C * σ) :=
      sum_abs_tail_le_of_mgf (K.pathWeight n x) (K.pathReward r 0 n x)
        (K.pathWeight_nonneg n x) hχ hpos hneg
    _ ≤ 2 * Real.exp (-s) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      exact bernstein_threshold_exponent hb hσ hs

/-- Concentration transferred to an actual terminal event, with its pathwise
connection explicitly required and its transition-operator probability expanded. -/
theorem iterate_bernstein (r : ℕ → State → Choice → ℝ) (v : ℕ → ℝ)
    (n : ℕ) (x : State) (f : State → ℝ) {b σ s : ℝ}
    (hb : 0 ≤ b) (hσ : 0 < σ) (hs : 0 < s)
    (hmean : ∀ i < n, ∀ y, ∑ c, K.weight y c * r i y c = 0)
    (hbound : ∀ i < n, ∀ y c, |r i y c| ≤ b)
    (hvar : ∀ i < n, ∀ y, ∑ c, K.weight y c * (r i y c) ^ 2 ≤ v i)
    (hbudget : ∑ i ∈ Finset.range n, v i ≤ σ)
    (hterminal : ∀ p : ChoicePath Choice n,
      f (K.pathTerminal n x p) = K.pathReward r 0 n x p) :
    K.iterate n (fun y => if Real.sqrt (2 * σ * s) + (2 * b / 3) * s ≤ |f y|
      then 1 else 0) x ≤ 2 * Real.exp (-s) := by
  classical
  rw [K.iterate_eq_pathSum]
  simp only [hterminal, mul_ite, mul_one, mul_zero]
  exact K.pathReward_bernstein r v n x hb hσ hs hmean hbound hvar hbudget

end GraphicalAllocation.Process.FiniteKernel
