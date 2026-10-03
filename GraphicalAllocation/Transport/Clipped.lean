import GraphicalAllocation.Rules.Selector
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The actual clipped two-point observable

This module supplies the deterministic content of (5.6), including max-minus-min
Gap and its invariance under common translations. Profiles are integer-valued;
the observable and its finite differences are real-valued.
-/

noncomputable section

namespace GraphicalAllocation.Transport
open Rules

variable {V : Type*} [DecidableEq V]

/-- Projection onto the interval `[-1, 1]`. -/
def clip (a : ℝ) : ℝ := max (-1) (min 1 a)

theorem clip_bounds (a : ℝ) : -1 ≤ clip a ∧ clip a ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_of_mem {a : ℝ} (ha : -1 ≤ a) (hb : a ≤ 1) : clip a = a := by
  simp [clip, min_eq_right hb, max_eq_right ha]

theorem clip_mono : Monotone clip := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl hab)

theorem clip_lipschitz (a b : ℝ) : |clip a - clip b| ≤ |a - b| := by
  calc
    |clip a - clip b| ≤ |min 1 a - min 1 b| := by
      simpa [clip, max_comm] using abs_max_sub_max_le_abs (min 1 a) (min 1 b) (-1 : ℝ)
    _ ≤ |a - b| := by
      simpa using abs_min_sub_min_le_max (1 : ℝ) a 1 b

/-- Bounded, translation-invariant two-point test. -/
def clippedContrast (i j : V) (M : ℝ) (x : Profile V) : ℝ :=
  clip (((x i : ℝ) - (x j : ℝ)) / M)

/-- Discrete directional derivative from adding one ball. -/
def finiteDifference (f : Profile V → ℝ) (x : Profile V) (v : V) : ℝ :=
  f (raise x v) - f x

omit [DecidableEq V] in
theorem clippedContrast_bounds (i j : V) (M : ℝ) (x : Profile V) :
    -1 ≤ clippedContrast i j M x ∧ clippedContrast i j M x ≤ 1 :=
  clip_bounds _

omit [DecidableEq V] in
theorem abs_clippedContrast_le_one (i j : V) (M : ℝ) (x : Profile V) :
    |clippedContrast i j M x| ≤ 1 :=
  abs_le.mpr (clippedContrast_bounds i j M x)

omit [DecidableEq V] in
theorem clippedContrast_sq_le_one (i j : V) (M : ℝ) (x : Profile V) :
    clippedContrast i j M x ^ 2 ≤ 1 := by
  have h := clippedContrast_bounds i j M x
  nlinarith

omit [DecidableEq V] in
theorem clippedContrast_translate (i j : V) (M : ℝ) (x : Profile V) (c : ℤ) :
    clippedContrast i j M (translate x c) = clippedContrast i j M x := by
  simp [clippedContrast, translate]

theorem finiteDifference_off_endpoints (i j v : V) (M : ℝ) (x : Profile V)
    (hi : v ≠ i) (hj : v ≠ j) :
    finiteDifference (clippedContrast i j M) x v = 0 := by
  simp [finiteDifference, clippedContrast, raise, Ne.symm hi, Ne.symm hj]

theorem finiteDifference_first (i j : V) (hij : i ≠ j) {M : ℝ} (hM : 0 < M)
    (x : Profile V) :
    0 ≤ finiteDifference (clippedContrast i j M) x i ∧
      finiteDifference (clippedContrast i j M) x i ≤ 1 / M := by
  have heq : (((raise x i) i : ℝ) - ((raise x i) j : ℝ)) / M =
      ((x i : ℝ) - (x j : ℝ)) / M + 1 / M := by
    simp [raise, Ne.symm hij]
    ring
  unfold finiteDifference clippedContrast
  rw [heq]
  have hnonneg : 0 ≤ (1 : ℝ) / M := le_of_lt (one_div_pos.mpr hM)
  constructor
  · exact sub_nonneg.mpr (clip_mono (le_add_of_nonneg_right hnonneg))
  · have h := clip_lipschitz (((x i : ℝ) - (x j : ℝ)) / M + 1 / M)
        (((x i : ℝ) - (x j : ℝ)) / M)
    simp only [add_sub_cancel_left, abs_of_nonneg hnonneg] at h
    exact (le_abs_self _).trans h

theorem finiteDifference_second (i j : V) (hij : i ≠ j) {M : ℝ} (hM : 0 < M)
    (x : Profile V) :
    -(1 / M) ≤ finiteDifference (clippedContrast i j M) x j ∧
      finiteDifference (clippedContrast i j M) x j ≤ 0 := by
  have heq : (((raise x j) i : ℝ) - ((raise x j) j : ℝ)) / M =
      ((x i : ℝ) - (x j : ℝ)) / M - 1 / M := by
    simp [raise, hij]
    ring
  unfold finiteDifference clippedContrast
  rw [heq]
  have hnonneg : 0 ≤ (1 : ℝ) / M := le_of_lt (one_div_pos.mpr hM)
  constructor
  · have h := clip_lipschitz (((x i : ℝ) - (x j : ℝ)) / M - 1 / M)
        (((x i : ℝ) - (x j : ℝ)) / M)
    simp only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnonneg] at h
    exact (abs_le.mp h).1
  · exact sub_nonpos.mpr (clip_mono (sub_le_self _ hnonneg))

/-- All one-ball changes of the clipped contrast are `1 / M`-bounded. -/
theorem finiteDifference_abs_le (i j v : V) (hij : i ≠ j) {M : ℝ}
    (hM : 0 < M) (x : Profile V) :
    |finiteDifference (clippedContrast i j M) x v| ≤ 1 / M := by
  by_cases hvi : v = i
  · subst v
    have h := finiteDifference_first i j hij hM x
    rw [abs_of_nonneg h.1]
    exact h.2
  · by_cases hvj : v = j
    · subst v
      have h := finiteDifference_second i j hij hM x
      rw [abs_of_nonpos h.2]
      linarith
    · rw [finiteDifference_off_endpoints i j v M x hvi hvj, abs_zero]
      exact le_of_lt (one_div_pos.mpr hM)

section Gap
variable [Fintype V] [Nonempty V]

/-- Maximum integer load. -/
def maxLoad (x : Profile V) : ℤ := Finset.univ.sup' Finset.univ_nonempty x
/-- Minimum integer load. -/
def minLoad (x : Profile V) : ℤ := Finset.univ.inf' Finset.univ_nonempty x
/-- Maximum minus minimum load, represented in the real numbers. -/
def gap (x : Profile V) : ℝ := (maxLoad x : ℝ) - (minLoad x : ℝ)

omit [DecidableEq V] in
theorem load_le_max (x : Profile V) (i : V) : x i ≤ maxLoad x :=
  Finset.le_sup' x (Finset.mem_univ i)

omit [DecidableEq V] in
theorem min_le_load (x : Profile V) (i : V) : minLoad x ≤ x i :=
  Finset.inf'_le x (Finset.mem_univ i)

omit [DecidableEq V] in
theorem difference_le_gap (x : Profile V) (i j : V) :
    (x i : ℝ) - (x j : ℝ) ≤ gap x := by
  have hi : (x i : ℝ) ≤ maxLoad x := by exact_mod_cast load_le_max x i
  have hj : (minLoad x : ℝ) ≤ x j := by exact_mod_cast min_le_load x j
  unfold gap
  linarith

omit [DecidableEq V] in
theorem abs_difference_le_gap (x : Profile V) (i j : V) :
    |(x i : ℝ) - (x j : ℝ)| ≤ gap x := by
  rw [abs_le]
  constructor
  · have := difference_le_gap x j i
    linarith
  · exact difference_le_gap x i j

omit [DecidableEq V] in
theorem gap_nonneg (x : Profile V) : 0 ≤ gap x := by
  obtain ⟨i⟩ := ‹Nonempty V›
  simpa using difference_le_gap x i i

omit [DecidableEq V] in
theorem maxLoad_translate (x : Profile V) (c : ℤ) :
    maxLoad (translate x c) = maxLoad x + c := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    simpa [translate, add_comm] using add_le_add_right (load_le_max x i) c
  · have h : maxLoad x ≤ maxLoad (translate x c) - c := by
      apply Finset.sup'_le
      intro i hi
      have := load_le_max (translate x c) i
      simp only [translate] at this
      omega
    omega

omit [DecidableEq V] in
theorem minLoad_translate (x : Profile V) (c : ℤ) :
    minLoad (translate x c) = minLoad x + c := by
  apply le_antisymm
  · have h : minLoad (translate x c) - c ≤ minLoad x := by
      apply Finset.le_inf'
      intro i hi
      have := min_le_load (translate x c) i
      simp only [translate] at this
      omega
    omega
  · apply Finset.le_inf'
    intro i hi
    simpa [translate, add_comm] using add_le_add_right (min_le_load x i) c

omit [DecidableEq V] in
theorem gap_translate (x : Profile V) (c : ℤ) : gap (translate x c) = gap x := by
  simp [gap, maxLoad_translate, minLoad_translate]

omit [DecidableEq V] in
theorem gap_eq_zero_iff (x : Profile V) : gap x = 0 ↔ ∀ i j, x i = x j := by
  constructor
  · intro h i j
    have hdiff := abs_difference_le_gap x i j
    rw [h] at hdiff
    have : (x i : ℝ) = (x j : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hdiff (abs_nonneg _)))
    exact_mod_cast this
  · intro h
    obtain ⟨i⟩ := ‹Nonempty V›
    have hmax : maxLoad x ≤ x i := by
      apply Finset.sup'_le
      intro j hj
      rw [h j i]
    have hmin : x i ≤ minLoad x := by
      apply Finset.le_inf'
      intro j hj
      rw [h i j]
    have heq : maxLoad x = minLoad x := by
      exact le_antisymm (hmax.trans hmin) ((min_le_load x i).trans (load_le_max x i))
    simp [gap, heq]

omit [DecidableEq V] in
/-- Integer loads make every nonzero gap at least one. -/
theorem gap_zero_or_one_le (x : Profile V) : gap x = 0 ∨ 1 ≤ gap x := by
  obtain ⟨i⟩ := ‹Nonempty V›
  have horder : minLoad x ≤ maxLoad x := (min_le_load x i).trans (load_le_max x i)
  by_cases heq : maxLoad x = minLoad x
  · left
    simp [gap, heq]
  · right
    have hint : (1 : ℤ) ≤ maxLoad x - minLoad x := by omega
    have : (1 : ℝ) ≤ ((maxLoad x - minLoad x : ℤ) : ℝ) := by exact_mod_cast hint
    simpa [gap] using this

omit [DecidableEq V] in
theorem one_le_gap_of_nonflat (x : Profile V) (h : ¬∀ i j, x i = x j) :
    1 ≤ gap x := by
  rcases gap_zero_or_one_le x with hz | hp
  · exact (h ((gap_eq_zero_iff x).mp hz)).elim
  · exact hp

/-- Exact unsaturated positive endpoint derivative on the good-gap event. -/
theorem finiteDifference_first_of_gap (i j : V) (hij : i ≠ j)
    {M : ℝ} (hM : 1 ≤ M) (x : Profile V) (hx : gap x ≤ M - 1) :
    finiteDifference (clippedContrast i j M) x i = 1 / M := by
  have hMpos : 0 < M := by linarith
  have hd := abs_le.mp ((abs_difference_le_gap x i j).trans hx)
  have hlow : -1 ≤ ((x i : ℝ) - (x j : ℝ)) / M := by
    apply (le_div_iff₀ hMpos).2
    linarith
  have hhigh : ((x i : ℝ) - (x j : ℝ)) / M ≤ 1 := by
    apply (div_le_iff₀ hMpos).2
    linarith
  have hlow' : -1 ≤ ((x i : ℝ) + 1 - (x j : ℝ)) / M := by
    apply (le_div_iff₀ hMpos).2
    linarith
  have hhigh' : ((x i : ℝ) + 1 - (x j : ℝ)) / M ≤ 1 := by
    apply (div_le_iff₀ hMpos).2
    linarith
  simp only [finiteDifference, clippedContrast, raise_self, raise_other x (Ne.symm hij),
    Int.cast_add, Int.cast_one]
  rw [clip_of_mem hlow' hhigh', clip_of_mem hlow hhigh]
  ring

/-- The positive endpoint half of (5.6), including the bad-gap case. -/
theorem finiteDifference_first_lower (i j : V) (hij : i ≠ j)
    {M : ℝ} (hM : 1 ≤ M) (x : Profile V) :
    (if gap x ≤ M - 1 then 1 / M else 0) ≤
      finiteDifference (clippedContrast i j M) x i := by
  split_ifs with hx
  · exact (finiteDifference_first_of_gap i j hij hM x hx).ge
  · exact (finiteDifference_first i j hij (by linarith) x).1

end Gap
end GraphicalAllocation.Transport
