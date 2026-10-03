import GraphicalAllocation.Process.FinitePaths
import GraphicalAllocation.Universal.Probability
import Mathlib.Tactic

/-!
# Independent uniform edge windows

The window is a finite product of actual edge labels. Its product weights and
normalization are explicit. The number of hits and the probability of avoiding
an arbitrary edge set are calculated directly; strategy choices do not appear.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped BigOperators
open Process

variable {E : Type*} [Fintype E] [Nonempty E]

/-- The product law of `h` independent uniform arrival labels. -/
def edgePathWeight (h : ℕ) (_p : ChoicePath E h) : ℝ :=
  (1 / (Fintype.card E : ℝ)) ^ h

theorem edgePathWeight_nonneg (h : ℕ) (p : ChoicePath E h) :
    0 ≤ edgePathWeight h p := by unfold edgePathWeight; positivity

omit [Nonempty E] in
/-- The first-edge / remaining-window factorization of the product law. -/
theorem edge_mean_succ (h : ℕ) (f : ChoicePath E (h + 1) → ℝ) :
    mean (edgePathWeight (E := E) (h + 1)) f =
      ∑ e : E, (1 / (Fintype.card E : ℝ)) *
        mean (edgePathWeight h) (fun p => f (e, p)) := by
  change (∑ p : E × ChoicePath E h, _ * f p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mean, edgePathWeight, Finset.mul_sum, pow_succ]
  apply Finset.sum_congr rfl
  intro p _
  ring

@[simp] theorem edgePathWeight_total (h : ℕ) :
    ∑ p : ChoicePath E h, edgePathWeight h p = 1 := by
  induction h with
  | zero => change (∑ _ : PUnit, (1 : ℝ)) = 1; simp
  | succ h ih =>
    have hm := edge_mean_succ (E := E) h (fun _ => 1)
    simp only [mean, mul_one] at hm
    rw [hm]
    simp only [ih, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero (α := E))

/-- Number of arrivals in a selected set of edge labels. -/
def hitCount (B : Finset E) : (h : ℕ) → ChoicePath E h → ℕ
  | 0, _ => 0
  | h + 1, p => (if p.1 ∈ B then 1 else 0) + hitCount B h p.2

/-- No edge from `B` arrives anywhere in the window. -/
def Avoids (B : Finset E) (h : ℕ) (p : ChoicePath E h) : Prop :=
  hitCount B h p = 0

omit [Fintype E] [Nonempty E] in
@[simp] theorem avoids_zero (B : Finset E) (p : ChoicePath E 0) : Avoids B 0 p := rfl

omit [Fintype E] [Nonempty E] in
@[simp] theorem avoids_succ (B : Finset E) (h : ℕ) (e : E) (p : ChoicePath E h) :
    Avoids B (h + 1) (e, p) ↔ e ∉ B ∧ Avoids B h p := by
  simp [Avoids, hitCount]

/-- The expected number of hits is window length times the one-draw mass. -/
theorem mean_hitCount (B : Finset E) (h : ℕ) :
    mean (edgePathWeight (E := E) h) (fun p => (hitCount B h p : ℝ)) =
      h * ((B.card : ℝ) / Fintype.card E) := by
  induction h with
  | zero => simp [mean, edgePathWeight, hitCount]
  | succ h ih =>
    rw [edge_mean_succ]
    have he (e : E) :
        mean (edgePathWeight h) (fun p => (hitCount B (h + 1) (e, p) : ℝ)) =
        (if e ∈ B then 1 else 0) + h * ((B.card : ℝ) / Fintype.card E) := by
      simp only [hitCount, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [mean_add, mean_const _ (edgePathWeight_total h), ih]
    simp_rw [he, mul_add]
    rw [Finset.sum_add_distrib]
    have hb : (∑ e : E, (1 / (Fintype.card E : ℝ)) * (if e ∈ B then 1 else 0)) =
        (B.card : ℝ) / Fintype.card E := by
      simp [mul_ite, Finset.sum_ite_mem, div_eq_mul_inv, mul_comm]
    rw [hb]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hcard : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
    field_simp
    ring

/-- The untouched probability is the exact independent-product expression. -/
theorem mass_avoids (B : Finset E) (h : ℕ) :
    mass (edgePathWeight (E := E) h) (Avoids B h) =
      (1 - (B.card : ℝ) / Fintype.card E) ^ h := by
  induction h with
  | zero =>
    simp only [mass, Avoids, hitCount, ↓reduceIte, pow_zero]
    exact mean_const _ (edgePathWeight_total 0) 1
  | succ h ih =>
    unfold mass at ih ⊢
    rw [edge_mean_succ]
    have he (e : E) :
        mean (edgePathWeight h) (fun p => if Avoids B (h + 1) (e, p) then 1 else 0) =
        (if e ∈ B then 0 else 1) * (1 - (B.card : ℝ) / Fintype.card E) ^ h := by
      by_cases he : e ∈ B
      · simp [he, mean, avoids_succ]
      · simp only [avoids_succ, he, not_false_eq_true, true_and, ↓reduceIte, one_mul]
        exact ih
    simp_rw [he, ← mul_assoc]
    rw [← Finset.sum_mul, pow_succ]
    have hb : (∑ e : E, (1 / (Fintype.card E : ℝ)) * (if e ∈ B then 0 else 1)) =
        1 - (B.card : ℝ) / Fintype.card E := by
      have hc := Transport.event_mass_complement
        (fun _ : E => 1 / (Fintype.card E : ℝ)) (fun e => e ∈ B)
      have hcard : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := E)
      simp [mul_ite, Finset.sum_ite_mem, div_eq_mul_inv, mul_comm, hcard] at hc ⊢
      linarith
    rw [hb]
    ring

omit [Fintype E] [Nonempty E] in
/-- Simultaneous avoidance is avoidance of the union of the edge sets. -/
theorem avoids_union [DecidableEq E] (B C : Finset E) (h : ℕ) (p : ChoicePath E h) :
    Avoids (B ∪ C) h p ↔ Avoids B h p ∧ Avoids C h p := by
  induction h with
  | zero => simp
  | succ h ih =>
    rcases p with ⟨e, p⟩
    simp only [avoids_succ, Finset.mem_union, not_or, ih]
    tauto

end GraphicalAllocation.Universal
