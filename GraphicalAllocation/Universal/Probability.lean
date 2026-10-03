import GraphicalAllocation.Transport.Weighted
import GraphicalAllocation.Transport.FiniteLaw

/-!
# Finite probability estimates used by the universal window argument

The two alternatives use an elementary first-moment estimate and the second-
moment method. All masses and moments below are explicit finite weighted sums.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GraphicalAllocation.Universal

open scoped BigOperators
open GraphicalAllocation.Transport

variable {Ω V : Type*} [Fintype Ω]

/-- A finite weighted expectation; weights need not be strictly positive. -/
def mean (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω * f ω

/-- The probability of a predicate under a finite law. -/
def mass (w : Ω → ℝ) (P : Ω → Prop) : ℝ :=
  mean w (fun ω => if P ω then 1 else 0)

@[simp] theorem mean_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (c : ℝ) :
    mean w (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, hw]

theorem mean_nonneg {w f : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean w f := Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (hf ω))

theorem mean_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hfg : ∀ ω, f ω ≤ g ω) : mean w f ≤ mean w g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hw ω))

theorem mean_add (w f g : Ω → ℝ) :
    mean w (fun ω => f ω + g ω) = mean w f + mean w g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_mul (w f : Ω → ℝ) (c : ℝ) :
    mean w (fun ω => c * f ω) = c * mean w f := by
  simp [mean, Finset.mul_sum, mul_left_comm]

theorem mean_sum (w : Ω → ℝ) (I : Finset V) (f : V → Ω → ℝ) :
    mean w (fun ω => ∑ v ∈ I, f v ω) = ∑ v ∈ I, mean w (f v) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (P : Ω → Prop) :
    0 ≤ mass w P := mean_nonneg hw (fun _ => by split_ifs <;> norm_num)

theorem mass_mono {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) : mass w P ≤ mass w Q := by
  apply mean_mono hw
  intro ω
  split_ifs with hp hq <;> simp_all

theorem mass_le_one {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (htotal : ∑ ω, w ω = 1) (P : Ω → Prop) : mass w P ≤ 1 := by
  calc
    _ ≤ mean w (fun _ => 1) := mean_mono hw (fun _ => by split_ifs <;> norm_num)
    _ = 1 := mean_const w htotal 1

/-- Markov's estimate in precisely the form needed for a deeply underloaded vertex. -/
theorem half_mass_of_mean_le {w Z : Ω → ℝ} {τ : ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (hZ : ∀ ω, 0 ≤ Z ω) (hτ : 0 < τ) (hmean : mean w Z ≤ 2 * τ) :
    1 / 2 ≤ mass w (fun ω => Z ω ≤ 4 * τ) := by
  have hpoint : mean w (fun ω => if Z ω ≤ 4 * τ then 0 else 4 * τ) ≤ mean w Z := by
    apply mean_mono hw
    intro ω
    split_ifs with h
    · exact hZ ω
    · exact (lt_of_not_ge h).le
  have hcomp := event_mass_complement w (fun ω => Z ω ≤ 4 * τ)
  rw [htotal] at hcomp
  have heq : mean w (fun ω => if Z ω ≤ 4 * τ then 0 else 4 * τ) =
      (4 * τ) * ∑ ω, w ω * (if Z ω ≤ 4 * τ then 0 else 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp only
    split_ifs <;> ring
  rw [heq] at hpoint
  change (∑ ω, w ω * if Z ω ≤ 4 * τ then 1 else 0) ≥ 1 / 2
  nlinarith

/-- Cauchy--Schwarz restricted to the positive support of a nonnegative variable. -/
theorem mean_sq_le_positive_mass {w Y : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hY : ∀ ω, 0 ≤ Y ω) :
    mean w Y ^ 2 ≤ mass w (fun ω => 0 < Y ω) * mean w (fun ω => Y ω ^ 2) := by
  let w' : Ω → ℝ := fun ω => if 0 < Y ω then w ω else 0
  have hcs := weighted_cauchy_schwarz Finset.univ w' Y (fun ω _ => by
    dsimp [w']
    split_ifs <;> first | exact hw ω | exact le_rfl)
  have hfirst : (∑ ω, w' ω * Y ω) = mean w Y := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [w']
    split_ifs with h
    · rfl
    · have hz : Y ω = 0 := le_antisymm (le_of_not_gt h) (hY ω)
      simp [hz]
  have hsecond : (∑ ω, w' ω * Y ω ^ 2) = mean w (fun ω => Y ω ^ 2) := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [w']
    split_ifs with h
    · rfl
    · have hz : Y ω = 0 := le_antisymm (le_of_not_gt h) (hY ω)
      simp [hz]
  have hmass : (∑ ω, w' ω) = mass w (fun ω => 0 < Y ω) := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp [w']
    split_ifs <;> simp
  rwa [hfirst, hsecond, hmass] at hcs

/-- The second-moment method gives probability one half when `EY≥1` and
`EY²≤EY+(EY)²`. These are proved from edge counts in the application. -/
theorem half_mass_of_second_moment {w Y : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hY : ∀ ω, 0 ≤ Y ω)
    (hfirst : 1 ≤ mean w Y)
    (hsecond : mean w (fun ω => Y ω ^ 2) ≤ mean w Y + mean w Y ^ 2) :
    1 / 2 ≤ mass w (fun ω => 0 < Y ω) := by
  have hp := mass_nonneg hw (fun ω => 0 < Y ω)
  have hcs := mean_sq_le_positive_mass hw hY
  have h2 : mean w Y + mean w Y ^ 2 ≤ 2 * mean w Y ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left (hsecond.trans h2) hp
  nlinarith [sq_pos_of_pos (by linarith : 0 < mean w Y)]

/-- Number of vertices for which a specified event occurs. -/
def countIndicators (I : Finset V) (A : V → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ v ∈ I, if A v ω then 1 else 0

omit [Fintype Ω] in
theorem countIndicators_nonneg (I : Finset V) (A : V → Ω → Prop) (ω : Ω) :
    0 ≤ countIndicators I A ω := by
  apply Finset.sum_nonneg
  intro v hv
  split_ifs <;> norm_num

/-- Exact first moment of a count of events having the same probability. -/
theorem mean_countIndicators (w : Ω → ℝ) (I : Finset V) (A : V → Ω → Prop)
    (q : ℝ) (hfirst : ∀ v ∈ I, mass w (A v) = q) :
    mean w (countIndicators I A) = (I.card : ℝ) * q := by
  change mean w (fun ω => ∑ v ∈ I, if A v ω then 1 else 0) = _
  rw [mean_sum]
  calc
    _ = ∑ _v ∈ I, q := Finset.sum_congr rfl (fun v hv => hfirst v hv)
    _ = _ := by simp

/-- Pairwise negative correlation suffices for the elementary second-moment
bound; no independence of the untouched-vertex events is asserted. -/
theorem second_moment_countIndicators (w : Ω → ℝ) (I : Finset V)
    (A : V → Ω → Prop) (q : ℝ)
    (hfirst : ∀ v ∈ I, mass w (A v) = q)
    (hpair : ∀ u ∈ I, ∀ v ∈ I, u ≠ v →
      mass w (fun ω => A u ω ∧ A v ω) ≤ q ^ 2) :
    mean w (fun ω => countIndicators I A ω ^ 2) ≤
      mean w (countIndicators I A) + mean w (countIndicators I A) ^ 2 := by
  classical
  have hprod (u v : V) :
      mean w (fun ω => (if A u ω then 1 else 0) * (if A v ω then 1 else 0)) =
        mass w (fun ω => A u ω ∧ A v ω) := by
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only
    split_ifs <;> simp_all
  have hsquare : mean w (fun ω => countIndicators I A ω ^ 2) =
      ∑ u ∈ I, ∑ v ∈ I, mass w (fun ω => A u ω ∧ A v ω) := by
    simp only [countIndicators, pow_two, Finset.sum_mul, Finset.mul_sum, mean_sum, hprod]
    exact Finset.sum_comm
  have hb (u : V) (hu : u ∈ I) :
      (∑ v ∈ I, mass w (fun ω => A u ω ∧ A v ω)) ≤ q + (I.card : ℝ) * q ^ 2 := by
    calc
      _ ≤ ∑ v ∈ I, ((if v = u then q else 0) + q ^ 2) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvu : v = u
        · subst v
          simp only [and_self, ↓reduceIte, hfirst u hu]
          exact le_add_of_nonneg_right (sq_nonneg q)
        · simpa [hvu] using hpair u hu v hv (Ne.symm hvu)
      _ = _ := by simp [Finset.sum_add_distrib, hu]
  rw [hsquare, mean_countIndicators w I A q hfirst]
  calc
    _ ≤ ∑ _u ∈ I, (q + (I.card : ℝ) * q ^ 2) := Finset.sum_le_sum hb
    _ = _ := by simp; ring

end GraphicalAllocation.Universal
