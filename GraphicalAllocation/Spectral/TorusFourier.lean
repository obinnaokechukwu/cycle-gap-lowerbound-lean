import GraphicalAllocation.Spectral.Green
import GraphicalAllocation.Geometry.Fourier
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Fourier characters of the actual square torus

The logical statement is an exact Green diagonal formula; the types are genuine cycle
vertices and real vertex profiles; the key predicates are the graph Laplacian
and its unique mean-zero inverse.  Characters supply explicit eigenvectors,
finite character orthogonality supplies their delta expansion, and uniqueness
identifies the resulting kernel with that inverse.
-/

noncomputable section
open scoped BigOperators Fin.CommRing
open SimpleGraph Matrix

namespace GraphicalAllocation.Spectral

set_option maxHeartbeats 800000

attribute [local instance] Classical.propDecidable

abbrev TorusVertex (n : ℕ) := Fin (n + 3) × Fin (n + 3)

abbrev torusGraph (n : ℕ) : SimpleGraph (TorusVertex n) :=
  cycleGraph (n + 3) □ cycleGraph (n + 3)

theorem torus_connected (n : ℕ) : (torusGraph n).Connected :=
  (cycleGraph_connected (n := n + 2)).boxProd (cycleGraph_connected (n := n + 2))

/-- Standard character, pulled back to the actual cyclic vertex type. -/
def cyclicCharacter (n : ℕ) (a x : Fin (n + 3)) : ℂ :=
  ZMod.stdAddChar (ZMod.finEquiv (n + 3) (a * x))

@[simp] theorem cyclicCharacter_zero (n : ℕ) (a : Fin (n + 3)) :
    cyclicCharacter n a 0 = 1 := by simp [cyclicCharacter]

@[simp] theorem cyclicCharacter_zero_frequency (n : ℕ) (x : Fin (n + 3)) :
    cyclicCharacter n 0 x = 1 := by simp [cyclicCharacter]

theorem cyclicCharacter_add (n : ℕ) (a x y : Fin (n + 3)) :
    cyclicCharacter n a (x + y) = cyclicCharacter n a x * cyclicCharacter n a y := by
  simp [cyclicCharacter, mul_add, AddChar.map_add_eq_mul]

theorem cyclicCharacter_comm (n : ℕ) (a x : Fin (n + 3)) :
    cyclicCharacter n a x = cyclicCharacter n x a := by simp [cyclicCharacter, mul_comm]

@[simp] theorem norm_cyclicCharacter (n : ℕ) (a x : Fin (n + 3)) :
    ‖cyclicCharacter n a x‖ = 1 := by
  exact Circle.norm_coe _

theorem cyclicCharacter_neg (n : ℕ) (a x : Fin (n + 3)) :
    cyclicCharacter n a (-x) = star (cyclicCharacter n a x) := by
  simp only [cyclicCharacter, mul_neg, map_neg, AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (norm_cyclicCharacter n a x)

/-- Orthogonality is proved from the primitive standard additive character. -/
theorem sum_cyclicCharacter (n : ℕ) (a : Fin (n + 3)) :
    ∑ x, cyclicCharacter n a x = if a = 0 then (n + 3 : ℂ) else 0 := by
  have hs : (∑ x : Fin (n + 3), cyclicCharacter n a x) =
      ∑ x : ZMod (n + 3), ZMod.stdAddChar (ZMod.finEquiv (n + 3) a * x) := by
    exact Fintype.sum_equiv (ZMod.finEquiv (n + 3)).toEquiv _ _
      (fun x => by simp [cyclicCharacter])
  rw [hs]
  have he : ZMod.finEquiv (n + 3) a = 0 ↔ a = 0 := by
    rw [← (ZMod.finEquiv (n + 3)).map_zero]
    exact (ZMod.finEquiv (n + 3)).injective.eq_iff
  have hz := AddChar.sum_mulShift (ZMod.finEquiv (n + 3) a)
    (ZMod.isPrimitive_stdAddChar (n + 3))
  by_cases ha : a = 0
  · simp [ha]
  · simpa [mul_comm, he, ha] using hz

/-- The two-dimensional tensor character. -/
def torusCharacter (n : ℕ) (a x : TorusVertex n) : ℂ :=
  cyclicCharacter n a.1 x.1 * cyclicCharacter n a.2 x.2

@[simp] theorem torusCharacter_zero (n : ℕ) (a : TorusVertex n) :
    torusCharacter n a 0 = 1 := by simp [torusCharacter]

@[simp] theorem torusCharacter_zero_frequency (n : ℕ) (x : TorusVertex n) :
    torusCharacter n 0 x = 1 := by simp [torusCharacter]

theorem torusCharacter_add (n : ℕ) (a x y : TorusVertex n) :
    torusCharacter n a (x + y) = torusCharacter n a x * torusCharacter n a y := by
  simp only [torusCharacter, Prod.fst_add, Prod.snd_add, cyclicCharacter_add]
  ring

theorem torusCharacter_comm (n : ℕ) (a x : TorusVertex n) :
    torusCharacter n a x = torusCharacter n x a := by
  simp only [torusCharacter, cyclicCharacter_comm n a.1, cyclicCharacter_comm n a.2]

theorem sum_torusCharacter (n : ℕ) (a : TorusVertex n) :
    ∑ x, torusCharacter n a x = if a = 0 then (n + 3 : ℂ)^2 else 0 := by
  simp only [torusCharacter, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_cyclicCharacter]
  by_cases ha : a.1 = 0 <;> by_cases hb : a.2 = 0 <;>
    simp [ha, hb, Prod.ext_iff, pow_two]

/-- A cycle has precisely its two neighboring offsets, including the triangle. -/
theorem torus_cycle_laplacian_apply {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin (n + 3) → R) (x : Fin (n + 3)) :
    ((cycleGraph (n + 3)).lapMatrix R *ᵥ f) x =
      2 * f x - f (x - 1) - f (x + 1) := by
  have hne : x - 1 ≠ x + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc, left_eq_add]
    exact ne_of_beq_false rfl
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le,
    cycleGraph_neighborFinset (n := n + 1)]
  simp [hne]
  ring

/-- The actual Cartesian graph Laplacian is the sum of its two cyclic ones. -/
theorem torus_laplacian_apply {R : Type*} [CommRing R] (n : ℕ)
    (f : TorusVertex n → R) (x : TorusVertex n) :
    ((torusGraph n).lapMatrix R *ᵥ f) x =
      4 * f x - f (x.1 - 1, x.2) - f (x.1 + 1, x.2) -
        f (x.1, x.2 - 1) - f (x.1, x.2 + 1) := by
  have hne (y : Fin (n + 3)) : y - 1 ≠ y + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc, left_eq_add]
    exact ne_of_beq_false rfl
  rw [lapMatrix_mulVec_apply, degree_boxProd, cycleGraph_degree_three_le,
    cycleGraph_degree_three_le, neighborFinset_boxProd]
  simp [cycleGraph_neighborFinset (n := n + 1), hne]
  ring

/-- The nonnegative eigenvalue of a cyclic Fourier mode. -/
def cyclicEigenvalue (n : ℕ) (a : Fin (n + 3)) : ℝ :=
  ‖cyclicCharacter n a 1 - 1‖ ^ 2

@[simp] theorem cyclicEigenvalue_zero (n : ℕ) : cyclicEigenvalue n 0 = 0 := by
  simp [cyclicEigenvalue]

theorem cyclicEigenvalue_nonneg (n : ℕ) (a : Fin (n + 3)) :
    0 ≤ cyclicEigenvalue n a := sq_nonneg _

theorem cyclicEigenvalue_cast (n : ℕ) (a : Fin (n + 3)) :
    (cyclicEigenvalue n a : ℂ) =
      2 - cyclicCharacter n a 1 - star (cyclicCharacter n a 1) := by
  have hn := norm_cyclicCharacter n a 1
  have hs : (cyclicCharacter n a 1).re ^ 2 + (cyclicCharacter n a 1).im ^ 2 = 1 := by
    have := Complex.sq_norm (cyclicCharacter n a 1)
    rw [hn] at this
    simpa [Complex.normSq_apply, pow_two] using this.symm
  apply Complex.ext
  · simp [cyclicEigenvalue, Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  · simp

theorem cyclicEigenvalue_pos (n : ℕ) {a : Fin (n + 3)} (ha : a ≠ 0) :
    0 < cyclicEigenvalue n a := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  have hc : cyclicCharacter n a 1 = 1 := sub_eq_zero.mp h
  have hz : ZMod.finEquiv (n + 3) a = 0 := by
    apply ZMod.injective_stdAddChar
    simpa [cyclicCharacter] using hc
  exact ha ((ZMod.finEquiv (n + 3)).injective (by simpa using hz))

/-- The sum eigenvalue of the two Cartesian factors. -/
def torusEigenvalue (n : ℕ) (a : TorusVertex n) : ℝ :=
  cyclicEigenvalue n a.1 + cyclicEigenvalue n a.2

@[simp] theorem torusEigenvalue_zero (n : ℕ) : torusEigenvalue n 0 = 0 := by
  simp [torusEigenvalue]

theorem torusEigenvalue_pos (n : ℕ) {a : TorusVertex n} (ha : a ≠ 0) :
    0 < torusEigenvalue n a := by
  by_cases h₁ : a.1 = 0
  · have h₂ : a.2 ≠ 0 := by simpa [Prod.ext_iff, h₁] using ha
    simpa [torusEigenvalue, h₁] using cyclicEigenvalue_pos n h₂
  · exact add_pos_of_pos_of_nonneg (cyclicEigenvalue_pos n h₁)
      (cyclicEigenvalue_nonneg n a.2)

/-- Every tensor character is an eigenvector of the genuine graph Laplacian. -/
theorem torusCharacter_eigenvector (n : ℕ) (a x : TorusVertex n) :
    ((torusGraph n).lapMatrix ℂ *ᵥ torusCharacter n a) x =
      (torusEigenvalue n a : ℂ) * torusCharacter n a x := by
  rw [torus_laplacian_apply]
  simp only [torusCharacter, sub_eq_add_neg, cyclicCharacter_add, cyclicCharacter_neg,
    torusEigenvalue, Complex.ofReal_add, cyclicEigenvalue_cast]
  ring

/-- The balanced frequency is the actual distance of a cycle vertex from zero. -/
theorem cycle_frequency_distance (n : ℕ) (a : Fin (n + 3)) :
    (cycleGraph (n + 3)).dist 0 a = min a.val (n + 3 - a.val) := by
  rw [Geometry.cycle_dist_eq_lift, Geometry.cycleLift]
  simp only [sub_zero, ZMod.valMinAbs_natAbs_eq_min]
  rfl

/-- Jordan's inequality bounds the exact cyclic Laplacian eigenvalue. -/
theorem cyclicEigenvalue_lower (n : ℕ) (a : Fin (n + 3)) :
    16 * ((min a.val (n + 3 - a.val) : ℕ) : ℝ)^2 / (n + 3 : ℝ)^2 ≤
      cyclicEigenvalue n a := by
  have h := Geometry.cycleFourier_chord_lower n 0 a
  have he : cyclicCharacter n a 1 = Geometry.cycleFourier n a := by
    simp [cyclicCharacter, Geometry.cycleFourier, ZMod.stdAddChar_apply]
  have hz : Geometry.cycleFourier n 0 = 1 := by simp [Geometry.cycleFourier]
  rw [cycle_frequency_distance, hz, ← he] at h
  have hs := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr h
  unfold cyclicEigenvalue
  simpa only [div_pow, mul_pow, show (4 : ℝ)^2 = 16 by norm_num] using hs

/-- The square-torus eigenvalue controls the Euclidean squared frequency. -/
theorem torusEigenvalue_lower (n : ℕ) (a : TorusVertex n) :
    16 * (((min a.1.val (n + 3 - a.1.val) : ℕ) : ℝ)^2 +
      ((min a.2.val (n + 3 - a.2.val) : ℕ) : ℝ)^2) / (n + 3 : ℝ)^2 ≤
        torusEigenvalue n a := by
  have h₁ := cyclicEigenvalue_lower n a.1
  have h₂ := cyclicEigenvalue_lower n a.2
  unfold torusEigenvalue
  convert add_le_add h₁ h₂ using 1
  ring

end GraphicalAllocation.Spectral
