import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs

/-!
# Finite selection-cell resampling

A finite positive weighted mark space suffices after refining the finitely many
thresholds encountered along a fixed finite allocation path.  The definitions
below are literal weighted conditional probabilities; no projection property or
Palm identity is assumed.
-/

noncomputable section

namespace GraphicalAllocation.Palm

open scoped BigOperators

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

/-- Unnormalized mass of a selection cell. -/
def cellMass (μ : A → ℝ) (p : A → B) (b : B) : ℝ :=
  ∑ a, if p a = b then μ a else 0

/-- Resample the mark from its current cell, using the original atom weights. -/
def cellKernel (μ : A → ℝ) (p : A → B) (a b : A) : ℝ :=
  if p b = p a then μ b / cellMass μ p (p a) else 0

omit [DecidableEq A] in
lemma cellMass_nonneg {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (p : A → B) (b : B) :
    0 ≤ cellMass μ p b := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> simp_all

omit [DecidableEq A] in
lemma atom_le_cellMass {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (p : A → B) (a : A) :
    μ a ≤ cellMass μ p (p a) := by
  calc
    μ a = (if p a = p a then μ a else 0) := by simp
    _ ≤ ∑ b, if p b = p a then μ b else 0 := by
      exact Finset.single_le_sum (f := fun b => if p b = p a then μ b else 0)
        (fun b _ => by split_ifs <;> simp_all) (Finset.mem_univ a)

omit [DecidableEq A] in
lemma cellMass_pos {μ : A → ℝ} (hμ : ∀ a, 0 < μ a) (p : A → B) (a : A) :
    0 < cellMass μ p (p a) :=
  lt_of_lt_of_le (hμ a) (atom_le_cellMass (fun a => (hμ a).le) p a)

omit [DecidableEq A] in
lemma cellKernel_nonneg {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a) (p : A → B) (a b : A) :
    0 ≤ cellKernel μ p a b := by
  unfold cellKernel
  split_ifs
  · exact div_nonneg (hμ b) (cellMass_nonneg hμ p _)
  · exact le_rfl

omit [DecidableEq A] in
lemma cellKernel_row_sum {μ : A → ℝ} (hμ : ∀ a, 0 < μ a) (p : A → B) (a : A) :
    ∑ b, cellKernel μ p a b = 1 := by
  have hm : cellMass μ p (p a) ≠ 0 := ne_of_gt (cellMass_pos hμ p a)
  calc
    ∑ b, cellKernel μ p a b =
        (∑ b, if p b = p a then μ b else 0) / cellMass μ p (p a) := by
      simp [cellKernel, Finset.sum_div, ite_div]
    _ = 1 := div_self hm

omit [DecidableEq A] in
lemma cellKernel_same_cell (μ : A → ℝ) (p : A → B) {a b : A}
    (hab : p a = p b) (c : A) : cellKernel μ p a c = cellKernel μ p b c := by
  simp [cellKernel, hab]

omit [DecidableEq A] in
/-- Detailed balance, the finite weighted form of self-adjointness. -/
lemma cellKernel_detailed_balance (μ : A → ℝ) (p : A → B) (a b : A) :
    μ a * cellKernel μ p a b = μ b * cellKernel μ p b a := by
  by_cases h : p b = p a
  · simp only [cellKernel, h, ite_true]
    ring
  · have h' : p a ≠ p b := Ne.symm h
    simp [cellKernel, h, h']

omit [DecidableEq A] in
/-- The original mark distribution is invariant under cell resampling. -/
lemma cellKernel_stationary {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (b : A) :
    ∑ a, μ a * cellKernel μ p a b = μ b := by
  simp_rw [cellKernel_detailed_balance μ p]
  rw [← Finset.mul_sum, cellKernel_row_sum hμ]
  simp

omit [DecidableEq A] in
/-- Resampling twice from one partition is the same as resampling once. -/
lemma cellKernel_idempotent {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (a b : A) :
    ∑ c, cellKernel μ p a c * cellKernel μ p c b = cellKernel μ p a b := by
  calc
    ∑ c, cellKernel μ p a c * cellKernel μ p c b =
        ∑ c, cellKernel μ p a c * cellKernel μ p a b := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : p c = p a
      · rw [cellKernel_same_cell μ p h]
      · simp [cellKernel, h]
    _ = (∑ c, cellKernel μ p a c) * cellKernel μ p a b := by
      rw [Finset.sum_mul]
    _ = cellKernel μ p a b := by rw [cellKernel_row_sum hμ]; simp

/-- The cell-average operator acting on real observables. -/
def cellAverage (μ : A → ℝ) (p : A → B) (f : A → ℝ) (a : A) : ℝ :=
  ∑ b, cellKernel μ p a b * f b

omit [DecidableEq A] in
lemma cellAverage_idempotent {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (f : A → ℝ) :
    cellAverage μ p (cellAverage μ p f) = cellAverage μ p f := by
  funext a
  simp only [cellAverage, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, cellKernel_idempotent hμ]

omit [DecidableEq A] in
/-- Weighted self-adjointness of the actual conditional-average operator. -/
lemma cellAverage_selfAdjoint (μ : A → ℝ) (p : A → B) (f g : A → ℝ) :
    (∑ a, μ a * f a * cellAverage μ p g a) =
      ∑ a, μ a * cellAverage μ p f a * g a := by
  simp only [cellAverage, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    μ b * f b * (cellKernel μ p b a * g a) =
      (μ b * cellKernel μ p b a) * f b * g a := by ring
    _ = (μ a * cellKernel μ p a b) * f b * g a := by
      rw [cellKernel_detailed_balance]
    _ = μ a * (cellKernel μ p a b * f b) * g a := by ring

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm

open scoped BigOperators

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

/-- A local partition remembers the selected vertex on active cells and the
exact mark everywhere else. Its cell resampling therefore fixes every inactive
mark pointwise. -/
def localKey (p : A → B) (S : Finset B) (a : A) : Sum B A :=
  if p a ∈ S then Sum.inl (p a) else Sum.inr a

omit [Fintype A] [DecidableEq A] in
lemma localKey_eq_of_active (p : A → B) (S : Finset B) {a : A}
    (ha : p a ∈ S) (b : A) :
    localKey p S b = localKey p S a ↔ p b = p a := by
  simp only [localKey, ha, ite_true]
  by_cases hb : p b ∈ S
  · simp [hb]
  · simp only [hb, ite_false, Sum.inr_ne_inl, false_iff]
    intro h
    exact hb (h ▸ ha)

omit [Fintype A] [DecidableEq A] in
lemma localKey_eq_of_inactive (p : A → B) (S : Finset B) {a : A}
    (ha : p a ∉ S) (b : A) :
    localKey p S b = localKey p S a ↔ b = a := by
  simp only [localKey, ha, ite_false]
  by_cases hb : p b ∈ S
  · simp only [hb, ite_true, Sum.inl_ne_inr, false_iff]
    intro h
    exact ha (h ▸ hb)
  · simp [hb]

lemma cellMass_localKey_active (μ : A → ℝ) (p : A → B) (S : Finset B)
    {a : A} (ha : p a ∈ S) :
    cellMass μ (localKey p S) (localKey p S a) = cellMass μ p (p a) := by
  simp only [cellMass, localKey_eq_of_active p S ha]

lemma cellMass_localKey_inactive (μ : A → ℝ) (p : A → B) (S : Finset B)
    {a : A} (ha : p a ∉ S) :
    cellMass μ (localKey p S) (localKey p S a) = μ a := by
  simp [cellMass, localKey_eq_of_inactive p S ha]

lemma cellKernel_localKey_active (μ : A → ℝ) (p : A → B) (S : Finset B)
    {a : A} (ha : p a ∈ S) (b : A) :
    cellKernel μ (localKey p S) a b = cellKernel μ p a b := by
  simp only [cellKernel, localKey_eq_of_active p S ha,
    cellMass_localKey_active μ p S ha]

lemma cellKernel_localKey_inactive {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (S : Finset B) {a : A} (ha : p a ∉ S) (b : A) :
    cellKernel μ (localKey p S) a b = if b = a then 1 else 0 := by
  simp only [cellKernel, localKey_eq_of_inactive p S ha,
    cellMass_localKey_inactive μ p S ha]
  split_ifs with h
  · subst b
    exact div_self (ne_of_gt (hμ a))
  · rfl

/-- The only-changing-old-cell property supplied by endpoint monotonicity. -/
def ChangesOnlyFrom (old new : A → B) (j : B) : Prop :=
  ∀ a, old a ≠ j → new a = old a

/-- Mass shared by an old and a new selection cell. -/
def overlap (μ : A → ℝ) (old new : A → B) (i j : B) : ℝ :=
  ∑ a, if old a = i ∧ new a = j then μ a else 0

omit [DecidableEq A] in
lemma overlap_nonneg {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) (i j : B) :
    0 ≤ overlap μ old new i j := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> simp_all

omit [DecidableEq A] in
lemma overlap_le_oldMass {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) (i j : B) :
    overlap μ old new i j ≤ cellMass μ old i := by
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp_all

omit [DecidableEq A] in
lemma overlap_eq_zero_of_oldMass_eq_zero {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) {i : B} (hi : cellMass μ old i = 0) (j : B) :
    overlap μ old new i j = 0 := by
  apply le_antisymm
  · simpa [hi] using overlap_le_oldMass hμ old new i j
  · exact overlap_nonneg hμ old new i j

omit [DecidableEq A] in
lemma overlap_row_sum [Fintype B] (μ : A → ℝ) (old new : A → B) (i : B) :
    ∑ j, overlap μ old new i j = cellMass μ old i := by
  unfold overlap cellMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : old a = i <;> simp [h]

omit [DecidableEq A] in
lemma overlap_col_sum [Fintype B] (μ : A → ℝ) (old new : A → B) (j : B) :
    ∑ i, overlap μ old new i j = cellMass μ new j := by
  unfold overlap cellMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : new a = j <;> simp [h]

omit [DecidableEq A] in
lemma overlap_of_not_selected (μ : A → ℝ) {old new : A → B} {j : B}
    (hchange : ChangesOnlyFrom old new j) {i : B} (hi : i ≠ j) (k : B) :
    overlap μ old new i k = if i = k then cellMass μ old i else 0 := by
  unfold overlap cellMass
  by_cases hik : i = k
  · subst k
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : old a = i
    · have hn : new a = i := (hchange a (ha ▸ hi)).trans ha
      simp [ha, hn]
    · simp [ha]
  · simp only [hik, ite_false]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : old a = i
    · have hn : new a = i := (hchange a (ha ▸ hi)).trans ha
      simp [ha, hn, hik]
    · simp [ha]

/-- The transition law obtained by reading the new cell of an old-cell-uniform
mark. Empty old cells are assigned a harmless identity row. -/
def tagKernel (μ : A → ℝ) (old new : A → B) (i j : B) : ℝ :=
  if cellMass μ old i = 0 then (if i = j then 1 else 0)
  else overlap μ old new i j / cellMass μ old i

omit [DecidableEq A] in
lemma weighted_tagKernel {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) (i j : B) :
    cellMass μ old i * tagKernel μ old new i j = overlap μ old new i j := by
  by_cases hi : cellMass μ old i = 0
  · simp [tagKernel, hi, overlap_eq_zero_of_oldMass_eq_zero hμ old new hi j]
  · simp only [tagKernel, hi, ite_false]
    field_simp

omit [DecidableEq A] in
lemma tagKernel_nonneg {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) (i j : B) :
    0 ≤ tagKernel μ old new i j := by
  unfold tagKernel
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (overlap_nonneg hμ old new i j) (cellMass_nonneg hμ old i)

omit [DecidableEq A] in
lemma tagKernel_row_sum [Fintype B] (μ : A → ℝ) (old new : A → B) (i : B) :
    ∑ j, tagKernel μ old new i j = 1 := by
  by_cases hi : cellMass μ old i = 0
  · simp [tagKernel, hi]
  · simp only [tagKernel, hi, ite_false, ← Finset.sum_div, overlap_row_sum]
    exact div_self hi

omit [DecidableEq A] in
/-- The one-step rate-biased Palm identity, including null selection cells. -/
lemma palm_one_step [Fintype B] {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → B) (j : B) :
    ∑ i, cellMass μ old i * tagKernel μ old new i j = cellMass μ new j := by
  simp_rw [weighted_tagKernel hμ]
  exact overlap_col_sum μ old new j

omit [DecidableEq A] in
/-- Tags away from the selected base vertex stay put. -/
lemma tagKernel_of_not_selected (μ : A → ℝ) {old new : A → B} {j : B}
    (hchange : ChangesOnlyFrom old new j) {i : B} (hi : i ≠ j) (k : B) :
    tagKernel μ old new i k = if i = k then 1 else 0 := by
  by_cases hm : cellMass μ old i = 0
  · simp [tagKernel, hm]
  · simp only [tagKernel, hm, ite_false, overlap_of_not_selected μ hchange hi]
    split_ifs
    · exact div_self hm
    · exact zero_div _

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm

open scoped BigOperators

variable {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] in
lemma cellKernel_eq_reverse_denominator (μ : A → ℝ) (p : A → B) (a b : A) :
    cellKernel μ p a b = if p a = p b then μ b / cellMass μ p (p b) else 0 := by
  by_cases h : p a = p b
  · simp [cellKernel, h]
  · simp [cellKernel, h, Ne.symm h]

lemma cellKernel_localKey_into_active (μ : A → ℝ) (p : A → B) (S : Finset B)
    {b : A} (hb : p b ∈ S) (a : A) :
    cellKernel μ (localKey p S) a b = cellKernel μ p a b := by
  rw [cellKernel_eq_reverse_denominator, cellKernel_eq_reverse_denominator]
  simp only [localKey_eq_of_active p S hb,
    cellMass_localKey_active μ p S hb]

lemma cellKernel_localKey_into_inactive {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → B) (S : Finset B) {b : A} (hb : p b ∉ S) (a : A) :
    cellKernel μ (localKey p S) a b = if a = b then 1 else 0 := by
  rw [cellKernel_eq_reverse_denominator]
  simp only [localKey_eq_of_inactive p S hb,
    cellMass_localKey_inactive μ p S hb]
  split_ifs <;> simp_all [ne_of_gt (hμ b)]

omit [DecidableEq A] in
lemma oldCell_cellKernel (μ : A → ℝ) (old new : A → B) (i : B) (b : A) :
    (∑ a, (if old a = i then μ a else 0) * cellKernel μ new a b) =
      overlap μ old new i (new b) * (μ b / cellMass μ new (new b)) := by
  unfold overlap
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [cellKernel_eq_reverse_denominator]
  by_cases hi : old a = i <;> by_cases hn : new a = new b <;> simp [hi, hn]

omit [DecidableEq A] in
lemma overlap_of_unchanged_new_cell (μ : A → ℝ) (old new : A → B) (i k : B)
    (h : ∀ a, new a = k → old a = new a) :
    overlap μ old new i k = if i = k then cellMass μ new k else 0 := by
  unfold overlap cellMass
  by_cases hik : i = k
  · subst i
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hn : new a = k
    · have ho : old a = k := (h a hn).trans hn
      simp [ho, hn]
    · simp [hn]
  · simp only [hik, ite_false]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hn : new a = k
    · have ho : old a = k := (h a hn).trans hn
      simp [ho, hn, Ne.symm hik]
    · simp [hn]

/-- Exact conditional-cell intertwining for the local auxiliary kernel.
It expresses preservation of the cell-uniform conditional distribution after
reading the new tag and resampling, and is the induction step of the marked
Palm representation. -/
lemma oldCell_localKernel {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (old new : A → B) (S : Finset B)
    (houtside : ∀ a, new a ∉ S → old a = new a) (i : B) (b : A) :
    (∑ a, (if old a = i then μ a else 0) * cellKernel μ (localKey new S) a b) =
      overlap μ old new i (new b) * (μ b / cellMass μ new (new b)) := by
  by_cases hb : new b ∈ S
  · simp_rw [cellKernel_localKey_into_active μ new S hb]
    exact oldCell_cellKernel μ old new i b
  · simp_rw [cellKernel_localKey_into_inactive hμ new S hb]
    rw [overlap_of_unchanged_new_cell μ old new i (new b)
      (fun a ha => houtside a (ha ▸ hb))]
    have ho : old b = new b := houtside b hb
    have hm : cellMass μ new (new b) ≠ 0 := ne_of_gt (cellMass_pos hμ new b)
    by_cases hi : i = new b
    · simp only [hi, ite_true]
      simp [ho, hm, mul_div_cancel₀]
    · simp [ho, hi, Ne.symm hi]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open scoped BigOperators
variable {A V : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]

/-- The actual hidden event mark conditioned on selecting base vertex `j`. -/
def conditionedEventWeight (μ : A → ℝ) (old : A → V) (j : V) (a : A) : ℝ :=
  if old a = j then μ a / cellMass μ old j else 0

omit [DecidableEq A] in
lemma conditionedEventWeight_sum (μ : A → ℝ) (old : A → V) (j : V)
    (hj : cellMass μ old j ≠ 0) :
    ∑ a, conditionedEventWeight μ old j a = 1 := by
  calc
    _ = cellMass μ old j / cellMass μ old j := by
      simp [conditionedEventWeight, cellMass, Finset.sum_div, ite_div]
    _ = 1 := div_self hj

/-- The synchronous discrepancy transition given a selected base vertex. -/
def conditionedDiscrepancyKernel (μ : A → ℝ) (old new : A → V)
    (j i k : V) : ℝ :=
  ∑ a, conditionedEventWeight μ old j a *
    (if (if i = j then new a else i) = k then 1 else 0)

omit [DecidableEq A] in
/-- The actual conditioned hidden event yields exactly the overlap tag kernel.
Only a positive-probability base selection is conditioned upon. -/
lemma conditionedDiscrepancyKernel_eq (μ : A → ℝ) (old new : A → V) (j : V)
    (hj : cellMass μ old j ≠ 0) (hchange : ChangesOnlyFrom old new j) (i k : V) :
    conditionedDiscrepancyKernel μ old new j i k = tagKernel μ old new i k := by
  by_cases hi : i = j
  · subst i
    simp only [conditionedDiscrepancyKernel, ite_true, tagKernel, hj, ite_false]
    unfold overlap
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ho : old a = j <;> by_cases hn : new a = k <;>
      simp [conditionedEventWeight, ho, hn]
  · rw [tagKernel_of_not_selected μ hchange hi]
    simp only [conditionedDiscrepancyKernel, hi, ite_false]
    rw [← Finset.sum_mul, conditionedEventWeight_sum μ old j hj, one_mul]

end GraphicalAllocation.Palm
