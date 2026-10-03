import GraphicalAllocation.Palm.Path

/-! # Exact finite conditional mark representation

The local mark chain and the cell-overlap tag chain are defined independently.
The representation theorem below proves their equality after every finite number
of updates, including the cell-uniform conditional-density invariant.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

/-- A vertex distribution is supported on non-null selection cells. -/
def CellSupported (μ : A → ℝ) (p : A → V) (d : V → ℝ) : Prop :=
  ∀ v, cellMass μ p v = 0 → d v = 0

/-- Lift a vertex distribution by making its mark conditionally uniform in each cell. -/
def cellLift (μ : A → ℝ) (p : A → V) (d : V → ℝ) (a : A) : ℝ :=
  d (p a) / cellMass μ p (p a) * μ a

/-- Push a vertex distribution through the explicit cell-overlap kernel. -/
def tagPush (μ : A → ℝ) (old new : A → V) (d : V → ℝ) (j : V) : ℝ :=
  ∑ i, d i * tagKernel μ old new i j

omit [DecidableEq A] [Fintype V] in
lemma overlap_le_newMass {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → V) (i j : V) :
    overlap μ old new i j ≤ cellMass μ new j := by
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp_all

omit [DecidableEq A] [Fintype V] in
lemma overlap_eq_zero_of_newMass_eq_zero {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → V) (i j : V) (hj : cellMass μ new j = 0) :
    overlap μ old new i j = 0 := by
  exact le_antisymm (by simpa [hj] using overlap_le_newMass hμ old new i j)
    (overlap_nonneg hμ old new i j)

omit [DecidableEq A] [Fintype V] in
lemma supported_mul_tagKernel (μ : A → ℝ) (old new : A → V) (d : V → ℝ)
    (hd : CellSupported μ old d) (i j : V) :
    d i * tagKernel μ old new i j = d i / cellMass μ old i * overlap μ old new i j := by
  by_cases hi : cellMass μ old i = 0
  · simp [hd i hi]
  · simp only [tagKernel, hi, ite_false]
    ring

omit [DecidableEq A] in
lemma tagPush_supported {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (old new : A → V) (d : V → ℝ) (hd : CellSupported μ old d) :
    CellSupported μ new (tagPush μ old new d) := by
  intro j hj
  unfold tagPush
  apply Finset.sum_eq_zero
  intro i _
  rw [supported_mul_tagKernel μ old new d hd,
    overlap_eq_zero_of_newMass_eq_zero hμ old new i j hj, mul_zero]

omit [DecidableEq A] in
lemma cellLift_expand (μ : A → ℝ) (p : A → V) (d : V → ℝ) (a : A) :
    cellLift μ p d a = ∑ i, d i / cellMass μ p i * (if p a = i then μ a else 0) := by
  simp [cellLift, mul_ite]

/-- Exact one-step intertwining: resampling the local auxiliary mark preserves
the uniform-in-cell invariant and induces the true tag transition. -/
lemma cellLift_localKernel {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (old new : A → V) (S : Finset V)
    (houtside : ∀ a, new a ∉ S → old a = new a)
    (d : V → ℝ) (hd : CellSupported μ old d) (b : A) :
    (∑ a, cellLift μ old d a * cellKernel μ (localKey new S) a b) =
      cellLift μ new (tagPush μ old new d) b := by
  simp_rw [cellLift_expand μ old d, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, oldCell_localKernel hμ old new S houtside]
  unfold cellLift tagPush
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [supported_mul_tagKernel μ old new d hd]
  ring

omit [DecidableEq A] [Fintype V] in
lemma cellLift_cellMass (μ : A → ℝ) (p : A → V) (d : V → ℝ)
    (hd : CellSupported μ p d) (j : V) :
    (∑ a, if p a = j then cellLift μ p d a else 0) = d j := by
  have heq : (∑ a, if p a = j then cellLift μ p d a else 0) =
      d j / cellMass μ p j * cellMass μ p j := by
    unfold cellMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : p a = j <;> simp [cellLift, cellMass, ha]
  rw [heq]
  by_cases hj : cellMass μ p j = 0
  · simp [hj, hd j hj]
  · exact div_mul_cancel₀ _ hj

/-- The finite tag distribution, defined by chronological transitions. -/
def tagDistribution (μ : A → ℝ) (p : ℕ → A → V) (d : V → ℝ) : ℕ → V → ℝ
  | 0 => d
  | n + 1 => tagPush μ (p n) (p (n + 1)) (tagDistribution μ p d n)

/-- The finite auxiliary-mark distribution, defined separately from the tag chain. -/
def markDistribution (μ : A → ℝ) (p : ℕ → A → V) (S : ℕ → Finset V)
    (d : V → ℝ) : ℕ → A → ℝ
  | 0 => cellLift μ (p 0) d
  | n + 1 => fun b => ∑ a, markDistribution μ p S d n a *
      cellKernel μ (localKey (p (n + 1)) (S n)) a b

omit [DecidableEq A] in
lemma tagDistribution_supported {μ : A → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (p : ℕ → A → V) (d : V → ℝ) (hd : CellSupported μ (p 0) d) (n : ℕ) :
    CellSupported μ (p n) (tagDistribution μ p d n) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact tagPush_supported hμ _ _ _ ih

/-- The conditional mark representation at every finite event count. -/
lemma markDistribution_eq_cellLift {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → V) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (d : V → ℝ) (hd : CellSupported μ (p 0) d) (n : ℕ) :
    markDistribution μ p S d n = cellLift μ (p n) (tagDistribution μ p d n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext b
    simp only [markDistribution, ih]
    exact cellLift_localKernel hμ _ _ _ (houtside n) _
      (tagDistribution_supported (fun a => (hμ a).le) p d hd n) b

/-- Reading the selected vertex from the auxiliary mark gives exactly the tag
law. The initial vertex law may be arbitrary on its non-null cells. -/
lemma markDistribution_reads_tag {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → V) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (d : V → ℝ) (hd : CellSupported μ (p 0) d) (n : ℕ) (j : V) :
    (∑ a, if p n a = j then markDistribution μ p S d n a else 0) =
      tagDistribution μ p d n j := by
  rw [markDistribution_eq_cellLift hμ p S houtside d hd]
  exact cellLift_cellMass μ _ _
    (tagDistribution_supported (fun a => (hμ a).le) p d hd n) j

end GraphicalAllocation.Palm
