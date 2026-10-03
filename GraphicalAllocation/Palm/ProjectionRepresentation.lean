import GraphicalAllocation.Palm.Representation
import GraphicalAllocation.Projections.Chain

/-! # Joint tag/mark endpoint laws

This joins the conditional mark representation to the exact forward-product
joint law used by the projection displacement estimate.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators Matrix
open GraphicalAllocation.Projections

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

omit [DecidableEq A] in
lemma tagDistribution_eq_tagEvolution (μ : A → ℝ) (p : ℕ → A → V)
    (d : V → ℝ) (n : ℕ) (j : V) :
    tagDistribution μ p d n j = ∑ i, d i * tagEvolution μ p n i j := by
  induction n generalizing j with
  | zero => simp [tagDistribution, tagEvolution]
  | succ n ih =>
    simp only [tagDistribution, tagPush, ih, tagEvolution, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

omit [Fintype V] in
lemma markDistribution_eq_forwardProduct (μ : A → ℝ) (p : ℕ → A → V)
    (S : ℕ → Finset V) (d : V → ℝ) (n : ℕ) (b : A) :
    markDistribution μ p S d n b =
      ∑ a, cellLift μ (p 0) d a *
        forwardProduct (fun k => cellKernel μ (localKey (p (k + 1)) (S k))) n a b := by
  induction n generalizing b with
  | zero => simp [markDistribution, forwardProduct, Matrix.one_apply]
  | succ n ih =>
    simp only [markDistribution, ih, forwardProduct, 
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    change _ = cellLift μ (p 0) d a * ∑ c,
      forwardProduct (fun k => cellKernel μ (localKey (p (k + 1)) (S k))) n a c *
        cellKernel μ (localKey (p (n + 1)) (S n)) c b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring

def initialTagMass (μ : A → ℝ) (p : A → V) (i j : V) : ℝ :=
  if i = j then cellMass μ p i else 0

omit [DecidableEq A] [Fintype V] in
lemma initialTagMass_supported (μ : A → ℝ) (p : A → V) (i : V) :
    CellSupported μ p (initialTagMass μ p i) := by
  intro j hj
  by_cases h : i = j <;> simp [initialTagMass, h, hj]

omit [Fintype V] [DecidableEq A] in
lemma cellLift_initialTagMass {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : A → V) (i : V) (a : A) :
    cellLift μ p (initialTagMass μ p i) a = if p a = i then μ a else 0 := by
  by_cases h : p a = i
  · have hm : cellMass μ p i ≠ 0 := by simpa [h] using ne_of_gt (cellMass_pos hμ p a)
    simp [cellLift, initialTagMass, h, hm]
  · simp [cellLift, initialTagMass, h, Ne.symm h]

omit [DecidableEq A] in
lemma tagDistribution_initialTagMass (μ : A → ℝ) (p : ℕ → A → V)
    (n : ℕ) (i j : V) :
    tagDistribution μ p (initialTagMass μ (p 0) i) n j =
      cellMass μ (p 0) i * tagEvolution μ p n i j := by
  rw [tagDistribution_eq_tagEvolution]
  simp [initialTagMass, ite_mul]

/-- Exact equality of the joint endpoint tag law and the projection-chain
endpoint law read through the initial and final selection partitions. -/
lemma tag_mark_endpoint_joint {μ : A → ℝ} (hμ : ∀ a, 0 < μ a)
    (p : ℕ → A → V) (S : ℕ → Finset V)
    (houtside : ∀ n a, p (n + 1) a ∉ S n → p n a = p (n + 1) a)
    (n : ℕ) (i j : V) :
    (∑ a, ∑ b, if p 0 a = i ∧ p n b = j then
      endpointJoint μ (fun k => cellKernel μ (localKey (p (k + 1)) (S k))) n a b else 0) =
      cellMass μ (p 0) i * tagEvolution μ p n i j := by
  have h := markDistribution_reads_tag hμ p S houtside
    (initialTagMass μ (p 0) i) (initialTagMass_supported μ (p 0) i) n j
  rw [tagDistribution_initialTagMass] at h
  rw [← h]
  simp_rw [markDistribution_eq_forwardProduct, cellLift_initialTagMass hμ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : p n b = j
  · simp only [hb, ite_true]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : p 0 a = i <;> simp [ha, endpointJoint]
  · simp [hb]

end GraphicalAllocation.Palm
