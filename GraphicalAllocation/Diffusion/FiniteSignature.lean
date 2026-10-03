import GraphicalAllocation.Diffusion.TagJoint
import GraphicalAllocation.Palm.FiniteModel
import GraphicalAllocation.Geometry.Hilbert

/-! # Allocation geometry on the exact finite mark space

All weights and partitions here are derived from the original uniform real
marks and the actual antitone allocation rule. No diffusion conclusion is
assumed, and null signatures have already been removed exactly.
-/

noncomputable section
namespace GraphicalAllocation.Diffusion
open scoped BigOperators
open MeasureTheory Rules Palm Projections Process

variable {E V I : Type*} [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype I] [DecidableEq I]

omit [DecidableEq E] [Fintype V] [DecidableEq V] [DecidableEq I] in
lemma finiteMark_selector (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) (i : I) :
    allocationSelector A.tail A.head A.probability (x i) (A.finiteMarkRepresentative x a) = a.val.2 i := by
  have h := congrArg (fun s : E × (I → V) => s.2 i) (A.finiteMarkRepresentative_spec x a)
  rw [allocationSelector_eq]
  exact h

omit [DecidableEq E] [Fintype V] [DecidableEq V] [DecidableEq I] in
lemma finiteMark_endpoint (A : AllocationRule V E) (x : I → Profile V)
    (a : A.FiniteMark x) (i : I) :
    a.val.2 i = A.tail a.val.1 ∨ a.val.2 i = A.head a.val.1 := by
  have h := allocationSelector_endpoint A.tail A.head A.probability (x i)
    (A.finiteMarkRepresentative x a)
  rw [finiteMark_selector, A.finiteMarkRepresentative_edge] at h
  exact h

omit [DecidableEq E] [Fintype V] [DecidableEq I] in
lemma finiteMark_unchanged_outside (A : AllocationRule V E) (x : I → Profile V)
    (i i' : I) (j : V) (S : Finset V) (hstep : x i' = raise (x i) j)
    (hS : ∀ e, A.tail e = j ∨ A.head e = j → A.tail e ∈ S ∧ A.head e ∈ S)
    (a : A.FiniteMark x) (ha : a.val.2 i' ∉ S) : a.val.2 i = a.val.2 i' := by
  rw [← finiteMark_selector A x a i, ← finiteMark_selector A x a i']
  rw [← finiteMark_selector A x a i', hstep] at ha
  rw [hstep]
  exact allocationSelector_unchanged_outside A.tail A.head A.distinct A.probability
    A.probability_antitone (x i) j S hS (A.finiteMarkRepresentative x a) ha

omit [DecidableEq E] in
/-- The localized mass is exactly the sum of the corresponding actual rates. -/
lemma finiteMark_selected_mass (A : AllocationRule V E) (x : I → Profile V)
    (i : I) (S : Finset V) :
    (∑ a : A.FiniteMark x,
      if a.val.2 i ∈ S then positiveAtomWeight (A.finiteMarkWeight x) a else 0) =
      (∑ v ∈ S, A.rate (x i) v) / Fintype.card E := by
  have heq : (∑ a : A.FiniteMark x,
      if a.val.2 i ∈ S then positiveAtomWeight (A.finiteMarkWeight x) a else 0) =
      ∑ v ∈ S, cellMass (positiveAtomWeight (A.finiteMarkWeight x))
        (fun a : A.FiniteMark x => a.val.2 i) v := by
    unfold cellMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [heq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  exact A.positiveFiniteSignature_kernel_weight x i v

omit [DecidableEq E] in
lemma finiteMark_selected_mass_le (A : AllocationRule V E) (x : I → Profile V)
    (i : I) (S : Finset V) (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ)
    (hS : S.card ≤ Δ + 1) :
    (∑ a : A.FiniteMark x,
      if a.val.2 i ∈ S then positiveAtomWeight (A.finiteMarkWeight x) a else 0) ≤
      (Δ : ℝ) * (Δ + 1) / Fintype.card E := by
  rw [finiteMark_selected_mass]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (∑ v ∈ S, A.rate (x i) v) ≤ ∑ v ∈ S, (Δ : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      exact (A.rate_le_degree (x i) v).trans (by exact_mod_cast hΔ v)
    _ = (S.card : ℝ) * Δ := by simp
    _ ≤ (Δ + 1 : ℝ) * Δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)
    _ = _ := by ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Midpoint observable of the actual edge retained by every signature. -/
def finiteMidpoint (A : AllocationRule V E) (x : I → Profile V) (F : V → H)
    (a : A.FiniteMark x) : H := Geometry.edgeMidpoint (F (A.tail a.val.1)) (F (A.head a.val.1))

omit [DecidableEq E] [Fintype V] [DecidableEq V] [DecidableEq I] in
lemma finiteMidpoint_cell_radius (A : AllocationRule V E) (x : I → Profile V)
    (F : V → H) (η : ℝ) (hedge : ∀ e, ‖F (A.tail e) - F (A.head e)‖ ≤ η)
    (a : A.FiniteMark x) (i : I) :
    ‖finiteMidpoint A x F a - F (a.val.2 i)‖ ≤ η / 2 := by
  rcases finiteMark_endpoint A x a i with h | h
  · rw [h, finiteMidpoint, Geometry.norm_edgeMidpoint_sub_left, norm_sub_rev]
    exact div_le_div_of_nonneg_right (hedge _) (by norm_num)
  · rw [h, finiteMidpoint, Geometry.norm_edgeMidpoint_sub_right]
    exact div_le_div_of_nonneg_right (hedge _) (by norm_num)

omit [DecidableEq E] in
/-- Event-time Hilbert estimate for every finite selected allocation path,
represented in any finite profile family. The path may stutter after its horizon. -/
theorem finiteSignature_hilbert_displacement_le (A : AllocationRule V E) (x : I → Profile V)
    (index : ℕ → I) (S : ℕ → Finset V)
    (hstep : ∀ k, x (index (k + 1)) = x (index k) ∨
      ∃ j, x (index (k + 1)) = raise (x (index k)) j ∧
        ∀ e, A.tail e = j ∨ A.head e = j → A.tail e ∈ S k ∧ A.head e ∈ S k)
    (Δ : ℕ) (hΔ : ∀ v, A.degree v ≤ Δ) (hS : ∀ k, (S k).card ≤ Δ + 1)
    (F : V → H) (η : ℝ) (hedge : ∀ e, ‖F (A.tail e) - F (A.head e)‖ ≤ η) (n : ℕ) :
    (∑ i, ∑ j, A.kernel.weight (x (index 0)) i *
      tagEvolution (positiveAtomWeight (A.finiteMarkWeight x))
        (fun k a => a.val.2 (index k)) n i j * ‖F j - F i‖ ^ 2) ≤
      2 * η ^ 2 * ((Δ : ℝ) * (Δ + 1) / Fintype.card E) * n + 2 * η ^ 2 := by
  have houtside : ∀ k (a : A.FiniteMark x), a.val.2 (index (k + 1)) ∉ S k →
      a.val.2 (index k) = a.val.2 (index (k + 1)) := by
    intro k a ha
    rcases hstep k with heq | ⟨j, heq, hj⟩
    · rw [← finiteMark_selector A x a (index k), ← finiteMark_selector A x a (index (k + 1)), heq]
    · exact finiteMark_unchanged_outside A x _ _ j (S k) heq hj a ha
  have h := local_tag_displacement_le (A.finiteEvent_weight_pos x) (A.finiteEvent_weight_sum x)
    (fun k (a : A.FiniteMark x) => a.val.2 (index k)) S houtside F
    (finiteMidpoint A x F) η ((Δ : ℝ) * (Δ + 1) / Fintype.card E)
    (fun k a => finiteMidpoint_cell_radius A x F η hedge a (index k))
    (fun k => finiteMark_selected_mass_le A x (index (k + 1)) (S k) Δ hΔ (hS k)) n
  simpa only [A.positiveFiniteSignature_kernel_weight] using h

end GraphicalAllocation.Diffusion
