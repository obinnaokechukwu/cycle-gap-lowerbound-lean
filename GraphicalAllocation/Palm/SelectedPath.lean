import GraphicalAllocation.Palm.Allocation
import GraphicalAllocation.Palm.ProjectionRepresentation
import GraphicalAllocation.Process.MarkedExperiment

/-! # Unconditional selected-base-path decomposition

The source is the actual independent finite-mark tagged kernel. The selected
vertex path is averaged with its genuine product probabilities. Conditional on
that path, the tag uses the proved cell-overlap kernels.
-/

noncomputable section
namespace GraphicalAllocation.Palm
open scoped BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

/-- The selection partition of an actual finite marked experiment. -/
def experimentSelector (F : FiniteMarks V A) (x : Profile V) (a : A) : V :=
  selected (F.event a).first (F.event a).second (F.event a).selector x

omit [DecidableEq A] [Fintype V] in
lemma experimentSelector_changes (F : FiniteMarks V A) (x : Profile V) (j : V) :
    ChangesOnlyFrom (experimentSelector F x) (experimentSelector F (raise x j)) j := by
  intro a ha
  exact selected_unchanged_of_other (F.event a).switchAway x j ha

omit [DecidableEq A] in
lemma cellMass_sum (μ : A → ℝ) (p : A → V) :
    ∑ j, cellMass μ p j = ∑ a, μ a := by
  unfold cellMass
  rw [Finset.sum_comm]
  simp

omit [Fintype V] [DecidableEq A] in
/-- Unnormalized one-step joint probability of a chosen base vertex and tag.
This also treats zero-probability base selections, without conditioning on them. -/
lemma selected_tag_joint_one_step (F : FiniteMarks V A) (x : Profile V) (i j k : V) :
    (∑ a, if experimentSelector F x a = j then
      F.weight a * (if (F.event a).tag x i = k then 1 else 0) else 0) =
      cellMass F.weight (experimentSelector F x) j *
        tagKernel F.weight (experimentSelector F x) (experimentSelector F (raise x j)) i k := by
  have hc := experimentSelector_changes F x j
  by_cases hij : i = j
  · subst i
    rw [weighted_tagKernel F.nonneg]
    unfold overlap
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : experimentSelector F x a = j
    · rw [ite_eq_left ha, event_tag_given_selection (F.event a) x j j ha]
      dsimp only [experimentSelector] at ha
      simp [experimentSelector, ha]
    · simp [ha]
  · rw [tagKernel_of_not_selected F.weight hc hij]
    unfold cellMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : experimentSelector F x a = j
    · rw [ite_eq_left ha, event_tag_given_selection (F.event a) x j i ha]
      simp [ha, hij]
    · simp [ha]

omit [DecidableEq A] in
/-- Group the genuine tagged update by its selected base vertex and new tag. -/
lemma tagged_step_by_selected (F : FiniteMarks V A) (f : Profile V × V → ℝ)
    (x : Profile V) (i : V) :
    F.tagged.step f (x, i) =
      ∑ j, cellMass F.weight (experimentSelector F x) j *
        ∑ k, tagKernel F.weight (experimentSelector F x)
          (experimentSelector F (raise x j)) i k * f (raise x j, k) := by
  simp only [Finset.mul_sum, ← mul_assoc]
  simp_rw [← selected_tag_joint_one_step F x i, Finset.sum_mul]
  conv_rhs =>
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold FiniteKernel.step
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  simp [FiniteMarks.tagged, Event.apply, update, experimentSelector, eq_comm]

/-- Final base profile of a selected vertex path. -/
def pathFinal (x : Profile V) : List V → Profile V
  | [] => x
  | j :: js => pathFinal (raise x j) js

/-- Conditional tag transition along an explicitly selected base path. -/
def pathTag (F : FiniteMarks V A) (x : Profile V) : List V → V → V → ℝ
  | [], i, k => if i = k then 1 else 0
  | j :: js, i, k => ∑ l, tagKernel F.weight (experimentSelector F x)
      (experimentSelector F (raise x j)) i l * pathTag F (raise x j) js l k

/-- Average over selected base paths of exactly n events. Every recursion
multiplies by the actual probability of the next selected base vertex. -/
def pathAverage (F : FiniteMarks V A) (x : Profile V) : ℕ → (List V → ℝ) → ℝ
  | 0, H => H []
  | n + 1, H => ∑ j, cellMass F.weight (experimentSelector F x) j *
      pathAverage F (raise x j) n (fun js => H (j :: js))

omit [DecidableEq A] in
lemma pathAverage_mul (F : FiniteMarks V A) (x : Profile V) (n : ℕ)
    (c : ℝ) (H : List V → ℝ) :
    pathAverage F x n (fun js => c * H js) = c * pathAverage F x n H := by
  induction n generalizing x H with
  | zero => rfl
  | succ n ih =>
    simp only [pathAverage, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [DecidableEq A] in
lemma pathAverage_sum {I : Type*} [Fintype I] (F : FiniteMarks V A)
    (x : Profile V) (n : ℕ) (H : I → List V → ℝ) :
    pathAverage F x n (fun js => ∑ i, H i js) = ∑ i, pathAverage F x n (H i) := by
  induction n generalizing x H with
  | zero => rfl
  | succ n ih =>
    simp only [pathAverage, ih, Finset.mul_sum]
    rw [Finset.sum_comm]

omit [DecidableEq A] in
lemma pathAverage_one (F : FiniteMarks V A) (x : Profile V) (n : ℕ) :
    pathAverage F x n (fun _ => 1) = 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [pathAverage, ih, cellMass_sum, F.total]

omit [DecidableEq A] in
lemma pathTag_test_cons (F : FiniteMarks V A) (x : Profile V) (j : V) (js : List V)
    (i : V) (f : Profile V × V → ℝ) :
    (∑ k, pathTag F x (j :: js) i k * f (pathFinal x (j :: js), k)) =
      ∑ l, tagKernel F.weight (experimentSelector F x) (experimentSelector F (raise x j)) i l *
        ∑ k, pathTag F (raise x j) js l k * f (pathFinal (raise x j) js, k) := by
  simp only [pathTag, pathFinal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq A] in
/-- Full unconditional selected-base-path decomposition of the actual tagged
experiment. This is the process-level conditional-law bridge in Proposition 3.1. -/
lemma tagged_iterate_eq_pathAverage (F : FiniteMarks V A) (n : ℕ)
    (f : Profile V × V → ℝ) (x : Profile V) (i : V) :
    F.tagged.iterate n f (x, i) = pathAverage F x n
      (fun js => ∑ k, pathTag F x js i k * f (pathFinal x js, k)) := by
  induction n generalizing x i with
  | zero => simp [FiniteKernel.iterate, pathAverage, pathTag, pathFinal]
  | succ n ih =>
    rw [FiniteKernel.iterate_succ, tagged_step_by_selected]
    simp_rw [ih]
    rw [pathAverage]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp_rw [pathTag_test_cons, pathAverage_sum, pathAverage_mul]
    simp_rw [pathAverage_sum]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open scoped BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

omit [DecidableEq A] in
lemma tagEvolution_succ_left (μ : A → ℝ) (p : ℕ → A → V) (n : ℕ) (i k : V) :
    tagEvolution μ p (n + 1) i k =
      ∑ l, tagKernel μ (p 0) (p 1) i l * tagEvolution μ (fun r => p (r + 1)) n l k := by
  induction n generalizing k with
  | zero => simp [tagEvolution]
  | succ n ih =>
    change (∑ r, tagEvolution μ p (n + 1) i r *
      tagKernel μ (p (n + 1)) (p (n + 1 + 1)) r k) =
      ∑ l, tagKernel μ (p 0) (p 1) i l *
        ∑ r, tagEvolution μ (fun t => p (t + 1)) n l r *
          tagKernel μ (p (n + 1)) (p (n + 1 + 1)) r k
    simp_rw [ih]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring

/-- Selection partitions along a vertex path, held constant after its end. -/
def pathPartitions (F : FiniteMarks V A) (x : Profile V) (js : List V)
    (n : ℕ) : A → V := experimentSelector F (pathFinal x (js.take n))

omit [DecidableEq A] [Fintype V] in
@[simp] lemma pathPartitions_zero (F : FiniteMarks V A) (x : Profile V) (js : List V) :
    pathPartitions F x js 0 = experimentSelector F x := rfl

omit [DecidableEq A] [Fintype V] in
@[simp] lemma pathPartitions_cons_succ (F : FiniteMarks V A) (x : Profile V)
    (j : V) (js : List V) (n : ℕ) :
    pathPartitions F x (j :: js) (n + 1) = pathPartitions F (raise x j) js n := by
  simp [pathPartitions, pathFinal]

omit [DecidableEq A] in
/-- The path-conditioned transition is exactly the chain used by the projection
representation, with no reversal or change of chronological order. -/
lemma pathTag_eq_tagEvolution (F : FiniteMarks V A) (x : Profile V)
    (js : List V) (i k : V) :
    pathTag F x js i k = tagEvolution F.weight (pathPartitions F x js) js.length i k := by
  induction js generalizing x i k with
  | nil => simp [pathTag, tagEvolution]
  | cons j js ih =>
    simp only [List.length_cons, tagEvolution_succ_left, pathTag,
      pathPartitions_zero, pathPartitions_cons_succ]
    apply Finset.sum_congr rfl
    intro l _
    rw [ih]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open scoped BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

omit [DecidableEq A] in
lemma pathAverage_nonneg (F : FiniteMarks V A) (x : Profile V) (n : ℕ)
    (H : List V → ℝ) (hH : ∀ js, 0 ≤ H js) : 0 ≤ pathAverage F x n H := by
  induction n generalizing x H with
  | zero => exact hH []
  | succ n ih =>
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (cellMass_nonneg F.nonneg _ _) (ih _ _ (fun js => hH (j :: js)))

omit [DecidableEq A] in
lemma pathAverage_mono (F : FiniteMarks V A) (x : Profile V) (n : ℕ)
    (H K : List V → ℝ) (h : ∀ js, H js ≤ K js) :
    pathAverage F x n H ≤ pathAverage F x n K := by
  induction n generalizing x H K with
  | zero => exact h []
  | succ n ih =>
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (ih _ _ _ (fun js => h (j :: js)))
      (cellMass_nonneg F.nonneg _ _)

omit [DecidableEq A] in
/-- The rate-biased Palm intertwining for one true tagged transition. -/
lemma palm_tagged_step (F : FiniteMarks V A) (f : Profile V × V → ℝ) (x : Profile V) :
    (∑ i, cellMass F.weight (experimentSelector F x) i * F.tagged.step f (x, i)) =
      F.base.step (fun y => ∑ k, cellMass F.weight (experimentSelector F y) k * f (y, k)) x := by
  simp_rw [tagged_step_by_selected, Finset.mul_sum]
  rw [FiniteMarks.base_step_eq_selectionMass, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, ∑ k,
    cellMass F.weight (experimentSelector F x) i *
      (cellMass F.weight (experimentSelector F x) j *
        (tagKernel F.weight (experimentSelector F x) (experimentSelector F (raise x j)) i k *
          f (raise x j, k)))) = _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = cellMass F.weight (experimentSelector F x) j *
      (∑ i, cellMass F.weight (experimentSelector F x) i *
        tagKernel F.weight (experimentSelector F x) (experimentSelector F (raise x j)) i k) *
          f (raise x j, k) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [palm_one_step F.nonneg]
      exact mul_assoc _ _ _

omit [DecidableEq A] in
/-- Equation (3.4) after an arbitrary deterministic number of events, for the
actual finite independent-mark process and every real test function. -/
lemma palm_tagged_iterate (F : FiniteMarks V A) (n : ℕ)
    (f : Profile V × V → ℝ) (x : Profile V) :
    (∑ i, cellMass F.weight (experimentSelector F x) i * F.tagged.iterate n f (x, i)) =
      F.base.iterate n (fun y => ∑ k, cellMass F.weight (experimentSelector F y) k * f (y, k)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteKernel.iterate_succ]
    rw [palm_tagged_step]
    unfold FiniteKernel.step
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [ih]

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open scoped BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

omit [DecidableEq A] in
lemma pathAverage_mono_of_length (F : FiniteMarks V A) (x : Profile V) (n : ℕ)
    (H K : List V → ℝ) (h : ∀ js, js.length = n → H js ≤ K js) :
    pathAverage F x n H ≤ pathAverage F x n K := by
  induction n generalizing x H K with
  | zero => exact h [] rfl
  | succ n ih =>
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (cellMass_nonneg F.nonneg _ _)
    apply ih
    intro js hj
    exact h (j :: js) (by simpa using congrArg Nat.succ hj)

omit [DecidableEq A] in
lemma pathAverage_const (F : FiniteMarks V A) (x : Profile V) (n : ℕ) (c : ℝ) :
    pathAverage F x n (fun _ => c) = c := by
  have h := pathAverage_mul F x n c (fun _ => 1)
  simpa [pathAverage_one] using h

omit [DecidableEq A] in
lemma pathAverage_final (F : FiniteMarks V A) (x : Profile V) (n : ℕ)
    (g : Profile V → ℝ) :
    pathAverage F x n (fun js => g (pathFinal x js)) = F.base.iterate n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [pathAverage, pathFinal, ih, FiniteKernel.iterate_succ,
      FiniteMarks.base_step_eq_selectionMass]
    rfl

end GraphicalAllocation.Palm

namespace GraphicalAllocation.Palm
open GraphicalAllocation.Rules GraphicalAllocation.Process
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma pathFinal_append (x : Profile V) (xs ys : List V) :
    pathFinal x (xs ++ ys) = pathFinal (pathFinal x xs) ys := by
  induction xs generalizing x with
  | nil => rfl
  | cons j js ih => exact ih (raise x j)

omit [Fintype V] in
lemma pathFinal_take_succ (x : Profile V) (js : List V) (n : ℕ) (hn : n < js.length) :
    pathFinal x (js.take (n + 1)) = raise (pathFinal x (js.take n)) js[n] := by
  rw [List.take_succ_eq_append_getElem hn, pathFinal_append]
  rfl

omit [DecidableEq A] [Fintype V] in
lemma pathPartitions_step (F : FiniteMarks V A) (x : Profile V) (js : List V)
    (n : ℕ) (hn : n < js.length) :
    pathPartitions F x js (n + 1) =
      experimentSelector F (raise (pathFinal x (js.take n)) js[n]) := by
  rw [pathPartitions, pathFinal_take_succ x js n hn]

omit [DecidableEq A] [Fintype V] in
lemma pathPartitions_stutter (F : FiniteMarks V A) (x : Profile V) (js : List V)
    (n : ℕ) (hn : js.length ≤ n) :
    pathPartitions F x js (n + 1) = pathPartitions F x js n := by
  simp [pathPartitions, List.take_of_length_le hn,
    List.take_of_length_le (hn.trans (Nat.le_succ n))]

end GraphicalAllocation.Palm
