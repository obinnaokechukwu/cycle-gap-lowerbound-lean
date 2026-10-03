import GraphicalAllocation.Palm.Infinite.AllocationPath
import Mathlib.Probability.ProductMeasure

/-! # Causal observations of the original independent marks

The original allocation process is realized on one infinite product of its
literal marked-edge law. Prescribing its selected vertices is exactly a
rectangle of selection cells evaluated at the corresponding deterministic
profiles. No transition law of the conditioned process is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal ProbabilityTheory BigOperators
open GraphicalAllocation.Rules GraphicalAllocation.Process

namespace GraphicalAllocation.Palm.Infinite

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The original independent uniform-edge/uniform-mark experiment. -/
def independentMarkLaw : Measure (ℕ → E × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => (markedMeasure (E := E)))

instance : IsProbabilityMeasure (independentMarkLaw (E := E)) := by
  unfold independentMarkLaw
  infer_instance

/-- The genuine causal base recursion, driven by independent event marks. -/
def originalProfile (A : AllocationRule V E) (x : Profile V) (ω : ℕ → E × ℝ) :
    ℕ → Profile V
  | 0 => x
  | n + 1 => (A.event (ω n).1 (ω n).2).apply (originalProfile A x ω n)

/-- The vertices actually selected by the independent-mark process. -/
def originalSelection (A : AllocationRule V E) (x : Profile V) (ω : ℕ → E × ℝ)
    (n : ℕ) : V :=
  allocationSelector A.tail A.head A.probability (originalProfile A x ω n) (ω n)

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma originalProfile_succ (A : AllocationRule V E) (x : Profile V)
    (ω : ℕ → E × ℝ) (n : ℕ) :
    originalProfile A x ω (n + 1) = raise (originalProfile A x ω n)
      (originalSelection A x ω n) := rfl

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma originalProfile_eq_selectedProfile (A : AllocationRule V E) (x : Profile V)
    (ω : ℕ → E × ℝ) :
    originalProfile A x ω = selectedProfile x (originalSelection A x ω) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => rw [originalProfile_succ, selectedProfile, ih]

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma originalProfile_eq_of_prefix (A : AllocationRule V E) (x : Profile V)
    (ω : ℕ → E × ℝ) (j : ℕ → V) (n : ℕ)
    (h : ∀ r, r < n → originalSelection A x ω r = j r) :
    originalProfile A x ω n = selectedProfile x j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [originalProfile_succ, selectedProfile, h n (by omega), ih]
    exact fun r hr => h r (by omega)

/-- An observed base prefix in the original, independently driven process. -/
def originalBaseCylinder (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) : Set (ℕ → E × ℝ) :=
  {ω | ∀ r, r < n → originalSelection A x ω r = j r}

/-- The cell rectangle forced by a prescribed base prefix. -/
def selectedCellRectangle (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) : Set (ℕ → E × ℝ) :=
  Set.pi (Finset.range n) (fun r =>
    {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r})

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Conditioning on actual selected vertices imposes precisely these cell
conditions on the independent marks, including every intermediate update. -/
theorem originalBaseCylinder_eq_rectangle (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    originalBaseCylinder A x j n = selectedCellRectangle A x j n := by
  ext ω
  change (∀ r, r < n → originalSelection A x ω r = j r) ↔
    ∀ r ∈ Finset.range n,
      allocationSelector A.tail A.head A.probability (selectedProfile x j r) (ω r) = j r
  simp only [Finset.mem_range]
  constructor
  · intro h r hr
    rw [← originalProfile_eq_of_prefix A x ω j r (fun s hs => h s (by omega))]
    exact h r hr
  · intro h r hr
    have hp : ∀ k, k ≤ n → originalProfile A x ω k = selectedProfile x j k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [originalProfile_succ, selectedProfile, ih (by omega)]
        congr 1
        unfold originalSelection
        rw [ih (by omega)]
        exact h k (by omega)
    unfold originalSelection
    rw [hp r (by omega)]
    exact h r hr

omit [Fintype V] [Nonempty E] [DecidableEq E] in
lemma originalBaseCylinder_measurable (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) : MeasurableSet (originalBaseCylinder A x j n) := by
  rw [originalBaseCylinder_eq_rectangle]
  exact MeasurableSet.pi (Finset.countable_toSet _)
    (fun r _ => allocationSelector_measurable A _ (measurableSet_singleton _))

omit [Fintype V] [DecidableEq E] in
/-- Every finite base-history probability is the actual product of its
successive original selection probabilities. -/
theorem independentMarkLaw_baseCylinder (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    independentMarkLaw (originalBaseCylinder A x j n) =
      ∏ r ∈ Finset.range n, (markedMeasure (E := E))
        {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r} := by
  rw [originalBaseCylinder_eq_rectangle]
  exact Measure.infinitePi_pi _ (fun r _ =>
    allocationSelector_measurable A _ (measurableSet_singleton _))

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Literal independence of every finite family of original event marks. -/
lemma independentMarkLaw_map_restrict (s : Finset ℕ) :
    (independentMarkLaw (E := E)).map s.restrict =
      Measure.pi (fun _ : s => (markedMeasure (E := E))) :=
  Measure.infinitePi_map_restrict _

omit [Fintype V] [DecidableEq E] in
/-- Feasibility of a finite selected history is exactly positivity of each
successive selection cell, rather than an additional probabilistic assumption. -/
lemma originalBaseCylinder_ne_zero_iff (A : AllocationRule V E) (x : Profile V)
    (j : ℕ → V) (n : ℕ) :
    independentMarkLaw (originalBaseCylinder A x j n) ≠ 0 ↔
      ∀ r, r < n → (markedMeasure (E := E))
        {a | allocationSelector A.tail A.head A.probability (selectedProfile x j r) a = j r} ≠ 0 := by
  rw [independentMarkLaw_baseCylinder]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_range]

end GraphicalAllocation.Palm.Infinite
