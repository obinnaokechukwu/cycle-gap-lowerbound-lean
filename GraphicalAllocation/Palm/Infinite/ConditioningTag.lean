import GraphicalAllocation.Palm.Infinite.ConditioningOriginal
import GraphicalAllocation.Palm.Infinite.DrivenTagLaw

/-! # Causal original tags and observation-dependent tag maps

The actual synchronous discrepancy is driven by the original random base
profile. When its observed selection path is supplied to the conditional
recursion, the two deterministic tag processes agree at every coordinate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open GraphicalAllocation.Rules GraphicalAllocation.Process
namespace GraphicalAllocation.Palm.Infinite
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype E] [Nonempty E] [DecidableEq E]
  [MeasurableSpace E] [MeasurableSingletonClass E]

lemma selectedProfile_measurable (x : Profile V) (n : ℕ) :
    Measurable (fun j : ℕ → V => selectedProfile x j n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun z : Profile V × V => raise z.1 z.2)).comp
      (ih.prodMk (measurable_pi_apply n))

omit [DecidableEq E] [Nonempty E] in
lemma originalEventTag_joint_measurable (A : AllocationRule V E) :
    Measurable (fun s : (Profile V × V) × (E × ℝ) =>
      (A.event s.2.1 s.2.2).tag s.1.1 s.1.2) :=
  measurable_from_prod_countable_right (fun s => original_event_tag_measurable A s.1 s.2)

/-- The actual causal synchronous discrepancy on an initial tag and the original
independent marked path, using the random original base profile at every step. -/
def originalTagProcess (A : AllocationRule V E) (x : Profile V)
    (s : V × (ℕ → E × ℝ)) : ℕ → V
  | 0 => s.1
  | n + 1 => (A.event (s.2 n).1 (s.2 n).2).tag
      (originalProfile A x s.2 n) (originalTagProcess A x s n)

omit [Nonempty E] [DecidableEq E] in
lemma originalTagProcess_measurable (A : AllocationRule V E) (x : Profile V) :
    Measurable (originalTagProcess A x) := by
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact (originalEventTag_joint_measurable A).comp
      ((((originalProfile_measurable A x n).comp measurable_snd).prodMk ih).prodMk
        ((measurable_pi_apply n).comp measurable_snd))

omit [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype E] [Nonempty E]
  [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The supplied observed path exactly reconstructs the random original base
profile, so the conditional and causal discrepancy recursions agree pointwise. -/
theorem conditionalOriginalTagProcess_observed (A : AllocationRule V E) (x : Profile V)
    (s : V × (ℕ → E × ℝ)) :
    conditionalOriginalTagProcess A x (originalSelection A x s.2) s =
      originalTagProcess A x s := by
  funext n
  change drivenTagProcess _ s n = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [drivenTagProcess, originalTagProcess, ih, originalProfile_eq_selectedProfile]

omit [DecidableEq E] [Nonempty E] in
/-- Joint measurability permits conditional pushforward to depend on the full
observed base path as well as the initial tag and original hidden marks. -/
lemma conditionalOriginalTagProcess_joint_measurable (A : AllocationRule V E)
    (x : Profile V) : Measurable (fun q : (ℕ → V) × (V × (ℕ → E × ℝ)) =>
      conditionalOriginalTagProcess A x q.1 q.2) := by
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_fst.comp measurable_snd
  | succ n ih =>
    exact (originalEventTag_joint_measurable A).comp
      ((((selectedProfile_measurable x n).comp measurable_fst).prodMk ih).prodMk
        ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)))

end GraphicalAllocation.Palm.Infinite
